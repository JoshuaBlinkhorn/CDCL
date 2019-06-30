// CDCL.c
// Joshua Blinkhorn 29.04.2019
// This file is part of CDCL

// CURRENT UPGRADE: 1. literals as assignment pointers 2. pure literal elimination

// This upgrade will implement the trail as a ring buffer, and
// the decision heuristic as a linked list structure that holds
// the buffer. Reordering the links in the list allows to schedule
// locally relevent variables at the head of the buffer.
// Decision terminates when the ring buffer empties

#include "CDCL.h"
#include <stdlib.h>
#include <stdio.h>
#include <math.h>
#include <limits.h>
#include <time.h>
#include <assert.h>
#include "getRSS.c"


// enable debugging
#ifdef VERBOSE
#define VERBOSE_(x) (x)
#else
#define VERBOSE_(x) 
#endif

#ifdef ASSERT
#define ASSERT_(x) (x)
#else
#define ASSERT_(x) 
#endif

#ifdef TIDY
#define TIDY_(x) (x)
#else
#define TIDY_(x) 
#endif


// MACROS

// truth values / phases
#define POSITIVE 1
#define NEGATIVE 0

// group ids
#define POOL ULONG_MAX
#define MODEL ULONG_MAX - 1

// maximum number of variables handled at present
#define MAX_VARS (ULONG_MAX / 2)

// native type aliases
typedef signed char truth_value_t;
typedef signed char phase_t;
typedef signed long int DIMACS_lit_t;
typedef unsigned long int cnf_size_t;
typedef unsigned long int varset_size_t; 
typedef unsigned long int list_size_t;
typedef unsigned long int group_id_t;

// MAIN STRUCTURE OF DATA 

struct group {
  group_id_t id;
  struct group* next;
  struct ass {
    struct group* head;
    struct ass* prev;
    struct ass* next;
    struct var {
      struct ass* trail_pos;
      cnf_size_t num_pos, num_neg;
      struct list {
	list_size_t size;
	list_size_t used;
	list_size_t at;
	struct clause {
	  varset_size_t width;
	  struct lit {
	    struct var* var;
	    phase_t phase;	    
	  } *lits;
	} **clauses;    
      } pos_all, neg_all, pos_watched, neg_watched;
    } *var;
    phase_t phase;
  } *first, *last;
};

typedef struct group group_t;
typedef struct ass ass_t;
typedef struct var var_t;
typedef struct list list_t;
typedef struct clause clause_t;
typedef struct lit lit_t;

// assignments are the main objects, which are treated implicitly in one-to-one 
// correspondence with literals. A clause is a fixed size list of pointers to
// assignments. Each assignment watches a mutable subset of the clauses in which
// its negation appears.

typedef struct trail {
  group_t* pool;
  group_t* model;
  group_t* root;
  group_t* current;
  group_t* conflict;
} trail_t;

// the trail stores a fixed-sized array of pointers to assignments, storing the
// current assignment and the order in which it was made

typedef struct cnf {
  clause_t* clauses;
  cnf_size_t size;
} cnf_t;

// a cnf stores a fixed-sized array of clauses 

// GLOBAL DECLARATIONS

// the solver
varset_size_t num_vars;
cnf_t cnf;
var_t* varset;
trail_t trail;

// stats
clock_t start_time;
unsigned long num_conflicts = 0;
unsigned long num_decisions = 0;
unsigned long num_unit_props = 0;
unsigned long num_pure_props = 0;
unsigned long num_redefinitions = 0;

// HELPER FUNCTIONS

void error(char* message);

// literal-related

var_t* DIMACS_to_var(DIMACS_lit_t DIMACS_lit);
phase_t DIMACS_to_phase(DIMACS_lit_t DIMACS_lit);
DIMACS_lit_t lit_to_DIMACS(lit_t* lit);
DIMACS_lit_t ass_to_DIMACS(ass_t* lit);

// clause-related
clause_t clause_init(varset_size_t width);
void clause_free(clause_t* clause);

// list related
// this is an automatically resized array of pointers to clauses.
// the array becomes twice as large whenever necessary to add an item
void list_init(list_t* list);
void list_free(list_t* list);
void list_push(list_t* list, clause_t* datum);
void list_print_clauses(list_t* list); // write when needed

// group related
group_t* group_init(group_id_t id);
void group_free(group_t* group);
void pool_add_ass(ass_t* ass);
int queue(group_t* group, var_t* var, phase_t phase);

// assignment related
//void assign(ass_t* lit);
//void unassign(ass_t* lit);

// trail related
//void trail_queue_lit(ass_t* lit, model_size_t dec_level);
//void trail_shuffle();

// miscellaneous
void report_SAT();
void report_UNSAT();

// printing and debugging
void print_lit(lit_t* lit);
void print_clause(clause_t* clause);
void print_cnf();
void print_ass(ass_t* ass);
void print_list(list_t *list);
void print_group(group_t* group);
void print_trail();
void print_stats();

// asserts
void assert_literal_validity(DIMACS_lit_t DIMACS_lit);

// to categorise
void immortalise(ass_t* ass);

// CDCL INTERFACE IMPLEMENTATION

void CDCL_init(char* DIMACS_filename)
{
  
  // initialises global solver according to the DIMACS file 'input'.
  // all data structures are initialised and all initial memory allocated
  // unit clauses found while reading the input are placed on the trail.

  FILE* input, *cursor;
  char buffer[5]; // used only to read the `cnf' string from the input file
  char ch; // used to read single characters from the input file  
  DIMACS_lit_t DIMACS_lit; // temporary literal for reading
  varset_size_t width, which_lit, which_var; 
  cnf_size_t which_clause;
  clause_t* clause;
  lit_t* lit;
  ass_t* ass;
  var_t* var;

  start_time = clock();
  VERBOSE_(fprintf(stderr, "In CDCL_init()..\n"));

  // open file connections
  // TODO: currently using two file connections to find size of clauses before writing
  // them; it is probably possible to use just one, and to traverse the stream 
  // backwards when needed
  if ((input = (FILE *)fopen(DIMACS_filename, "r")) == NULL) error("cannot open file");
  if ((cursor = (FILE *)fopen(DIMACS_filename, "r")) == NULL) error("cannot open file");

  // PARSE HEADER
  // disregard comment lines
  while ((ch = fgetc(input)) == 'c')
    while ((ch = fgetc(input)) != '\n')
      continue;
  while ((ch = fgetc(cursor)) == 'c')
    while ((ch = fgetc(cursor)) != '\n')
      continue;
  // read header line
  if (ch != 'p') error("bad input - 'p' not found");
  if ((fscanf(input, "%s", buffer)) != 1) error("bad input - 'cnf' not found");
  fscanf(cursor, "%s", buffer);

  // read number of variables
  if ((fscanf(input, "%lu", &(num_vars))) != 1)
    error("bad input - number of vars missing");
  fscanf(cursor, "%lu", &(num_vars));

  if (num_vars > MAX_VARS) // i.e. more variables than our data type can handle
    error("too many vars - maximum MAX_VARS");

  // INITIALISE SOLVER STRUCTURES
  // varset
  if ((varset = (var_t*)malloc(sizeof(var_t) * num_vars)) == NULL)
	error("cannot allocate varset");
  // lists
  

  // initialise pool group and default assignments
  // initially the pool contains all variables
  trail.pool = group_init(POOL);

  // initialise default assignments TODO: there is a better way to do this
  for (which_var = 0; which_var < num_vars; which_var++)
    {
      if ((ass = (ass_t*)malloc(sizeof(ass_t))) == NULL)
	error("cannot allocate assignment");      
      ass->var = varset + which_var;
      ass->phase = POSITIVE;
      pool_add_ass(ass);
      varset[which_var].trail_pos = ass;
      // initialise lists
      list_init(&(varset[which_var].pos_watched));
      list_init(&(varset[which_var].neg_watched));
      list_init(&(varset[which_var].pos_all));
      list_init(&(varset[which_var].neg_all));
    }

  // initialise model group
  trail.model = group_init(MODEL);
  trail.root = trail.model;

  // READ CNF
  // read number of clauses
  if(fscanf(input, "%lu", &cnf.size) != 1)
    error("bad input - number of clauses not found");
  fscanf(cursor, "%lu", &cnf.size);

  // deal with trivial formulas
  if (cnf.size == 0)
    {
      report_SAT();
      exit(0);
    }
  if (num_vars == 0)
    {
      report_UNSAT();
      exit(0);
    }

  // initialise cnf
  if ((cnf.clauses = (clause_t*)malloc(sizeof(clause_t) * cnf.size)) == NULL)
	error("cannot allocate cnf clauses");

  // allocate clauses and add to formula
  for(which_clause = 0; which_clause < cnf.size; which_clause++)
    {
      // find width of clause with cursor
      fscanf(cursor, "%ld", &DIMACS_lit);
      for(width = 0; DIMACS_lit != 0; width++) 
	{
	  // TODO: enclose in check macro
	  ASSERT_(assert_literal_validity(DIMACS_lit));
	  fscanf(cursor, "%ld", &DIMACS_lit);
	}

      // if the width is 0, formula is UNSAT
      if (width == 0)
	{
	  report_UNSAT();
	  exit(0);
	}

      // if the width is 1, add the assignment as an implied unit propagation
      if (width == 1)
	{
	  fscanf(input, "%ld", &DIMACS_lit);
	  if (queue(trail.model, DIMACS_to_var(DIMACS_lit), DIMACS_to_phase(DIMACS_lit)))
	    num_unit_props++;
	  fscanf(input, "%ld", &DIMACS_lit);
	  // we do not store unit clauses, so decrement counters
	  // TODO: cnf.size is probably inessential
	  // TODO: better error handling for CDCL_init();
	  cnf.size--;
	  which_clause--;
	}
      else 
	{
	  // initialise clause
	  cnf.clauses[which_clause] = clause_init(width);
	  clause = cnf.clauses + which_clause;
	  // set literals 
	  fscanf(input, "%ld", &DIMACS_lit);
	  for(which_lit = 0; which_lit < width; which_lit++) 
	    {	      
	      clause->lits[which_lit].var = (var = DIMACS_to_var(DIMACS_lit));
	      if ((clause->lits[which_lit].phase = DIMACS_to_phase(DIMACS_lit)) == POSITIVE)
		list_push(&(var->pos_all), clause);
	      else list_push(&(var->neg_all), clause);
	      fscanf(input, "%ld", &DIMACS_lit);
	    }
       	  // watch the first two literals
	  if ((lit = clause->lits)->phase == POSITIVE)
	    list_push(&((lit->var)->pos_watched),clause);
	  else list_push(&((lit->var)->neg_watched), clause);
	  if ((lit = clause->lits + 1)->phase == POSITIVE)
	    list_push(&((lit->var)->pos_watched),clause);
	  else list_push(&((lit->var)->neg_watched), clause);
	}
    }

  // IDENTIFY PURE LITERALS
  // cycle through variables
  for (which_var = 0; which_var < num_vars; which_var++)
    {
      var = varset + which_var;
      // if positive literal is pure, queue it, if not queed already
      // n.b. the literal may be `pure (as in num_pos == 0)' even when its negation
      // was unit, since that unit clause was not added to the CNF
      if ((var->num_pos = var->pos_all.used) == 0 && var->trail_pos->head != trail.model)
	  if (queue(trail.model, varset + which_var, NEGATIVE)) num_pure_props++;
      // do same for negative literal
      if ((var->num_neg = var->neg_all.used) == 0 && var->trail_pos->head != trail.model)	 
	  if (queue(trail.model, varset + which_var, POSITIVE)) num_pure_props++; 
    }
  
  // PREPROCESS
  ass = trail.model->first;
  while(ass != NULL)
    {
      immortalise(ass);
      ass = ass->next;
    }
  if (trail.pool->first == NULL)
    report_SAT();
}

void immortalise(ass_t* ass)
{
  // 1. Deletes all clauses satisfied by the current assignment,
  // and queues any resulting pure propagations.
  // 2. Swaps for each watched clause are attempted,
  // queueing any resulting unit propagations.

  VERBOSE_(fprintf(stderr, "In immortalise()..\n"));
  
  list_t* all, * watched;
  clause_t** clauses;
  clause_t* clause;
  lit_t* lit;
  var_t* var, * unit_var;
  cnf_size_t which_clause, num_clauses;
  varset_size_t which_lit, num_lits;
  lit_t temp_lit;

  // get the appropriate lists
  var = ass->var;
  if (ass->phase == POSITIVE) 
    {
      all = &(var->pos_all);
      watched = &(var->neg_watched);
    }
  else
    {
      all = &(var->neg_all);
      watched = &(var->pos_watched);
    }

  // 1. Delete the clauses satisfied by the assignment 

  // cycle through clauses
  clauses = all->clauses;
  num_clauses = all->used;
  for (which_clause = 0; which_clause < num_clauses; which_clause++)
    {
      // ignore dead clauses
      if ((clause = clauses[which_clause])->width != 0)
	{
	  // cycle through each literal in clause
	  num_lits = clause->width;
	  for (which_lit = 0; which_lit < num_lits; which_lit++)
	    {
	      // ignore a literal if an assignment to it is already queued
	      // TODO: can a pure propagation induce a `phony' conflict?
	      // if not, we can just queue the assignment ..
	      if ((var = (lit = clause->lits + which_lit)->var)->trail_pos->head != 
		  trail.model)
		{	    
		  // decrement literal counter; if it hits 0, the literal is pure -
		  // so complementary assignment is queued
		  if (lit->phase == POSITIVE && --(var = lit->var)->num_pos == 0)
		    {
		      num_pure_props++;
		      queue(trail.model, var, NEGATIVE);
		    }
		  else if (--(var = lit->var)->num_neg == 0)
		    {
		      num_pure_props++;
		      queue(trail.model, var, POSITIVE);
		    }
		}
	    }
	  // kill the clause; 0 width indicates a dead clause
	  // (unit and empty clauses are never stored)
	  clause->width = 0;
	}
    }
  // free the memory for the list
  free(all->clauses);
  TIDY_(all->clauses = NULL);
  TIDY_(all->size = (all->used = (all->at = 0)));
  
  // 2. visit the watched clauses for the assignment, and swap watches
  
  // cycle through clauses
  clauses = watched->clauses;
  num_clauses = watched->used;
  for (which_clause = 0; which_clause < num_clauses; which_clause++)
    {
      // clauses of size 2 become unit
      if ((num_lits = (clause = clauses[which_clause])->width) == 2)
	{
	  // queue unit assignment
	  if ((unit_var = (lit = clause->lits)->var) == var)
	      unit_var = (lit = clause->lits + 1)->var;
	  if (queue(trail.model, unit_var, lit->phase)) num_unit_props++;
	  // delete clause
	  clause->width = 0;
	}

      // ignore dead clauses
      else if (num_lits > 2)
	{
	  // swap watched literal with last literal and decrement clause width
	  if ((lit = clause->lits)->var != var)
	    lit = clause->lits + 1;
	  temp_lit = *lit;
	  *lit = clause->lits[num_lits - 1];
	  clause->lits[num_lits - 1] = temp_lit;		  
	  clause->width--;
	}
    }
  // free the memory for the list
  free(watched->clauses);
  TIDY_(watched->clauses = NULL);
  TIDY_(watched->size = (watched->used = (watched->at = 0)));
}

void CDCL_print()
{
  //varset_size_t which_var;

  print_cnf();
  /*
  for (which_var = 0; which_var < num_vars; which_var++)
    {
      fprintf(stderr, "Variable %lu:\n", which_var + 1);
      fprintf(stderr, "positive watched:\n");
      print_list(&varset[which_var].pos_watched);
      fprintf(stderr, "negative watched:\n");
      print_list(&varset[which_var].neg_watched);
      fprintf(stderr, "positive all:\n");
      print_list(&varset[which_var].pos_all);
      fprintf(stderr, "negative all:\n");
      print_list(&varset[which_var].neg_all);
      fprintf(stderr, "\n");
    }
  */
  print_trail();
  print_stats();
}

/*

void CDCL_free()
{
  // this function probably never needs to be called
  // the OS can clean up when the program returns

  cnf_size_t which_clause;
  model_size_t which_ass;

  // free memory for the cnf
  for (which_clause = 0; which_clause < cnf.size; which_clause++)
    clause_free(cnf.clauses + which_clause);
  free(cnf.clauses);
    
  // free memory for the learned cnf
  mutable_free_clauses(&learned_cnf);

  // free memory for the model
  for (which_ass = 0; which_ass < num_asses; which_ass++)
    mutable_free(&(model[which_ass].watched_lits));
  free(model);
  
  // free memory for the trail
  free(trail.sequence);
}

void CDCL_prop()
{
  // handles the entire propagation cycle in a single function
  // terminates when head and tail trail pointers coincide
  
  // this function is responsible for all watched literal handling,
  // conflict detection and backtracking in the current version

  ass_t* temp_lit;
  model_size_t which_lit, candidate;
  ass_t** lits;
  cnf_size_t num_clauses, which_clause;
  mutable_t new_watchers;
  ass_t* propagator;
  clause_t** data;
  clause_t* clause;
  model_size_t dec_level;

  VERBOSE_(fprintf(stderr, "In CDCL_prop()..\n"));
  
  while (trail.head != trail.tail)
    {
      // make a local copy of the literal that we are propagating
      propagator = *(trail.head);
      dec_level = propagator->dec_level;
      
      // add the propagating assignment to the model, set all successive additions
      // as propagations
      VERBOSE_(print_model());
      VERBOSE_(print_trail());
      
      // make a local pointer to the list of watched literals, and get the list size 
      data = propagator->watched_lits.data;
      num_clauses = propagator->watched_lits.used;

      // initialise a new mutable for the replacement list
      mutable_init(&new_watchers);

      VERBOSE_(fprintf(stderr, "Propagating literal %ld on %lu clauses\n",
			lit_to_DIMACS(propagator), num_clauses));
      
      // cycle through the watched literals' clauses
      for (which_clause = 0; which_clause < num_clauses; which_clause++)
	{
	  // get the literals and the clause width
	  clause = data[which_clause];

	  // only work on living clauses
	  if(clause->width != 0)
	    {
	      // place the watched literal at the front of the clause
	      lits = clause->lits;
	      if(lits[0] != get_comp_lit(propagator))
		{
		  temp_lit = lits[0];
		  lits[0] = lits[1];
		  lits[1] = temp_lit;		  
		}

	      VERBOSE_(fprintf(stderr, "Dealing with clause: "));
	      VERBOSE_(print_clause(clause));
	      VERBOSE_(fprintf(stderr, " -> "));
	      
	      // the first case to deal with: the other watched literal is POSITIVE
	      // and its decision level is no larger than propagation dec level
	      if (lits[1]->truth_value == POSITIVE && lits[1]->dec_level <= dec_level)
		{
		  // if its dec level is 0, delete the clause
		  if (lits[1]->dec_level == 0)
		    {
		      for (which_lit = 0; which_lit < clause->width - 1; which_lit++)
			{			 
			  if(--(lits[which_lit]->num_active) == 1)
			    {
			      // TODO: propagate as pure literal
			      trail_queue_lit(lits[which_lit], dec_level);
			      num_pure_props++;
			    }
			}
		      
		      clause->width = 0;
		      
		      VERBOSE_(fprintf(stderr, "clause deleted"));
		      VERBOSE_(fprintf(stderr, 
					" (other watched literal is dec level 0)\n"));
		    }
		  else
		    {
		      // otherwise, preserve the watched literal
		      mutable_push(&new_watchers, clause);
		      
		      VERBOSE_(print_clause(clause));
		      VERBOSE_(fprintf(stderr, 
					" (no change - other watched literal is satisfied)\n"));
		    }
		}
	      // the other case : try to swap the current watched literal
	      else 
		{
		  // search for a candidate
		  candidate = 2;
		  while(candidate < clause->width &&
			lits[candidate]->truth_value == NEGATIVE &&
			lits[candidate]->dec_level <= dec_level)
		      candidate++;		    

		  // if there is no candidate, we have a unit clause
		  // the unit literal is the other watched literal, lits[1]
		  if (candidate == clause->width)
		    {
		      num_unit_props++; // TODO: increment here or when processed?
		      VERBOSE_(fprintf(stderr, "found unit clause %ld",
					lit_to_DIMACS(lits[1])));
		      
		      // preserve the propagator as watched literal for this clause
		      mutable_push(&new_watchers, clause);
		  
		      if (get_comp_lit(lits[1])->trail_pos != NULL && get_comp_lit(lits[1])->trail_pos < trail.tail) 
			{
			  // the propagated assignment yields a conflict
			  num_conflicts++;
			  VERBOSE_(fprintf(stderr,
					    " -- detected conflict.\n"));
			  
			  // at level 0 the conflict is fatal
			  if (dec_level == 0)
			    {
			      report_UNSAT();
			      exit(0);
			    }
			  
			  // preserve watched literals on unprocessed clauses
			  for (which_clause++; which_clause < num_clauses; which_clause++)
			    mutable_push(&new_watchers, data[which_clause]);
			  
			  // reverse last decision
			  // go backwards through the trail and delete the assignments
			  trail.tail--;
			  while((trail.tail >= trail.sequence) &&
				((*trail.tail)->dec_level == dec_level))
			      trail.tail--;
			  trail.tail++;
			  trail.head = trail.tail;
			  
			  trail_queue_lit(get_comp_lit(*(trail.head)),
					      dec_level - 1);	

			  // the solution, since we increment the head later in all 
			  // cases TODO: is there a better solution?
			  trail.head--;
			  VERBOSE_(print_model());
			  VERBOSE_(print_trail());
			}
		      else if (lits[1]->trail_pos != NULL && lits[1]->trail_pos < trail.tail) 
			{
			  VERBOSE_(fprintf(stderr, " (ignoring repeated unit clause)\n"));
			}
		      else
			{
			  // queue the unit literal at the current decision level
			  trail_queue_lit(lits[1], dec_level);
			  VERBOSE_(fprintf(stderr,
					    " -- added to trail.\n"));
			}
		    }
		  else
		    {
		      // TODO handle case: candidate is decision level 0 - delete clause
		      // we found a candidate -- swap it with the watched literal
		      temp_lit = lits[0];
		      lits[0] = lits[candidate];
		      lits[candidate] = temp_lit;
		      
		      // add it to the appropriate list
		      mutable_push(&(get_comp_lit(lits[0])->watched_lits),
				   clause);
		      
		      VERBOSE_(print_clause(clause));
		      VERBOSE_(fprintf(stderr, "\n"));		      
		    }
		}
	    }
	}

      // instate new watched literals for the propagator      
      mutable_free(&(propagator->watched_lits));
      propagator->watched_lits = new_watchers;

      // increment head
      trail.head++;

      VERBOSE_(fprintf(stderr,
			"Completed propagation on literal %ld.\n",
			lit_to_DIMACS(propagator)));
      //VERBOSE_(print_watched_lits());
    }

  // propagation terminates
  VERBOSE_(fprintf(stderr,"Propagation cycle complete.\n"));
  VERBOSE_(print_model());
  VERBOSE_(print_trail());
  return;
}
		  
void CDCL_decide()
{
  // easy decision heuristic: selects the first unassigned variable positively 
  // and places it on the trail

  // trail head and tail should be equal when this function is called
  // and when it returns

  model_size_t which_var;
  model_size_t dec_level;

  VERBOSE_(fprintf(stderr, "In CDCL_decide(). "));

  if (trail.head == trail.sequence + num_vars)
    {
      report_SAT();
      exit(0);
    }
  if (trail.head == trail.sequence)
    {
      trail_queue_lit(*trail.head, 1);
    }
  else
    {
      trail_queue_lit(*trail.head, (*(trail.head - 1))->dec_level + 1);
    }

  VERBOSE_(fprintf(stderr, "Made decision %lu.\n",
		    lit_to_DIMACS(*trail.head)));
  VERBOSE_(print_model());
  VERBOSE_(print_trail());
  
  // find an unassigned var
  //for (which_var = 0; which_var < num_vars; which_var++)
  //  {
  //   if(model[which_var].dec_level == DEC_MAX)
  //	{
  //  // find the current decision level
  //	  if (trail.head == trail.sequence) dec_level = 1;
  //	  else dec_level = (*(trail.head - 1))->dec_level + 1;
  //
  //	  // queue the assignment on the trail (here the assignment is always positive)
  //	  trail_queue_lit(model + which_var, dec_level);
  //
  //	  // record the decision
  //	  num_decisions++;	  
  //	  return;
  //	}	
  //    }
  //
  //  return;
  //}

void CDCL_print()
{
  print_cnf();
  fprintf(stderr, "\n");
  print_model();
  print_trail();
}

// HELPER FUNCTION IMPLEMENTATION

//  error function implementation

// literal related

ass_t* DIMACS_to_lit(DIMACS_lit_t value)
{
  // converts a DIMACS literal into an internal literal
  return  model + ((value < 0 ? -1 : 1) * value) - 1 + ((value < 0) * num_vars);
}

DIMACS_lit_t lit_to_DIMACS(ass_t* lit)
{
  // converts an internal literal back into a DIMACS literal
  // this should only ever be used for printing or debugging
  return (DIMACS_lit_t)(((lit - model) % num_vars) + 1) * (((lit - model) < num_vars) ? 1 : -1);
}

ass_t* get_comp_lit(ass_t* lit)
{
  // returns the complementary literal
  return lit + ((lit - model < num_vars? 1 : -1) * num_vars);
}

// clause related

clause_t clause_init(model_size_t width)
{
  // initialises a clause of size `width'
  // the fist `literal' is the size of the clause 
  clause_t clause;

  clause.width = width;
  if ((clause.lits = (ass_t**)malloc(sizeof(ass_t*) * (width))) == NULL)
    error("cannot allocate clause literals");

  return clause;
}

void clause_free(clause_t* clause)
{
  free(clause->lits);
}

// cnf related


// mutable related

void mutable_init(mutable_t* mutable)
{
  // allocate memory for data - default size is 1
  if ((mutable->data = (clause_t**)malloc(sizeof(clause_t*))) == NULL)
    error("cannot allocate mutable data");

  // set default member values
  mutable->size = 1L;
  mutable->used = 0L;
}

// use this to free a watched literal list
void mutable_free(mutable_t* mutable)
{
  // frees only the data of the pointed to mutable
  free(mutable->data);
}

// use this to free learned cnf
void mutable_free_clauses(mutable_t* mutable)
{
  // frees both the data of the pointed to mutable, and the clauses
  // that the data points to
  cnf_size_t which_clause, num_clauses;

  num_clauses = mutable->used;
  for(which_clause = 0; which_clause < num_clauses; which_clause++)
    clause_free((clause_t*)*(mutable->data + which_clause));
  free(mutable->data);
}

void mutable_push(mutable_t* mutable, clause_t* datum)
{
  // pushes the datum onto the mutable's data array
  mutable_size_t size;

  if (mutable->used == (size = mutable->size))
    {
      if ((mutable->data = 
	   (clause_t**)realloc(mutable->data, 2 * size * sizeof(clause_t*))) == NULL)
	error("cannot reallocate mutable data");
      mutable->size = 2 * size;
      mutable->data[mutable->used++] = datum;
    }
  else
    {
      mutable->data[mutable->used++] = datum;      
    }
}

void unassign(ass_t* lit)
{
  // unassigns the variable for this literal (i.e. for the literal and its complement)
  lit->dec_level = DEC_MAX;
  get_comp_lit(lit)->dec_level = DEC_MAX;
}

// trail related

void trail_queue_lit(ass_t* lit, model_size_t dec_level)
{
  // make some temp copies
  ass_t* comp_lit = get_comp_lit(lit);
  ass_t** temp_trail_pos = lit->trail_pos;
  ass_t* temp_lit = *trail.tail;

  // place the queued literal at the tail
  *(trail.tail) = lit;
  lit->trail_pos = trail.tail;

  // move the literal that was at tail 
  if ((temp_lit->trail_pos = temp_trail_pos) != NULL)
    *(temp_trail_pos) = temp_lit
    
  // queue assignment at given decision level
  lit->dec_level = dec_level;
  lit->truth_value = POSITIVE;
  comp_lit->dec_level = dec_level;
  comp_lit->truth_value = NEGATIVE;
  
  // place assignment at tail of trail
  *(trail.tail) = lit;
  trail.tail++;
}

// printing and debugging

void print_lit(ass_t** lit)
{
  //(stderr, "%lu", *lit);
  // prints an internal literal in the form of a DIMACS literal
  fprintf(stderr, "%ld", lit_to_DIMACS(*lit));
}

void print_clause(clause_t* clause)
{
  model_size_t num_lits = clause->width;
  model_size_t which_lit;

  for(which_lit = 0; which_lit < num_lits; which_lit++)
    {
      print_lit(clause->lits + which_lit);
      fprintf(stderr, " ");
    }
}

void print_watched_lits()
{
  model_size_t which_ass;
  cnf_size_t which_clause;
  ass_t* temp_ass;
  
  for (which_ass = 0; which_ass < num_vars * 2; which_ass++)
    {
      temp_ass = model + which_ass;
      fprintf(stderr, "WATCHED LITERALS for literal %ld\n", lit_to_DIMACS(temp_ass));
      for (which_clause = 0; which_clause < temp_ass->watched_lits.used; which_clause++)
	{
	  print_clause(temp_ass->watched_lits.data[which_clause]);
	  fprintf(stderr, "\n");
	}
    }
  fprintf(stderr, "\n");
}


// prints the value of an assignment and its decision level
void print_ass(ass_t* ass)
{
  if(ass->dec_level != DEC_MAX)
      fprintf(stderr, "%d / %lu ", ass->truth_value, ass->dec_level);
}

void print_model()
{
  model_size_t which_var;

  fprintf(stderr, "MODEL:\n");      
    
  // print the assignment
  for(which_var = 0; which_var < num_vars; which_var++)
    {
      fprintf(stderr, "%lu: ", which_var + 1);
      print_ass(model + which_var);
      fprintf(stderr, "\n");
    }
  fprintf(stderr, "\n");
}




*/

// DIMACS related

var_t* DIMACS_to_var(DIMACS_lit_t DIMACS_lit)
{
  return  varset + ((DIMACS_lit < 0 ? -1 : 1) * DIMACS_lit) - 1;
}

phase_t DIMACS_to_phase(DIMACS_lit_t DIMACS_lit)
{
  return  (DIMACS_lit < 0 ? NEGATIVE : POSITIVE);
}

DIMACS_lit_t lit_to_DIMACS(lit_t* lit)
{
  return (DIMACS_lit_t)((lit->var - varset) + 1) * (lit->phase == POSITIVE ? 1 : -1);
}

DIMACS_lit_t ass_to_DIMACS(ass_t* ass)
{
  return (DIMACS_lit_t)((ass->var - varset) + 1) * (ass->phase == POSITIVE ? 1 : -1);
}

// clause related

clause_t clause_init(varset_size_t width)
{
  // initialises a clause of size `width'
  clause_t clause;

  clause.width = width;
  if ((clause.lits = (lit_t*)malloc(sizeof(lit_t) * (width))) == NULL)
    error("cannot allocate clause literals");

  return clause;
}

void clause_free(clause_t* clause)
{
  free(clause->lits);
}

// list related

void list_init(list_t* list)
{
  // allocate memory for data - default size is 1
  if ((list->clauses = (clause_t**)malloc(sizeof(clause_t*))) == NULL)
    error("cannot allocate list data");

  // set default member values
  list->size = 1L;
  list->used = 0L;
  list->at = 0L;
}

// use this to free a watched literal list
void list_free(list_t* list)
{
  // frees only the data of the pointed to list
  free(list->clauses);
  list->clauses = NULL;
  list->size = (list->used = (list->at = 0));
}

void list_push(list_t* list, clause_t* clause)
{
  // pushes the datum onto the list's data array
  list_size_t size;

  if (list->used == (size = list->size))
    {
      if ((list->clauses = 
	   (clause_t**)realloc(list->clauses, 2 * size * sizeof(clause_t*))) == NULL)
	error("cannot reallocate list data");
      list->size = 2 * size;
      list->clauses[list->used++] = clause;
    }
  else
    {
      list->clauses[list->used++] = clause;      
    }
}

// group related

group_t* group_init(group_id_t id)
{
  group_t* group;

  if ((group = (group_t*)malloc(sizeof(group_t))) == NULL)
    error("cannot allocate group_t");
  group->id = id;
  group->first = (group->last = NULL);

  return group;
}

void group_free(group_t* group)
{
  ;
}

void pool_add_ass(ass_t* ass)
{
  // add assignment to pool
  if (trail.pool->last == NULL)
    {
      trail.pool->first = (trail.pool->last = ass);
      ass->prev = (ass->next = NULL);
    }
  else
    {
      trail.pool->last->next = ass;
      ass->prev = trail.pool->last;
      ass->next = NULL;
      trail.pool->last = ass;
    }
  ass->head = trail.pool;
}

int queue(group_t* group, var_t* var, phase_t phase)
{
  ass_t* ass = var->trail_pos;

  VERBOSE_(fprintf(stderr, "In queue(): "));
  VERBOSE_(fprintf(stderr, "queueing variable %ld in phase %d\n",
		   var - varset + 1,
		   phase));
  VERBOSE_(print_stats());

  // if  assignment is already in model, ignore and return 0:
  if (var->trail_pos->head == trail.model && var->trail_pos->phase == phase)
    return 0;

  // check for conflict: 
  // TODO: expand during implementation of propagation 
  if ((group->id == MODEL) && 
      (ass->phase != phase) &&
      (ass->head->id == MODEL))
    {
      // a conflict between implied literals -- fatal
      num_conflicts++;
      report_UNSAT();
    }
  // remove the assignment from its current group
  if (ass->next == NULL)
    ass->head->last = ass->prev;
  else
    ass->next->prev = ass->prev;
  if (ass->prev == NULL)
    ass->head->first = ass->next;
  else
    ass->prev->next = ass->next;

  // add assignment to new group
  ass->phase = phase;
  if (group->last == NULL)
    {
      group->first = (group->last = ass);
      ass->prev = (ass->next = NULL);
    }
  else
    {
      ass->prev = group->last;
      ass->next = NULL;
      group->last->next = ass;
      group->last = ass;
    }
  ass->head = group;
  
  // indicate that queueing was successful
  return 1;
}

// miscellaneous

void error(char* message)
{
  fprintf(stderr, "FATAL ERROR: %s.\n", message);
  exit(1);
}

void report_SAT()
{
  VERBOSE_(print_trail());
  fprintf(stderr, "v SAT\n");
  print_stats();
  exit(0);
}
void report_UNSAT()
{
  VERBOSE_(print_trail());
  fprintf(stderr, "v UNSAT\n");
  print_stats();
  exit(0);
}

// printing and debugging

void print_lit(lit_t* lit)
{
  // prints an internal literal in the form of a DIMACS literal
  fprintf(stderr, "%ld", lit_to_DIMACS(lit));
}

void print_clause(clause_t* clause)
{
  varset_size_t which_lit, num_lits = clause->width;

  for(which_lit = 0; which_lit < num_lits; which_lit++)
    {
      print_lit(clause->lits + which_lit);
      fprintf(stderr, " ");
    }
}

void print_cnf()
{
  cnf_size_t which_clause;
  
  fprintf(stderr, "FORMULA:\n");
  for(which_clause = 0; which_clause < cnf.size; which_clause++)
    {
      print_clause(cnf.clauses + which_clause);
      fprintf(stderr, "\n");
    }
}

void print_list(list_t *list)
{
  cnf_size_t which_clause, num_clauses = list->used;
  clause_t** clauses = list->clauses;

  for (which_clause = 0; which_clause < num_clauses; which_clause++)
    {
	  print_clause(clauses[which_clause]);
	  fprintf(stderr, "\n");
    }
}

void print_ass(ass_t* ass)
{
  fprintf(stderr, "%ld", ass_to_DIMACS(ass));
}

void print_group(group_t* group)
{
  ass_t* ass;

  switch(group->id)
    {
    case POOL:
      fprintf(stderr, "P ");
      break;
    case MODEL:
      fprintf(stderr, "M ");
      break;
    default:
      fprintf(stderr, "%lu ", group->id);
    }  
  
  ass = group->first;
  while(ass != NULL)
    {
      print_ass(ass);
      fprintf(stderr, " ");
      ass = ass->next;
    }
  fprintf(stderr, "\n");
}

void print_trail()
{
  // print model
  print_group(trail.model);

  // print pool
  print_group(trail.pool);

  // print rest of trail
}

void print_stats()
{
  fprintf(stderr, "Conflicts:         %lu\n", num_conflicts);
  fprintf(stderr, "Decisions:         %lu\n", num_decisions);
  fprintf(stderr, "Unit Propagations: %lu\n", num_unit_props);
  fprintf(stderr, "Pure Propagations: %lu\n", num_pure_props);
  fprintf(stderr, "%1.1lfs ", ((double)(clock() - start_time)) / CLOCKS_PER_SEC);
  fprintf(stderr, "%1.1zdMb ", getPeakRSS() / 1048576);
  fprintf(stderr, "\n");
}

// asserts

void assert_literal_validity(DIMACS_lit_t DIMACS_lit)
{
  if ((((DIMACS_lit < 0 ? -1 : 1) * DIMACS_lit) - 1) >= num_vars)
    {
      error("bad input: literal magnitude exceeds number of variables");
      exit(1);
    }
  ;
}
