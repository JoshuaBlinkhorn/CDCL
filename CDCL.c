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
#include "getRSS.c"

#ifdef DEBUG
#define DEBUG_MSG(x) (x)
#else
#define DEBUG_MSG(x) 
#endif

// MACROS

// truth values / phases
#define POSITIVE 1
#define NEGATIVE 0

// highest decision level (indicates an avaliable decision)
#define DEC_MAX ULONG_MAX
#define MAX_VARS (ULONG_MAX / 2 - 1)

// native type aliases
typedef signed char truth_value_t;
typedef signed char phase_t;
typedef signed long int DIMACS_lit_t;
typedef unsigned long int cnf_size_t;
typedef unsigned long int varset_size_t; 
typedef unsigned long int list_size_t;
typedef unsigned long int dec_id_t;

// MAIN STRUCTURE OF DATA 

struct dec {
  dec_id_t id;
  struct dec* next;
  struct ass {
    struct dec* head;
    struct ass* prev;
    struct ass* next;
    struct var {
      struct ass* trail_pos;
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

typedef struct dec dec_t;
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
  dec_t* pool;
  dec_t* implied;
  dec_t* head;
  dec_t* current;
  dec_t* conflict;
  ass_t* cursor;
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
var_t* model;
trail_t trail;

// stats
clock_t start_time;
unsigned long num_conflicts = 0;
unsigned long num_decisions = 0;
unsigned long num_unit_props = 0;
unsigned long num_pure_props = 0;
unsigned long num_redefinitions = 0;

void dec_add_ass(dec_t* dec, ass_t* ass)
{
  ass->head = dec;
  ass->next = dec->first;
  dec->first = ass;
}

void queue(dec_t* dec, var_t* var, phase_t phase)
{
  ass_t* temp_ass = var->trail_pos;
  temp_ass->prev->next = temp_ass->next;
  temp_ass->next->prev = temp_ass->prev;
  temp_ass->phase = phase;
  dec->last->next = temp_ass;
  temp_ass->prev = dec->last;
  temp_ass->next = NULL;
  dec->last = temp_ass;
}

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
void print_watched_lits();
void print_model();
void print_trail();
void print_stats();

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
  if ((model = (var_t*)malloc(sizeof(var_t) * num_vars)) == NULL)
	error("cannot allocate model");

  // initialise pool group and default assignments
  // initially the pool contains all variables
  if ((trail.pool = (dec_t*)malloc(sizeof(dec_t))) == NULL)
    error("cannot allocate dec_t pool");

  for (which_var = 0; which_var < num_vars; which_var++)
    {
      ass = (ass_t*)malloc(sizeof(ass_t));
      ass->var = model + which_var;
      ass->phase = POSITIVE;
      dec_add_ass(trail.pool, ass);
      model[which_var].trail_pos = ass;
    }
  
  // initialise implied literal group
  if ((trail.implied = (dec_t*)malloc(sizeof(dec_t))) == NULL)
    error("cannot allocate dec_t pool");

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
	fscanf(cursor, "%ld", &DIMACS_lit);

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
	  queue(trail.implied, DIMACS_to_var(DIMACS_lit), DIMACS_to_phase(DIMACS_lit));
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

  DEBUG_MSG(fprintf(stderr, "In CDCL_prop()..\n"));
  
  while (trail.head != trail.tail)
    {
      // make a local copy of the literal that we are propagating
      propagator = *(trail.head);
      dec_level = propagator->dec_level;
      
      // add the propagating assignment to the model, set all successive additions
      // as propagations
      DEBUG_MSG(print_model());
      DEBUG_MSG(print_trail());
      
      // make a local pointer to the list of watched literals, and get the list size 
      data = propagator->watched_lits.data;
      num_clauses = propagator->watched_lits.used;

      // initialise a new mutable for the replacement list
      mutable_init(&new_watchers);

      DEBUG_MSG(fprintf(stderr, "Propagating literal %ld on %lu clauses\n",
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

	      DEBUG_MSG(fprintf(stderr, "Dealing with clause: "));
	      DEBUG_MSG(print_clause(clause));
	      DEBUG_MSG(fprintf(stderr, " -> "));
	      
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
		      
		      DEBUG_MSG(fprintf(stderr, "clause deleted"));
		      DEBUG_MSG(fprintf(stderr, 
					" (other watched literal is dec level 0)\n"));
		    }
		  else
		    {
		      // otherwise, preserve the watched literal
		      mutable_push(&new_watchers, clause);
		      
		      DEBUG_MSG(print_clause(clause));
		      DEBUG_MSG(fprintf(stderr, 
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
		      DEBUG_MSG(fprintf(stderr, "found unit clause %ld",
					lit_to_DIMACS(lits[1])));
		      
		      // preserve the propagator as watched literal for this clause
		      mutable_push(&new_watchers, clause);
		  
		      if (get_comp_lit(lits[1])->trail_pos != NULL && get_comp_lit(lits[1])->trail_pos < trail.tail) 
			{
			  // the propagated assignment yields a conflict
			  num_conflicts++;
			  DEBUG_MSG(fprintf(stderr,
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
			  DEBUG_MSG(print_model());
			  DEBUG_MSG(print_trail());
			}
		      else if (lits[1]->trail_pos != NULL && lits[1]->trail_pos < trail.tail) 
			{
			  DEBUG_MSG(fprintf(stderr, " (ignoring repeated unit clause)\n"));
			}
		      else
			{
			  // queue the unit literal at the current decision level
			  trail_queue_lit(lits[1], dec_level);
			  DEBUG_MSG(fprintf(stderr,
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
		      
		      DEBUG_MSG(print_clause(clause));
		      DEBUG_MSG(fprintf(stderr, "\n"));		      
		    }
		}
	    }
	}

      // instate new watched literals for the propagator      
      mutable_free(&(propagator->watched_lits));
      propagator->watched_lits = new_watchers;

      // increment head
      trail.head++;

      DEBUG_MSG(fprintf(stderr,
			"Completed propagation on literal %ld.\n",
			lit_to_DIMACS(propagator)));
      //DEBUG_MSG(print_watched_lits());
    }

  // propagation terminates
  DEBUG_MSG(fprintf(stderr,"Propagation cycle complete.\n"));
  DEBUG_MSG(print_model());
  DEBUG_MSG(print_trail());
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

  DEBUG_MSG(fprintf(stderr, "In CDCL_decide(). "));

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

  DEBUG_MSG(fprintf(stderr, "Made decision %lu.\n",
		    lit_to_DIMACS(*trail.head)));
  DEBUG_MSG(print_model());
  DEBUG_MSG(print_trail());
  
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


void print_trail()
{
  ass_t** temp_pointer;
  model_size_t which_var, dec_level;

  fprintf(stderr, "TRAIL:\n");

  for(which_var = 0, temp_pointer = trail.sequence; which_var < num_vars; which_var++, temp_pointer++)
    {
      fprintf(stderr, "%lu: %ld / ",
	      which_var + 1,
	      lit_to_DIMACS(*(temp_pointer)));

      if ((*temp_pointer)->dec_level == DEC_MAX)
	fprintf(stderr, "M");
      else
	fprintf(stderr, "%lu", (*temp_pointer)->dec_level);
      if (temp_pointer == trail.head) fprintf(stderr, " HEAD");
      if (temp_pointer == trail.tail) fprintf(stderr, " TAIL");
      fprintf(stderr, "\n");
    }
  fprintf(stderr, "\n");
}


*/

// DIMACS related

var_t* DIMACS_to_var(DIMACS_lit_t DIMACS_lit)
{
  return  model + ((DIMACS_lit < 0 ? -1 : 1) * DIMACS_lit) - 1;
}

phase_t DIMACS_to_phase(DIMACS_lit_t DIMACS_lit)
{
  return  (DIMACS_lit < 0 ? NEGATIVE : POSITIVE);
}

DIMACS_lit_t lit_to_DIMACS(lit_t* lit)
{
  return (DIMACS_lit_t)((lit->var - model) + 1) * (lit->phase == POSITIVE ? 1 : -1);
}

DIMACS_lit_t ass_to_DIMACS(ass_t* ass)
{
  return (DIMACS_lit_t)((ass->var - model) + 1) * (ass->phase == POSITIVE ? 1 : -1);
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

// miscellaneous

void error(char* message)
{
  fprintf(stderr, "FATAL ERROR: %s.\n", message);
  exit(1);
}

void report_SAT()
{
  //print_model();
  fprintf(stderr, "v SAT\n");
  print_stats();
  exit(0);
}
void report_UNSAT()
{
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

void  print_stats()
{
  fprintf(stderr, "Conflicts:         %lu\n", num_conflicts);
  fprintf(stderr, "Decisions:         %lu\n", num_decisions);
  fprintf(stderr, "Unit Propagations: %lu\n", num_unit_props);
  //fprintf(stderr, "Redefinitions:     %lu\n", num_redefinitions);
  fprintf(stderr, "%1.1lfs ", ((double)(clock() - start_time)) / CLOCKS_PER_SEC);
  fprintf(stderr, "%1.1zdMb ", getPeakRSS() / 1048576);
  fprintf(stderr, "\n");
}
