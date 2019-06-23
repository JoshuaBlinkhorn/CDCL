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

// results
#define UNSAT 0
#define SAT 1

// truth values
#define POSITIVE 1
#define NEGATIVE -1

// highest decision level (indicates an avaliable decision)
#define DEC_MAX ULONG_MAX
#define MAX_VARS ULONG_MAX / 2

// assignment types
#define DEC_ASS 0
#define PROP_ASS 1
#define CON_ASS 2

// assignment states -- ordered as they appear on the trail
#define DECEASED 1
#define ACTIVE 2
#define PENDING 3
#define AVAILABLE 4

// special values
#define NULL_DEC_LEVEL ULONG_MAX - 1
#define MAX_VARS ULONG_MAX / 2

// low level types
typedef unsigned char result_t;
typedef signed char truth_value_t;
typedef unsigned char ass_type_t;
typedef unsigned char ass_status_t;
typedef signed long int DIMACS_lit_t;
typedef unsigned long int cnf_size_t;
typedef unsigned long int model_size_t; 
typedef unsigned long int mutable_size_t;
typedef unsigned long int lit_t;
typedef signed long int DIMACS_lit_t;

// stats
clock_t start_time;

// higher level types 

// mutable (array)

// this is an automatically resized array of pointers to lit_t.
// it can be used to store a cnf, or a list of pointers to literals (e.g. the 
// watched literals for a singleton assignment), which can also be thought of
// as a set of unit clauses

// the array becomes twice as large whenever necessary to add an item

typedef struct ass {
  ass_status_t ass_status;
  truth_value_t truth_value;
  ass_type_t ass_type; 
  model_size_t dec_level;
  cnf_size_t num_active;

  struct mutable {
    mutable_size_t size;
    mutable_size_t used;

    struct clause {
      struct ass** lits;
      model_size_t width;
    };
    
    struct clause** data;
  };

  struct mutable watched_lits;

} ass_t;

typedef struct mutable mutable_t;
typedef struct clause clause_t;

// assignment

// stores various information about a singleton assignment, including
// a list of watched literals


// clause

// cnf

// a CNF is a struct storing (1) an array of clauses and (2) the size of the array 

typedef struct cnf {
  clause_t* clauses;
  cnf_size_t size;
} cnf_t;

// trail

// a trail is an ordered sequence of pointers literals
// it is allocated as a fixed size array, since it size never exceeds
// the number of variables
// head and tail are pointers into the array used in propagation

typedef struct trail {
  ass_t** sequence;
  ass_t** head;
  ass_t** tail;
} trail_t;

// global solver

// data
model_size_t num_vars;
model_size_t num_asses;

// stats variables
unsigned long num_conflicts = 0;
unsigned long num_decisions = 0;
unsigned long num_unit_props = 0;
unsigned long num_redefinitions = 0;

// decision pointers
ass_t* dec_head;
ass_t* dec_tail;

// organs
cnf_t cnf;
mutable_t learned_cnf;
ass_t* model;
trail_t trail;
state_t stat;

// IMPLEMENTATION

void error(char* message);

// LITERAL RELATED FUNCTIONS

ass_t* DIMACS_to_lit(DIMACS_lit_t value)
{
  // converts a DIMACS literal into an internal literal
  // internal literals are represented as values from 0 to (2 * num_vars) - 1
  // values from 0 to num_vars - 1 represent positive literals,
  // values from num_vars to (2 * num_vars) - 1 represent negative literals.
  return  model + ((value < 0 ? -1 : 1) * value) - 1 + ((value < 0) * num_vars);
}

DIMACS_lit_t lit_to_DIMACS(ass_t* lit)
{
  // converts an internal literal back into a DIMACS literal
  // this should only ever be used for printing literal values
  return (DIMACS_lit_t)(((lit - model) % num_vars) + 1) * (((lit - model) < num_vars) ? 1 : -1);
}

ass_t* get_comp_lit(ass_t* lit)
{
  // returns the complementary literal
  return lit + ((lit - model < num_vars? 1 : -1) * num_vars);
}

void lit_print(ass_t** lit)
{
  //(stderr, "%lu", *lit);
  // prints an internal literal in the form of a DIMACS literal
  fprintf(stderr, "%ld", lit_to_DIMACS(*lit));
}


// CLAUSE RELATED FUNCTIONS

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

char clause_is_unit(clause_t* clause)
{
  // returns 1 if the given clause is a unit clause, 0 otherwise
  return (clause->width == 1) ? 1 : 0;
}

void clause_free(clause_t* clause)
{
  free(clause->lits);
}

void clause_print(clause_t* clause)
{
  model_size_t num_lits = clause->width;
  model_size_t which_lit;

  for(which_lit = 0; which_lit < num_lits; which_lit++)
    {
      lit_print(clause->lits + which_lit);
      fprintf(stderr, " ");
    }
}

// CNF RELATED FUNCTIONS

void cnf_print()
{
  cnf_size_t which_clause;
  
  fprintf(stderr, "FORMULA:\n");
  for(which_clause = 0; which_clause < cnf.size; which_clause++)
    {
      clause_print(cnf.clauses + which_clause);
      fprintf(stderr, "\n");
    }
}


// MUTABLE RELATED FUNCTIONS

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

// use to print a learned cnf
void mutable_print_clauses(mutable_t* mutable)
{
  mutable_size_t which_clause, num_clauses;
  clause_t** data;
  
  fprintf(stderr, "LEARNED CLAUSES:\n");
  fprintf(stderr, "size: %lu, used: %lu\n", mutable->size, mutable->used);

  num_clauses = mutable->used;
  data = mutable->data;
  for(which_clause = 0; which_clause < num_clauses; which_clause++)
    {
      clause_print(data[which_clause]);
      fprintf(stderr, "\n");
    }
}


/*
// use to print a watched literal list // TODO deprecate, or hone for debugginf
void mutable_print_lits(mutable_t* mutable)
{
  mutable_size_t which_lit, num_lits;
  lit_t** data;
  
  fprintf(stderr, "size: %lu, used: %lu, literals:", mutable->size, mutable->used);

  num_lits = mutable->used;
  data = mutable->data;
  for(which_lit = 0; which_lit < num_lits; which_lit++)
    {
      lit_print(data + which_lit);
    }
  fprintf(stderr, "\n");
}

*/
void print_watched_lits() // TODO deprecate, or hone for debugging
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
	  clause_print(temp_ass->watched_lits.data[which_clause]);
	  fprintf(stderr, "\n");
	}
    }
  fprintf(stderr, "\n");
}

// ASSIGNMENT RELATED FUNCTIONS

void assign(ass_t* lit)
{
  // overwrites the assignment satisfying the literal into the model
  // the assignment type should already have been set when the literal
  // was added to the trail
  ass_t* comp_lit = get_comp_lit(lit);

  lit->truth_value = POSITIVE;
  comp_lit->truth_value = NEGATIVE;
}

void unassign(ass_t* lit)
{
  // unassigns the variable for this literal (i.e. for the literal and its complement)
  lit->dec_level = DEC_MAX;
  get_comp_lit(lit)->dec_level = DEC_MAX;
}

// prints the value of an assignment and its decision level
void ass_print(ass_t* ass)
{
  if(ass->dec_level != DEC_MAX)
    {
      fprintf(stderr, "%d / %lu ", ass->truth_value, ass->dec_level);
      
      /* TODO: delete if ass_type is deprecated
      switch(ass->ass_type)
	{
	case DEC_ASS:
	  fprintf(stderr, "D ");
	  break;
	case PROP_ASS:
	  fprintf(stderr, "P ");
	  break;
	case CON_ASS:
	  fprintf(stderr, "C ");
	  break;
	default:
	  break;
	}
      */
    }
}

// this function assumes trail.head > trail.sequence
void backtrack(model_size_t new_dec_level)
{  
  DEBUG_MSG(fprintf(stderr,
		    "In backtrack(). Backtracking to decision level %lu.\n",
		    new_dec_level));
  // go backwards through the trail and delete the assignments
  while((trail.tail >= trail.sequence) && ((*(trail.tail))->dec_level > new_dec_level))
    {
      unassign(*trail.tail);
      trail.tail--;
    }
  trail.tail++;
  trail.head = trail.tail;
}

// MODEL RELATED FUNCTIONS

// prints the contents of the given model
void print_model()
{
  model_size_t which_var;

  fprintf(stderr, "MODEL:\n");      
    
  // print the assignment
  for(which_var = 0; which_var < num_vars; which_var++)
    {
      fprintf(stderr, "%lu: ", which_var + 1);
      ass_print(model + which_var);
      fprintf(stderr, "\n");
    }
  fprintf(stderr, "\n");
}
 
// TRAIL RELATED FUNCTIONS

void trail_queue_lit(ass_t* lit, model_size_t dec_level)
{
  ass_t* comp_lit = get_comp_lit(lit);

  // queue assignment at current decision level
  lit->dec_level = dec_level;
  lit->truth_value = POSITIVE;
  comp_lit->dec_level = dec_level;
  comp_lit->truth_value = NEGATIVE;

  // place assignment at tail of trail
  *(trail.tail) = lit;
  trail.tail++;
}

void print_trail()
{
  ass_t** temp_pointer;

  fprintf(stderr, "TRAIL: ");

  if (trail.sequence == trail.tail) 
    {
      fprintf(stderr, " (empty)\n\n");
      return;
    }
  fprintf(stderr, "\n");
  for(temp_pointer = trail.sequence; temp_pointer < trail.tail; temp_pointer++)
    {
      fprintf(stderr, "%lu: %ld / %lu",
	      temp_pointer - trail.sequence + 1,
	      lit_to_DIMACS(*temp_pointer),
	      (*temp_pointer)->dec_level);
      if (temp_pointer == trail.head) fprintf(stderr, " HEAD");
      if (temp_pointer == trail.tail) fprintf(stderr, " TAIL");
      fprintf(stderr, "\n");
    }
  fprintf(stderr, "\n");
}

// CDCL INTERFACE IMPLEMENTATION

void  CDCL_print_stats()
{
  fprintf(stderr, "Conflicts:         %lu\n", num_conflicts);
  fprintf(stderr, "Decisions:         %lu\n", num_decisions);
  fprintf(stderr, "Unit Propagations: %lu\n", num_unit_props);
  //fprintf(stderr, "Redefinitions:     %lu\n", num_redefinitions);
  fprintf(stderr, "%1.1lfs ", ((double)(clock() - start_time)) / CLOCKS_PER_SEC);
  fprintf(stderr, "%1.1zdMb ", getPeakRSS() / 1048576);
  fprintf(stderr, "\n");
}

void CDCL_report_SAT()
{
  print_model();
  fprintf(stderr, "v SAT\n");
  CDCL_print_stats();
  exit(0);
}
void CDCL_report_UNSAT()
{
  fprintf(stderr, "v UNSAT\n");
  CDCL_print_stats();
  exit(0);
}

// initialises global solver according to the DIMACS file 'input'.
void CDCL_init(char* DIMACS_filename)
{
  FILE* input, *cursor;
  char buffer[5]; // used only to read the `cnf' string from the input file
  char ch; // used to read single characters from the input file  
  DIMACS_lit_t DIMACS_lit; // temporary literal for reading
  model_size_t width; 
  model_size_t which_lit; 
  model_size_t which_ass; 
  cnf_size_t which_clause;
  clause_t clause;
  ass_t* lit;

  start_time = clock();
  state = DECIDE;

  // open file connections
  // TODO: currently using two file connections to find size of clauses before writing
  // them; it is probably possible to use just one, and to traverse the stream 
  // backwards when needed
  if ((input = (FILE *)fopen(DIMACS_filename, "r")) == NULL) error("cannot open file");
  if ((cursor = (FILE *)fopen(DIMACS_filename, "r")) == NULL) error("cannot open file");

  // parse header
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

  if (num_vars > pow(2,(sizeof(lit_t) * 8) - 3) - 1) // i.e. more variables than our data type can handle
    error("too many vars");
  num_asses = num_vars * 2;

  // initialise model
  if ((model = (ass_t*)malloc(sizeof(ass_t) * num_asses)) == NULL)
	error("cannot allocate model");
  for (which_ass = 0; which_ass < num_asses; which_ass++)
    {
      // set default values and initialise watched literals mutable for each assignment
      model[which_ass].dec_level = DEC_MAX; 
      model[which_ass].num_active = 0;
      mutable_init(&(model[which_ass].watched_lits));
    }

  // initialise trail
  if ((trail.sequence = (ass_t**)malloc(sizeof(ass_t*) * num_asses)) == NULL)
	error("cannot allocate trail sequence");
  trail.head = trail.sequence;
  trail.tail = trail.sequence;

  // read number of clauses
  if(fscanf(input, "%lu", &cnf.size) != 1)
    error("bad input - number of clauses not found");
  fscanf(cursor, "%lu", &cnf.size);

  if (cnf.size == 0)
    {
      CDCL_report_SAT();
      exit(0);
    }
  if (num_vars == 0)
    {
      CDCL_report_UNSAT();
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

      // if the width is 0, note that the formula is UNSAT and return
      if (width == 0)
	{
	  CDCL_report_UNSAT();
	  exit(0);
	}

      // if the width is 1, add the assignment as a level 0 unit propagation
      if (width == 1)
	{
	  fscanf(input, "%ld", &DIMACS_lit);
	  trail_queue_lit(DIMACS_to_lit(DIMACS_lit), 0);
	  fscanf(input, "%ld", &DIMACS_lit);
	  state = PROPAGATE;
	  // we do not store unit clauses, so decrement counters
	  cnf.size--;
	  which_clause--;
	}
      else 
	{
	  // initialise clause
	  clause = clause_init(width);
	  // set literals with input
	  which_lit = 0;
	  fscanf(input, "%ld", &DIMACS_lit);
	  while(DIMACS_lit != 0) 
	    {
	      clause.lits[which_lit] = (lit = DIMACS_to_lit(DIMACS_lit));
	      lit->num_active++;
	      fscanf(input, "%ld", &DIMACS_lit);
	      which_lit++;
	    }
	  
	  // put the clause into the cnf
	  cnf.clauses[which_clause] = clause;
	  
       	  // watch the first two literals
	  mutable_push(&(get_comp_lit(clause.lits[0])->watched_lits),
		       cnf.clauses + which_clause);
	  mutable_push(&(get_comp_lit(clause.lits[1])->watched_lits),
		       cnf.clauses + which_clause);
	}
    }
  
  // initialise empty learned clause list
  mutable_init(&(learned_cnf));
}

void CDCL_free()
{
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

// TODO: the watched literals should be the first two in the clause
// then we can deal with them by swapping them explicitly with some other literal,
// if possible

// handles the entire propagation cycle in a single function

// head should immediately precede tail of the trail when this function
// is called,
// in case of conflict, tail will exceed head when it returns 
// otherwise tail and head will be identical

// this function is responsible for all watched literals handling, except for the
// assignment of inital watched literals of learned clause, which is handled
// by conflict analysis

// the assignment at head when the function is called is handled first
// the watched literals are visited in order
// the function first attemps to push the watch to another literal
// if the clause is found to be unit, the assignment is checked for conflict
// if conflict is found, the watched literals for the current assignment are
// cleaned up and the function returns CONFLICT
// if no conflict is found, the unit assignment is added to the tail of the trail
// when all clauses have been visited, the trail head is incremented
// the function returns NO_CONFLICT when head and tail are again identical

state_t CDCL_prop()
{

  ass_t* temp_lit;
  model_size_t which_lit, candidate;
  ass_t** lits;
  cnf_size_t num_clauses, which_clause;
  mutable_t new_watchers;
  ass_t* propagator;
  clause_t** data;
  clause_t* clause;
  model_size_t dec_level;
  //ass_t* ass;

  DEBUG_MSG(fprintf(stderr, "In CDCL_prop()..\n"));
  
  while (trail.head != trail.tail)
    {
      // make a local copy of the literal that we are propagating
      propagator = *(trail.head);
      dec_level = propagator->dec_level;
      
      // add the propagating assignment to the model, set all successive additions
      // as propagations
      //assign(propagator);
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
	      DEBUG_MSG(clause_print(clause));
	      DEBUG_MSG(fprintf(stderr, " -> "));
	      
	      // the first case to deal with: the other watched literal is POSITIVE
	      // and its decision level is no larger than propagation dec level
	      if (lits[1]->truth_value == POSITIVE && lits[1]->dec_level <= dec_level)
		{
		  // if its dec level is 0, delete the clause
		  if (lits[1]->dec_level == 0)
		    {
		      for (which_lit = 0; which_lit < clause->width - 1; which_lit++)
			lits[which_lit]->num_active--;
		      clause->width = 0;
		      
		      DEBUG_MSG(fprintf(stderr, "clause deleted"));
		      DEBUG_MSG(fprintf(stderr, 
					" (other watched literal is dec level 0)\n"));
		    }
		  else
		    {
		      // otherwise, preserve the watched literal
		      mutable_push(&new_watchers, clause);
		      
		      DEBUG_MSG(clause_print(clause));
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
		  
		      if (lits[1]->dec_level <= dec_level)
			{
			  if (lits[1]->truth_value == POSITIVE)
			    {
			      // the variable is alredy assigned in the correct phase 
			      
			      DEBUG_MSG(fprintf(stderr,
						" -- ignored repeat assignment.\n"));			      
			    }
			  else
			    {
			      // the propagated assignment yields a conflict
			      num_conflicts++;
			      DEBUG_MSG(fprintf(stderr,
						" -- detected conflict.\n"));

			      // at level 0 the conflict is fatal
			      if (dec_level == 0)
				{
				  CDCL_report_UNSAT();
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
				{
				  unassign(*trail.tail);
				  trail.tail--;
				}
			      trail.tail++;
			      trail.head = trail.tail;

			      trail_queue_lit(get_comp_lit(*(trail.head)),
					      dec_level - 1);	

			      // the solution, since we increment the head later in all 
			      // cases TODO: is there a better solution?
			      trail.head--;
			      DEBUG_MSG(print_model());
			      DEBUG_MSG(print_trail());
			      DEBUG_MSG(fprintf(stderr, "head: %p, tail: %p\n",
					       trail.head, trail.tail));
			    }
			}
		      else
			{
			  // queue the unit literal at the current decision level
			  trail_queue_lit(lits[1], propagator->dec_level);
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
		      
		      DEBUG_MSG(clause_print(clause));
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
      DEBUG_MSG(print_watched_lits());
    }

  // propagation terminates
  DEBUG_MSG(fprintf(stderr,"Propagation cycle complete.\n"));
  DEBUG_MSG(print_model());
  DEBUG_MSG(print_trail());
  return DECIDE;
}
		  
// easy decision heuristic: assigns the first unassigned variable positively 
// trail.head and trail.tail are always equal when CDCL_decide() is called
// and point to the location after the final assignment
// if the function returns PROPAGATE, trail.head points to the location of
// the final assignment, trail.tail to the next location.  

char CDCL_decide()
{
  model_size_t which_var;
  model_size_t dec_level;

  DEBUG_MSG(fprintf(stderr, "In CDCL_decide(). "));

  if (trail.head == trail.sequence + num_vars)
    {
      CDCL_report_SAT();
      exit(0);
    }

  // find an unassigned var
  for (which_var = 0; which_var < num_vars; which_var++)
    {
      if(model[which_var].dec_level == DEC_MAX)
	{
	  // find the current decision level
	  if (trail.head == trail.sequence) dec_level = 1;
	  else dec_level = (*(trail.head - 1))->dec_level + 1;

	  // queue the assignment on the trail (here the assignment is always positive)
	  trail_queue_lit(model + which_var, dec_level);

	  // record the decision
	  num_decisions++;

	  DEBUG_MSG(fprintf(stderr, "Made decision %lu.\n",
			    lit_to_DIMACS(model + which_var)));
	  DEBUG_MSG(print_model());
	  DEBUG_MSG(print_trail());
	  
	  return PROPAGATE;
	}	
    }
  DEBUG_MSG(fprintf(stderr, "No decision possible.\n"));
  return SUCCESS;
}


// the simplest clause learning: DPLL-style
// learn clauses that encode DPLL brandhing
/*
void CDCL_repair_conflict()
{
  clause_t learned_clause;
  model_size_t which_var;

  DEBUG_MSG(fprintf(stderr, "In CDCL_repair_conflict."));
  
  num_conflicts++;
  if (dec_level == 0) CDCL_report_UNSAT();

  // decision level 1 is a special case - no clause actually need be learned
  if (dec_level != 1)
    {
      // construct the learned clause
      learned_clause = clause_init(dec_level);
      for (which_var = 0; which_var < num_vars; which_var++)
	{
	  if((model[which_var].ass_status != AVAILABLE) &&
	     (model[which_var].ass_type == DEC_ASS))
	    {
	      // put the highest decision level literals first
	      learned_clause.lits[dec_level - model[which_var].dec_level] = 
		(model[which_var].truth_value == POSITIVE) ? 
		get_comp_lit(model + which_var) : model + which_var;
	    }
	}
      DEBUG_MSG(fprintf(stderr, "Learned clause: "));
      DEBUG_MSG(clause_print(&learned_clause));
      DEBUG_MSG(fprintf(stderr, "\n"));
      // watch the highest level literals in the clause
      mutable_push(&(get_comp_lit(learned_clause.lits[0])->watched_lits), &learned_clause);
      mutable_push(&(get_comp_lit(learned_clause.lits[1])->watched_lits), &learned_clause);
      // add clause to the formula
      mutable_push(&learned_cnf, &learned_clause);
    }
  // note that backtracking leaves the head pointing to the last decision assignment.
  // backtrack, and add the negation of the last decision (as PROP_ASS) to the trail
  backtrack(dec_level - 1);
  trail_queue_lit(get_comp_lit(*(trail.head)), dec_level - 1);
}
*/

void CDCL_print()
{
  cnf_print();
  fprintf(stderr, "\n");
  mutable_print_clauses(&learned_cnf);
  print_model();
  print_trail();
}

//  error function implementation
void error(char* message)
{
  fprintf(stderr, "FATAL ERROR: %s.\n", message);
  exit(1);
}
