// CDCL.c
// Joshua Blinkhorn 29.04.2019
// This file is part of CDCL

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
#define UNASSIGNED 0
#define POSITIVE 1
#define NEGATIVE -1

// assignment types
#define DEC_ASS 0
#define PROP_ASS 1
#define CON_ASS 2

// special values
#define NULL_DEC_LEVEL ULONG_MAX - 1
#define MAX_VARS ULONG_MAX / 2

// low level types
typedef unsigned char result_t;
typedef signed char truth_value_t;
typedef unsigned char ass_type_t;
typedef signed long int DIMACS_lit_t;
typedef unsigned long int cnf_size_t;
typedef unsigned long int var_set_size_t; // deprecate
typedef unsigned long int model_size_t; // deprecate
typedef unsigned long int mutable_size_t;
typedef unsigned long int lit_t;
typedef signed long int DIMACS_lit_t;

// stats
clock_t start_time;

// higher level types 

// cls

// a clause is a pointer to a literal. It names an array of literals.
// note that the cls_t typedef is superflous, we could use lit_t* instead, but it
// might be useful if later on we need a more sophisticated clause object

typedef lit_t* cls_t;

// cnf

// a CNF is a struct storing (1) an array of clauses and (2) the size of the array 

typedef struct cnf {
  cls_t* clauses;
  cnf_size_t size;
} cnf_t;

// mutable (array)

// this is an automatically resized array of pointers to lit_t.
// it can be used to store a cnf, or a list of pointers to literals (e.g. the 
// watched literals for a singleton assignment), which can also be thought of
// as a set of unit clauses

// the array becomes twice as large whenever necessary to add an item

typedef struct mutable {
  lit_t** data;
  mutable_size_t size;
  mutable_size_t used;
} mutable_t;

// assignment

// stores various information about a singleton assignment, including
// a list of watched literals

typedef struct ass {
  truth_value_t truth_value;
  dec_level_t dec_level;
  ass_type_t ass_type;
  mutable_t watched_lits;
} ass_t;

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

var_set_size_t num_vars;
var_set_size_t num_asses;
unsigned long num_conflicts = 0;
unsigned long num_decisions = 0;
unsigned long num_unit_props = 0;
unsigned long num_redefinitions = 0;
cnf_t cnf;
mutable_t learned_cnf;
ass_t* model;
trail_t trail;
state_t stat;

// IMPLEMENTATION

void error(char* message);

// LITERAL RELATED FUNCTIONS

lit_t DIMACS_to_lit(DIMACS_lit_t value)
{
  // converts a DIMACS literal into an internal literal
  // internal literals are represented as values from 0 to (2 * num_vars) - 1
  // values from 0 to num_vars - 1 represent positive literals,
  // values from num_vars to (2 * num_vars) - 1 represent negative literals.
  return (lit_t) ((value < 0 ? -1 : 1) * value) - 1 + ((value < 0) * num_vars);
}

DIMACS_lit_t lit_to_DIMACS(lit_t lit)
{
  // converts an internal literal back into a DIMACS literal
  // this should only ever be used for printing literal values
  return (DIMACS_lit_t)((lit % num_vars) + 1) * ((lit < num_vars) ? 1 : -1);
}


truth_value_t lit_truth_value(lit_t* lit)
{
  // determines the truth value of the literal under the current assignment
  return (model + *lit)->truth_value;
}

lit_t ass_to_lit(ass_t* ass)
{
  // determines the literal satisfied by the assignment pointed to by ass
  return (lit_t)(ass - model);
}

lit_t get_comp_lit(lit_t lit)
{
  // returns the complementary literal
  return lit + ((lit < num_vars? 1 : -1) * num_vars);
}

void lit_print(lit_t* lit)
{
  //fprintf(stderr, "%lu", *lit);
  // prints an internal literal in the form of a DIMACS literal
  fprintf(stderr, "%ld", lit_to_DIMACS(*lit));
}

void lit_print_binary(lit_t* lit)
{
  // prints the bitwise encoding of the literal
  size_t which_bit, num_bits;
  
  num_bits = sizeof(*lit) * 8;

  for (which_bit = 0; which_bit < num_bits; which_bit++)
    {
      fprintf(stderr,"%lu", (*lit >> (num_bits - which_bit - 1)) & (lit_t)1);
    }
}

// CLAUSE RELATED FUNCTIONS

cls_t cls_init(lit_t width)
{
  // initialises a clause of size `width'
  // the fist `literal' is the size of the clause 
  cls_t cls;

  if ((cls = (lit_t*)malloc(sizeof(lit_t) * (width + 1))) == NULL)
    error("cannot allocate clause");
  cls[0] = width;

  return cls;
}

char cls_is_unit(cls_t cls)
{
  // returns 1 if the given clause is a unit clause, 0 otherwise
  return (cls[0] == 1) ? 1 : 0;
}

void cls_free(cls_t cls)
{
  free(cls);
}

void cls_print(cls_t cls)
{
  var_set_size_t width = cls[0];
  var_set_size_t which_lit;

  for(which_lit = 1; which_lit <= width; which_lit++)
    {
      lit_print(cls + which_lit);
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
      cls_print(cnf.clauses[which_clause]);
      fprintf(stderr, "\n");
    }
}

// MUTABLE RELATED FUNCTIONS

void mutable_init(mutable_t* mutable)
{
  // allocate memory for data - default size is 1
  if ((mutable->data = (lit_t**)malloc(sizeof(lit_t*))) == NULL)
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
    cls_free(mutable->data[which_clause]);
  free(mutable->data);
}

void mutable_push(mutable_t* mutable, lit_t* datum)
{
  // pushes the datum onto the mutable's data array
  mutable_size_t size;

  if (mutable->used == (size = mutable->size))
    {
      if ((mutable->data = 
	   (lit_t**)realloc(mutable->data, 2 * size * sizeof(lit_t*))) == NULL)
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
  lit_t** data;
  
  fprintf(stderr, "LEARNED CLAUSES:\n");
  fprintf(stderr, "size: %lu, used: %lu\n", mutable->size, mutable->used);

  num_clauses = mutable->used;
  data = mutable->data;
  for(which_clause = 0; which_clause < num_clauses; which_clause++)
    {
      cls_print(data[which_clause]);
      fprintf(stderr, "\n");
    }
}

// use to print a watched literal list
void mutable_print_lits(mutable_t* mutable)
{
  mutable_size_t which_lit, num_lits;
  lit_t** data;
  
  fprintf(stderr, "size: %lu, used: %lu, literals:", mutable->size, mutable->used);

  num_lits = mutable->used;
  data = mutable->data;
  for(which_lit = 0; which_lit < num_lits; which_lit++)
    {
      lit_print(data[which_lit]);
    }
  fprintf(stderr, "\n");
}

void print_watched_lits()
{
  model_size_t which_ass;

  fprintf(stderr, "WATCHED LITERALS\n");
  for (which_ass = 0; which_ass < num_asses; which_ass++)
    {
      mutable_print_lits(&(model[which_ass].watched_lits));
    }
  fprintf(stderr, "\n");
}

// ASSIGNMENT RELATED FUNCTIONS

void assign_by_lit(lit_t lit)
{
  // overwrites the assignment satisfying the literal into the model
  // the assignment type should already have been set when the literal
  // was added to the trail
  lit_t comp_lit = get_comp_lit(lit);

  model[lit].truth_value = POSITIVE;
  model[lit].dec_level = dec_level;
  model[comp_lit].truth_value = NEGATIVE;
  model[comp_lit].dec_level = dec_level;
}

void unassign_by_lit(lit_t lit)
{
  // unassigns the variable for this literal (i.e. for the literal and its complement)
  // 
  lit_t comp_lit = get_comp_lit(lit);

  model[lit].truth_value = UNASSIGNED;
  model[comp_lit].truth_value = UNASSIGNED;
}

// prints the value of an assignment and its decision level
void ass_print(ass_t* ass)
{
  dec_level_t dec_level = ass->dec_level;

  if(ass->truth_value == UNASSIGNED)
    fprintf(stderr, "0 ");
  else
    {
      fprintf(stderr, "%2d / %ld ", ass->truth_value,
	      dec_level == NULL_DEC_LEVEL ? -1L : (long)dec_level);
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
    }
}

// this function assumes trail.head > trail.sequence
void backtrack(dec_level_t new_dec_level)
{  
  DEBUG_MSG(fprintf(stderr,
		    "In backtrack(). Backtracking to decision level %lu.\n",
		    new_dec_level));
  // go backwards through the trail and delete the assignments
  while((trail.head >= trail.sequence) && ((*(trail.head))->dec_level > new_dec_level))
    {
      unassign_by_lit(*trail.head - model);
      trail.head--;
    }
  trail.head++;
  trail.tail = trail.head;
  //revert to given decision level
  dec_level = new_dec_level;
}

// MODEL RELATED FUNCTIONS

// prints the contents of the given model
void print_model()
{
  var_set_size_t which_var;

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

void trail_add_ass(ass_t* ass)
{
  *(trail.tail) = ass;
  trail.tail++;
}

void trail_add_lit(lit_t lit, ass_type_t ass_type)
{
  model[lit].ass_type = ass_type;
  model[get_comp_lit(lit)].ass_type = ass_type;
  *(trail.tail) = model + lit;
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
      fprintf(stderr, "%lu: %ld ",
	      temp_pointer - trail.sequence + 1,
	      lit_to_DIMACS(*temp_pointer - model));
      if ((*temp_pointer)->truth_value == UNASSIGNED)
	fprintf(stderr, "U ");
      else switch((*temp_pointer)->ass_type)
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
      if (temp_pointer == trail.head) fprintf(stderr, "HEAD");
      if (temp_pointer == trail.tail) fprintf(stderr, "TAIL");
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
  var_set_size_t width; 
  var_set_size_t which_lit; 
  var_set_size_t which_ass; 
  cnf_size_t which_clause;
  cls_t cls;

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
      model[which_ass].truth_value = UNASSIGNED; 
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

  // initialise cnf
  if ((cnf.clauses = (cls_t*)malloc(sizeof(cls_t) * cnf.size)) == NULL)
	error("cannot allocate cnf clauses");

  // allocate clauses and add to formula
  for(which_clause = 0; which_clause < cnf.size; which_clause++)
    {
      // find width of clause with cursor
      fscanf(cursor, "%ld", &DIMACS_lit);
      for(width = 0; DIMACS_lit != 0; width++) fscanf(cursor, "%ld", &DIMACS_lit);

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
	  trail_add_lit(DIMACS_to_lit(DIMACS_lit), PROP_ASS);
	  fscanf(input, "%ld", &DIMACS_lit);
	  state = PROPAGATE;
	  // we do not store unit clauses, so decrement counters
	  cnf.size--;
	  which_clause--;
	}
      else 
	{
	  // initialise clause
	  cls = cls_init(width);
	  // set liqterals with input
	  which_lit = 1;
	  fscanf(input, "%ld", &DIMACS_lit);
	  while(DIMACS_lit != 0) 
	    {
	      cls[which_lit] = DIMACS_to_lit(DIMACS_lit);
	      fscanf(input, "%ld", &DIMACS_lit);
	      which_lit++;
	    }
	  
	  // put the clause into the cnf
	  cnf.clauses[which_clause] = cls;
	  
	  // watch the first two literals
	  mutable_push(&(model[get_comp_lit(cls[1])].watched_lits), cls);
	  mutable_push(&(model[get_comp_lit(cls[2])].watched_lits), cls);
	}
    }
  // set default decision level
  dec_level = 0;
  // initialise empty learned clause list
  mutable_init(&(learned_cnf));
}

void CDCL_free()
{
  cnf_size_t which_clause;
  var_set_size_t which_ass;

  // free memory for the cnf
  for (which_clause = 0; which_clause < cnf.size; which_clause++)
    cls_free(cnf.clauses[which_clause]);
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

  lit_t* watched_lit, *other_watched_lit, *candidate_lit;
  lit_t temp_lit;
  var_set_size_t which_lit;
  cls_t clause;
  cnf_size_t num_clauses, which_clause;
  mutable_t new_watchers;
  model_size_t propagator, width;
  ass_t** temp_head;
  lit_t** data;
  //ass_t* ass;

  DEBUG_MSG(fprintf(stderr, "In CDCL_prop()..\n"));
  
  while (trail.head != trail.tail)
    {
      // store the literal that we are propagating
      propagator = *(trail.head) - model;
      
      // add the propagating assignment to the model, set all successive additions
      // as propagations
      assign_by_lit(propagator);
      
      // fetch a pointer to the list of watched literals, and its size 
      data = model[propagator].watched_lits.data;
      num_clauses = model[propagator].watched_lits.used;

      // initialise a new mutable for the replacement list
      mutable_init(&new_watchers);

      DEBUG_MSG(fprintf(stderr, "Propagating literal %ld on %lu clauses\n",
			lit_to_DIMACS(propagator), num_clauses));
      DEBUG_MSG(print_model());
      DEBUG_MSG(print_trail());
      DEBUG_MSG(print_watched_lits());
      
      // cycle through the watched literals' clauses
      for (which_clause = 0; which_clause < num_clauses; which_clause++)
	{
	  // get the current clause and its width
	  clause = data[which_clause];
	  width = *clause;

	  DEBUG_MSG(fprintf(stderr, "Dealing with clause: "));
	  DEBUG_MSG(cls_print(clause));

	  // get pointers to the watched literal being processed,
	  // the other watched literal, and the first candidate literal
	  if (clause[1] == get_comp_lit(propagator))
	    {
	      watched_lit = clause + 1;
	      other_watched_lit = clause + 2;
	    }
	  else
	    {
	      watched_lit = clause + 2;
	      other_watched_lit = clause + 1;
	    }

	  // if the other watched literal is satisfied, we leave the clause as it is
	  if (lit_truth_value(other_watched_lit) == POSITIVE)  
	    {
	      // so the watched literal goes onto the replacement list
	      mutable_push(&new_watchers, clause);

	      DEBUG_MSG(fprintf(stderr, " -> "));
	      DEBUG_MSG(cls_print(clause));
	      DEBUG_MSG(fprintf(stderr, 
				" (no change - other watched literal is satisfied)\n"));
	    }
	  else
	    {
	      // cycle through the remaining candidate literals 
	      for(which_lit = 3; which_lit <= width; which_lit++)
		{
		  candidate_lit = clause + which_lit;
		  if (lit_truth_value(candidate_lit) != NEGATIVE)
		    {
		      // we found an eligible literal
		      // swap it for the original watched literal
		      temp_lit = *candidate_lit;
		      *candidate_lit = *watched_lit;
		      *watched_lit = temp_lit;
		      // add it to the appropriate list
		      mutable_push(&(model[get_comp_lit(*watched_lit)].watched_lits),
				   clause);

		      DEBUG_MSG(fprintf(stderr, " -> "));
		      DEBUG_MSG(cls_print(clause));
		      DEBUG_MSG(fprintf(stderr, "\n"));
		      
		      // force inner loop to terminate
		      break;
		    }
		}
	      if (which_lit > width)
		{
		  // we have a unit clause based on the other watched literal
		  DEBUG_MSG(fprintf(stderr, "found unit clause %ld",
				    lit_to_DIMACS(*other_watched_lit)));
		  num_unit_props++;
		  // the watched literal should be placed on the replacement list
		  mutable_push(&new_watchers, clause);  

		  // the implied assignment is not in the model, nor is its negation
		  // but either may be on the trail
		  // cycle through the trail
		  for (temp_head = trail.sequence; temp_head < trail.tail; temp_head++)
		    {
		      if (*other_watched_lit == *temp_head - model)
			{ // the implied assignment is already on the trail
			  DEBUG_MSG(fprintf(stderr,
					    " -- ignoring repeated unit clause.\n"));			  
			  break;
			}
		      if (*other_watched_lit == get_comp_lit(*temp_head - model))
			// the implied assignment yields a conflict
			{
			  DEBUG_MSG(fprintf(stderr,
					    " -- detected conflict - aborting propagation.\n"));
			  // add clauses for unprocessed watched literals to replacement
			  // list
			  for (which_clause++; which_clause < num_clauses; which_clause++)
			      mutable_push(&new_watchers, data[which_clause]);
			  // free the old data and instate the new list
			  mutable_free(&(model[propagator].watched_lits));
			  model[propagator].watched_lits = new_watchers;
			  return CONFLICT;
			}
		    }
		  if (temp_head == trail.tail)
		    {
		      // add unit assignment to trail
		      trail_add_lit(*other_watched_lit, PROP_ASS);
		      DEBUG_MSG(fprintf(stderr,
					" -- added to trail.\n"));

		    }
		}
	    }
	}
      // propagation for this assignment has completed without conflict
      // instate new watched lits      
      mutable_free(&(model[propagator].watched_lits));
      model[propagator].watched_lits = new_watchers;

      // increment head
      trail.head++;
      DEBUG_MSG(fprintf(stderr,
			"Completed propagation on literal %ld without conflict\n",
			lit_to_DIMACS(propagator)));
    }

  // propagation terminates without a conflict
  DEBUG_MSG(fprintf(stderr,"Propagation cycle complete.\n"));
  return DECIDE;
}
		  
// easy decision heuristic: assigns the first unassigned variable positively 
// trail.head and trail.tail are always equal when CDCL_decide() is called
// and point to the location after the final assignment
// if the function returns PROPAGATE, trail.head points to the location of
// the final assignment, trail.tail to the next location.  
int CDCL_decide()
{
  model_size_t which_ass;

  DEBUG_MSG(fprintf(stderr, "In CDCL_decide(). "));
  num_decisions++;

  // find an unassigned var
  for (which_ass = 0; which_ass < num_vars; which_ass++)
    {
      if(model[which_ass].truth_value == UNASSIGNED)
	{
	  // set assignment type
	  model[which_ass].ass_type = DEC_ASS;
	  model[which_ass + num_vars].ass_type = DEC_ASS;
	  // put the assignment on the trail
	  trail_add_lit(which_ass, DEC_ASS);
	  // update decision level
	  dec_level++;

	  DEBUG_MSG(fprintf(stderr, "Made decision %lu.\n",
			    lit_to_DIMACS(which_ass)));
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
void CDCL_repair_conflict()
{
  cls_t learned_cls;
  model_size_t which_var;

  DEBUG_MSG(fprintf(stderr, "In CDCL_repair_conflict."));
  
  num_conflicts++;
  if (dec_level == 0) CDCL_report_UNSAT();

  // decision level 1 is a special case - no clause actually need be learned
  if (dec_level != 1)
    {
      // construct the learned clause
      learned_cls = cls_init(dec_level);
      for (which_var = 0; which_var < num_vars; which_var++)
	{
	  if((model[which_var].truth_value != UNASSIGNED) &&
	     (model[which_var].ass_type == DEC_ASS))
	    {
	      // put the highest decision level literals first
	      learned_cls[dec_level - model[which_var].dec_level + 1] = 
		(model[which_var].truth_value == POSITIVE) ? 
		get_comp_lit(which_var) : which_var;
	    }
	}
      DEBUG_MSG(fprintf(stderr, "Learned clause: "));
      DEBUG_MSG(cls_print(learned_cls));
      DEBUG_MSG(fprintf(stderr, "\n"));
      // watch the highest level literals in the clause
      mutable_push(&(model[get_comp_lit(learned_cls[1])].watched_lits), learned_cls);
      mutable_push(&(model[get_comp_lit(learned_cls[2])].watched_lits), learned_cls);
      // add clause to the formula
      mutable_push(&learned_cnf, learned_cls);
    }
  // note that backtracking leaves the head pointing to the last decision assignment.
  // backtrack, and add the negation of the last decision (as PROP_ASS) to the trail
  backtrack(dec_level - 1);
  trail_add_lit(get_comp_lit(*(trail.head) - model), CON_ASS);
}

void CDCL_print()
{
  cnf_print();
  fprintf(stderr, "\n");
  mutable_print_clauses(&learned_cnf);
  print_model();
  print_trail();
  // print_watched_lits();
}

//  error function implementation
void error(char* message)
{
  fprintf(stderr, "FATAL ERROR: %s.\n", message);
  exit(1);
}
