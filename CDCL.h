// CDCL.h
// Joshua Blinkhorn 29.04.2019
// This file is part of CDCL

// CDCL INTERFACE

// states
#define CONFLICT 0
#define DECIDE 1
#define PROPAGATE 2
#define SUCCESS 3

typedef unsigned char state_t;
state_t state;

// the current decision level is global
typedef unsigned long int dec_level_t;

// initialises the solver into default state based on the given DIMACS file
void CDCL_init(char* DIMACS_filename);
// deallocates all memory allocated during the CDCL process
void CDCL_free();
// looks for unit clauses under the assignment in the solver's model, and adds 
// them to the model and trail, until none remain
state_t CDCL_prop();
// looks for a single unit clause, and returns the fist it finds, or NULL if
// none is to be found
char CDCL_decide();
// learns a clause after conflict, currently this is just the negation of the decision
// assignment
void CDCL_repair_conflict();
// prints the entire contents of the solver
void CDCL_print();
// carries out the solver's final task
void CDCL_report_SAT(); //M?
void CDCL_report_UNSAT(); //M
