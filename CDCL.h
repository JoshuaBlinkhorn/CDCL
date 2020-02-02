// CDCL.h
// Joshua Blinkhorn 29.04.2019
// This file is part of CDCL

// CDCL INTERFACE

void CDCL_init(char* DIMACS_filename);
// initialises the solver into default state based on the given DIMACS file

void CDCL_free();
// deallocates all memory allocated during the CDCL process

void CDCL_prop();
// looks for unit clauses under the assignment in the solver's model, and adds 
// them to the model and trail, until none remain

void CDCL_decide();
// looks for a single unit clause, and returns the first it finds, or NULL if
// none is to be found

void CDCL_print();
// learns a clause after conflict, currently this is just the negation of the decision
// assignment

