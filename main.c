// main.c
// Joshua Blinkhorn 29.04.2019
// This file is part of CDCL

#include <stdio.h>
#include <stdlib.h>
#include "CDCL.h"

int main(int argc, char** argv)
{  
  CDCL_init(argv[1]);

  CDCL_print();

  if(state == PROPAGATE)
    CDCL_prop();

  while(CDCL_decide() != SUCCESS)
    {
      while (CDCL_prop() == CONFLICT)
	{
	  CDCL_repair_conflict();	    
	}
    }
  CDCL_report_SAT();
  // CDCL_free(); not needed as the previous line exits
  return 0;
}
