// main.c
// Joshua Blinkhorn 29.04.2019
// This file is part of CDCL

#include <stdio.h>
#include <stdlib.h>
#include "CDCL.h"

int main(int argc, char** argv)
{  
  CDCL_init(argv[1]);
  while(1)
    {
      CDCL_prop();
      CDCL_decide();
    }
  return 0;
}
