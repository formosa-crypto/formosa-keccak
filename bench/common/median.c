#ifndef MEDIAN_C
#define MEDIAN_C

#include <inttypes.h>
#include <stdlib.h>
#include <stdio.h>

static void median_fr(uint64_t results[LOOPS])
{
  int op, loop;
  uint64_t min;

  // get min median of LOOP runs
  min = results[0];
    for (loop = 1; loop < LOOPS; loop++)
    { if (min > results[loop])
      { min = results[loop]; } }
    results[0] = min;
}

#endif
