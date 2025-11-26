#include "api.h"
#include "namespace.h"

#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <assert.h>

//

#define crypto_sha3_256 NAMESPACE_LC(sha3_256)


//

#include "config.h"
#include "cpucycles.c"
#include "median.c"
#include "alignedcalloc.c"

//

int main(int argc, char**argv)
{
  int run, loop, i;
  uint64_t cycles[TIMINGS];
  uint64_t results[LOOPS];

  uint64_t cycles_sha[RUNS];

  uint8_t *_ins, *ins, *in;
  uint8_t *_os, *os, *o;
  size_t ilen, olen;

  ilen = alignedcalloc_step(1184);
  olen = alignedcalloc_step(32);

  ins = alignedcalloc(&_ins, ilen * TIMINGS);
  os = alignedcalloc(&_os, olen * TIMINGS);

  for(run = 0; run < RUNS; run++)
  {
    for(loop = 0; loop < LOOPS; loop++)
    {
        in = ins; o = os;
      for (i = 0; i < TIMINGS; i++, in += ilen, o += olen)
      { cycles[i] = cpucycles();
        crypto_sha3_256(o,in); 
      }
      results[loop] = cpucycles_median(cycles, TIMINGS);

    }
    median_fr(results);
    cycles_sha[run] = results[0];
  }

  qsort(cycles_sha,RUNS,sizeof(uint64_t),cmp_uint64);

  for(run = 0; run < RUNS; run++)
  {
    printf("|%" PRIu64 "|\n",
      cycles_sha[run]);
  }

  free(_ins);
  free(_os);


  return 0;
}

