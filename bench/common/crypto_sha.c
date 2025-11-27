#include "api.h"
#include "namespace.h"

#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <assert.h>

//

#define crypto_sha3_256 NAMESPACE_LC(sha3_256)
#define crypto_shake256 NAMESPACE_LC(shake256)
#define crypto_shake256x4 NAMESPACE_LC(shake256x4)
#define OP 3


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
  uint64_t results[OP][LOOPS];

  uint64_t cycles_sha[RUNS];
  uint64_t cycles_shake[RUNS];
  uint64_t cycles_shakex4[RUNS];

  uint8_t *_ps32, *ps32, *p32;
  uint8_t *_ps1184, *ps1184, *p1184;
  uint8_t *_ps128_0, *ps128_0, *p128_0;
  uint8_t *_ps128_1, *ps128_1, *p128_1;
  uint8_t *_ps128_2, *ps128_2, *p128_2;
  uint8_t *_ps128_3, *ps128_3, *p128_3;
  uint8_t *_ps1, *ps1, *p1;
  uint8_t *_ps4, *ps4, *p4;

  size_t len_1184, len_32, len_128, len_1, len_4;

  len_1184 = alignedcalloc_step(1184);
  len_32 = alignedcalloc_step(32);
  len_128 = alignedcalloc_step(128);
  len_1 = alignedcalloc_step(1);
  len_4 = alignedcalloc_step(4);

  ps32 = alignedcalloc(&_ps32, len_32 * TIMINGS);
  ps1184 = alignedcalloc(&_ps1184, len_1184 * TIMINGS);
  ps128_0 = alignedcalloc(&_ps128_0, len_128 * TIMINGS);
  ps128_1 = alignedcalloc(&_ps128_1, len_128 * TIMINGS);
  ps128_2 = alignedcalloc(&_ps128_2, len_128 * TIMINGS);
  ps128_3 = alignedcalloc(&_ps128_3, len_128 * TIMINGS);
  ps1 = alignedcalloc(&_ps1, len_1 * TIMINGS);
  ps4 = alignedcalloc(&_ps4, len_4 * TIMINGS);

  for(run = 0; run < RUNS; run++)
  {
    for(loop = 0; loop < LOOPS; loop++)
    {
      p1184 = ps1184; p32 = ps32;
      for (i = 0; i < TIMINGS; i++, p1184 += len_1184, p32 += len_32)
      { cycles[i] = cpucycles();
        crypto_sha3_256(p32,p1184); 
      }
      results[0][loop] = cpucycles_median(cycles, TIMINGS);

      p128_0 = ps128_0; p1 = ps1; p32 = ps32;
      for (i = 0; i < TIMINGS; i++, p1 += len_1, p32 += len_32, p128_0 += len_128)
      { cycles[i] = cpucycles();
        crypto_shake256(p128_0,p32,p1); 
      }
      results[1][loop] = cpucycles_median(cycles, TIMINGS);

      p128_0 = ps128_0; p128_1 = ps128_1; p128_2 = ps128_2; p128_3 = ps128_3; p4 = ps4; p32 = ps32;
      for (i = 0; i < TIMINGS; i++, p4 += len_4, p32 += len_32, p128_0 += len_128, p128_1 += len_128, p128_2 += len_128, p128_3 += len_128)
      { cycles[i] = cpucycles();

        crypto_shake256x4(p128_0,p128_1,p128_2,p128_3,p32,p4);
      }
      results[2][loop] = cpucycles_median(cycles, TIMINGS);
    }
    median_fr(results);
    cycles_sha[run] = results[0][0];
    cycles_shake[run] = results[1][0];
    cycles_shakex4[run] = results[2][0];
  }

  qsort(cycles_sha,RUNS,sizeof(uint64_t),cmp_uint64);
  qsort(cycles_shake,RUNS,sizeof(uint64_t),cmp_uint64);
  qsort(cycles_shakex4,RUNS,sizeof(uint64_t),cmp_uint64);


   for(run = 0; run < RUNS; run++)
  {
    printf("|%" PRIu64 "|%" PRIu64 "|%"  PRIu64 "|\n",
      cycles_sha[run],
      cycles_shake[run],
      cycles_shakex4[run]);
  }


  free(_ps32);
  free(_ps1184);
  free(_ps128_0);
  free(_ps128_1);
  free(_ps128_2);
  free(_ps128_3);
  free(_ps1);
  free(_ps4);


  return 0;
}

