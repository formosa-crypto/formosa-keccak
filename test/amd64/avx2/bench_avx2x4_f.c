#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <stdbool.h>
#include <string.h>
#include <assert.h>

//
#define TIMINGS 100000
#define RUNS 20
#define LOOPS 1
#define OP 5

// ////////////////////////////////////////////////////////////////////////////

extern void get_params_ref(uint64_t*);
extern void get_params_avx2x4(uint64_t*);


// AVX2x4
typedef uint64_t KeccakState[25];
typedef uint64_t KeccakStateAvx2[28];
typedef uint64_t KeccakStateX4[4*25];

extern void testF_avx2(KeccakStateAvx2 st);
extern void testF_avx2x4_orig(KeccakStateX4 st);
extern void testF_avx2x4_alt(KeccakStateX4 st);
extern void testF_avx2x4_native(KeccakStateX4 st);

#include "constants.h"
extern int keccak_f1600_x4_avx2_asm(uint64_t states[100], const uint64_t rc[24],
                                  const uint64_t rho8[4],
                                  const uint64_t rho56[4]);
                                  
//

//include "cpucycles.c"
#ifndef CPUCYCLES_C
#define CPUCYCLES_C

static inline uint64_t cpucycles(void) {
  uint64_t result;

  __asm__ volatile ("rdtsc; shlq $32,%%rdx; orq %%rdx,%%rax"
    : "=a" (result) : : "%rdx");

  return result;
}

static int cmp_uint64(const void *a, const void *b)
{
  if(*(uint64_t *)a < *(uint64_t *)b){ return -1; }
  if(*(uint64_t *)a > *(uint64_t *)b){ return 1; }
  return 0;
}

static uint64_t median(uint64_t *l, size_t llen)
{
  qsort(l,llen,sizeof(uint64_t),cmp_uint64);

  if(llen%2) return l[llen/2];
  else return (l[llen/2-1]+l[llen/2])/2;
}

static uint64_t cpucycles_median(uint64_t *cycles, size_t timings)
{
  size_t i;
  for (i = 0; i < timings-1; i++)
  { cycles[i] = cycles[i+1] - cycles[i]; }

  return median(cycles, timings-1);
}


#endif

//include "median.c"
#ifndef MEDIAN_C
#define MEDIAN_C

#include <inttypes.h>
#include <stdlib.h>
#include <stdio.h>

static void median_fr(uint64_t results[OP][LOOPS])
{
  int op, loop;
  uint64_t min;

  // get min median of LOOP runs
  for (op = 0; op < OP; op++)
  { min = results[op][0];
    for (loop = 1; loop < LOOPS; loop++)
    { if (min > results[op][loop])
      { min = results[op][loop]; } }
    results[op][0] = min;
  }
}


#endif

//include "alignedcalloc.c"
#ifndef ALIGNEDCALLOC_C
#define ALIGNEDCALLOC_C

#include <stdint.h>
#include <stdlib.h>
//include <error.h>

static size_t alignedcalloc_step(size_t len)
{
  size_t step;
  step = len + (63 & (-len));
  return step;
}

static uint8_t *alignedcalloc(uint8_t** _x, size_t len)
{
  uint8_t* x = (uint8_t*) calloc(1, len + 128);
  if (!x) exit(-1); //error(-1, -1, "out of memory");
  if(_x){ *_x = x; }
  x += 63 & (-(unsigned long) x);
  return x;
}

#endif



int run_bench()
{
  int run, loop, i;
  uint64_t cycles[TIMINGS];
  uint64_t results[OP][LOOPS];

  uint64_t cycles_avx2[RUNS];
  uint64_t cycles_orig[RUNS];
  uint64_t cycles_alt[RUNS];
  uint64_t cycles_native[RUNS];
  uint64_t cycles_native2[RUNS];

  size_t lenavx2, len;
  uint64_t *_avx2, *_orig, *_alt, *_native, *_native2;
  uint64_t *avx2, *orig, *alt, *native, *native2;

  lenavx2 = alignedcalloc_step(sizeof(uint64_t) * 28);
  len = alignedcalloc_step(sizeof(uint64_t) * 4 * 25);

  avx2 = (uint64_t*) alignedcalloc((uint8_t**)&_avx2, lenavx2);
  orig = (uint64_t*) alignedcalloc((uint8_t**)&_orig, len);
  alt = (uint64_t*) alignedcalloc((uint8_t**)&_alt, len);
  native = (uint64_t*) alignedcalloc((uint8_t**)&_native, len);
  native2 = (uint64_t*) alignedcalloc((uint8_t**)&_native2, len);

  for(run = 0; run < RUNS; run++)
  {
    for(loop = 0; loop < LOOPS; loop++)
    {
      // avx2: 0 
      for (i = 0; i < TIMINGS; i++)
      { cycles[i] = cpucycles();
        testF_avx2(avx2); 
      }
      results[0][loop] = cpucycles_median(cycles, TIMINGS);

      // orig: 1 
      for (i = 0; i < TIMINGS; i++)
      { cycles[i] = cpucycles();
        testF_avx2x4_orig(orig); 
      }
      results[1][loop] = cpucycles_median(cycles, TIMINGS);

      // alt: 2
      for (i = 0; i < TIMINGS; i++)
      { cycles[i] = cpucycles();
        testF_avx2x4_alt(alt); 
      }
      results[2][loop] = cpucycles_median(cycles, TIMINGS);

      // native: 3
      for (i = 0; i < TIMINGS; i++)
      { cycles[i] = cpucycles();
        testF_avx2x4_native(native);
      }
      results[3][loop] = cpucycles_median(cycles, TIMINGS);
      
      // native2: 4
      for (i = 0; i < TIMINGS; i++)
      { cycles[i] = cpucycles();
        keccak_f1600_x4_avx2_asm(native2, rc, rho8, rho56);
      }
      results[4][loop] = cpucycles_median(cycles, TIMINGS);
      
    }
    median_fr(results);
    cycles_avx2[run] = results[0][0];
    cycles_orig[run] = results[1][0];
    cycles_alt[run] = results[2][0];
    cycles_native[run] = results[3][0];
    cycles_native2[run] = results[4][0];
  }

  qsort(cycles_avx2,RUNS,sizeof(uint64_t),cmp_uint64);
  qsort(cycles_orig,RUNS,sizeof(uint64_t),cmp_uint64);
  qsort(cycles_alt,RUNS,sizeof(uint64_t),cmp_uint64);
  qsort(cycles_native,RUNS,sizeof(uint64_t),cmp_uint64);
  qsort(cycles_native2,RUNS,sizeof(uint64_t),cmp_uint64);


  printf("|avx2 |orig|alt |nat |nAWS|\n");
  for(run = 0; run < RUNS; run++)
  {
    printf("|%" PRIu64 "|%" PRIu64 "|%" PRIu64 "|%" PRIu64 "|%"  PRIu64 "|\n",
      cycles_avx2[run],
      cycles_orig[run],
      cycles_alt[run],
      cycles_native[run],
      cycles_native2[run]);
  }

  free(_avx2);
  free(_orig);
  free(_alt);
  free(_native);
  free(_native2);

  return 0;
}


int main()
{
  return run_bench();
}


