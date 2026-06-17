#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <stdbool.h>
#include <string.h>
#include <assert.h>

//
#define TIMINGS 10000
#define RUNS 20
#define LOOPS 1
#define OP 9

// ////////////////////////////////////////////////////////////////////////////

extern void get_params_ref(uint64_t*);
extern void get_params_avx2x4(uint64_t*);

#define BIT_INTERLEAVE 0
static const uint64_t iotas[] = {
    BIT_INTERLEAVE ? 0x0000000000000001ULL : 0x0000000000000001ULL,
    BIT_INTERLEAVE ? 0x0000008900000000ULL : 0x0000000000008082ULL,
    BIT_INTERLEAVE ? 0x8000008b00000000ULL : 0x800000000000808aULL,
    BIT_INTERLEAVE ? 0x8000808000000000ULL : 0x8000000080008000ULL,
    BIT_INTERLEAVE ? 0x0000008b00000001ULL : 0x000000000000808bULL,
    BIT_INTERLEAVE ? 0x0000800000000001ULL : 0x0000000080000001ULL,
    BIT_INTERLEAVE ? 0x8000808800000001ULL : 0x8000000080008081ULL,
    BIT_INTERLEAVE ? 0x8000008200000001ULL : 0x8000000000008009ULL,
    BIT_INTERLEAVE ? 0x0000000b00000000ULL : 0x000000000000008aULL,
    BIT_INTERLEAVE ? 0x0000000a00000000ULL : 0x0000000000000088ULL,
    BIT_INTERLEAVE ? 0x0000808200000001ULL : 0x0000000080008009ULL,
    BIT_INTERLEAVE ? 0x0000800300000000ULL : 0x000000008000000aULL,
    BIT_INTERLEAVE ? 0x0000808b00000001ULL : 0x000000008000808bULL,
    BIT_INTERLEAVE ? 0x8000000b00000001ULL : 0x800000000000008bULL,
    BIT_INTERLEAVE ? 0x8000008a00000001ULL : 0x8000000000008089ULL,
    BIT_INTERLEAVE ? 0x8000008100000001ULL : 0x8000000000008003ULL,
    BIT_INTERLEAVE ? 0x8000008100000000ULL : 0x8000000000008002ULL,
    BIT_INTERLEAVE ? 0x8000000800000000ULL : 0x8000000000000080ULL,
    BIT_INTERLEAVE ? 0x0000008300000000ULL : 0x000000000000800aULL,
    BIT_INTERLEAVE ? 0x8000800300000000ULL : 0x800000008000000aULL,
    BIT_INTERLEAVE ? 0x8000808800000001ULL : 0x8000000080008081ULL,
    BIT_INTERLEAVE ? 0x8000008800000000ULL : 0x8000000000008080ULL,
    BIT_INTERLEAVE ? 0x0000800000000001ULL : 0x0000000080000001ULL,
    BIT_INTERLEAVE ? 0x8000808200000000ULL : 0x8000000080008008ULL
};

// AVX2x4
typedef uint64_t KeccakState[25];
typedef uint64_t KeccakStateAvx2[28];
typedef uint64_t KeccakStateX4[4*25];

extern void keccakf1600_refopt(KeccakState st);
extern void KeccakF1600_StatePermute(KeccakState st);
extern void sha3_keccak_f1600(KeccakState st, const uint64_t[24]);
extern void testF_bmi1(KeccakState st);
extern void testF_nat(KeccakState st);
extern void testF_ref_opt(KeccakState st);
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

  uint64_t cycles_ref[RUNS];
  uint64_t cycles_bmi1[RUNS];
  uint64_t cycles_nat[RUNS];
  uint64_t cycles_ropt[RUNS];
  uint64_t cycles_avx2[RUNS];
  uint64_t cycles_orig[RUNS];
  uint64_t cycles_alt[RUNS];
  uint64_t cycles_native[RUNS];
  uint64_t cycles_native2[RUNS];

  size_t lenavx2, len, lenref;
  uint64_t *_avx2, *_orig, *_alt, *_native, *_native2, *_ref, *_bmi1, *_nat, *_ropt;
  uint64_t *avx2, *orig, *alt, *native, *native2, *ref, *bmi1, *nat, *ropt;

  lenref = alignedcalloc_step(sizeof(uint64_t) * 25);
  lenavx2 = alignedcalloc_step(sizeof(uint64_t) * 28);
  len = alignedcalloc_step(sizeof(uint64_t) * 4 * 25);

  ref = (uint64_t*) alignedcalloc((uint8_t**)&_ref, lenref);
  bmi1 = (uint64_t*) alignedcalloc((uint8_t**)&_bmi1, lenref);
  nat = (uint64_t*) alignedcalloc((uint8_t**)&_nat, lenref);
  ropt = (uint64_t*) alignedcalloc((uint8_t**)&_ropt, lenref);
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
      
      // ref: 5
      for (i = 0; i < TIMINGS; i++)
      { cycles[i] = cpucycles();
        //sha3_keccak_f1600(ref,iotas);
	KeccakF1600_StatePermute(ref);
      }
      results[5][loop] = cpucycles_median(cycles, TIMINGS);
      
      // bmi1: 6
      for (i = 0; i < TIMINGS; i++)
      { cycles[i] = cpucycles();
        testF_bmi1(bmi1);
      }
      results[6][loop] = cpucycles_median(cycles, TIMINGS);
      
      // nat: 7
      for (i = 0; i < TIMINGS; i++)
      { cycles[i] = cpucycles();
        testF_nat(nat);
      }
      results[7][loop] = cpucycles_median(cycles, TIMINGS);

      // ref_opt: 8
      for (i = 0; i < TIMINGS; i++)
      { cycles[i] = cpucycles();
        keccakf1600_refopt(ropt);
      }
      results[8][loop] = cpucycles_median(cycles, TIMINGS);

    }
    median_fr(results);
    cycles_avx2[run] = results[0][0];
    cycles_orig[run] = results[1][0];
    cycles_alt[run] = results[2][0];
    cycles_native[run] = results[3][0];
    cycles_native2[run] = results[4][0];
    cycles_ref[run] = results[5][0];
    cycles_bmi1[run] = results[6][0];
    cycles_nat[run] = results[7][0];
    cycles_ropt[run] = results[8][0];
  }

  qsort(cycles_avx2,RUNS,sizeof(uint64_t),cmp_uint64);
  qsort(cycles_orig,RUNS,sizeof(uint64_t),cmp_uint64);
  qsort(cycles_alt,RUNS,sizeof(uint64_t),cmp_uint64);
  qsort(cycles_native,RUNS,sizeof(uint64_t),cmp_uint64);
  qsort(cycles_native2,RUNS,sizeof(uint64_t),cmp_uint64);
  qsort(cycles_ref,RUNS,sizeof(uint64_t),cmp_uint64);
  qsort(cycles_bmi1,RUNS,sizeof(uint64_t),cmp_uint64);
  qsort(cycles_nat,RUNS,sizeof(uint64_t),cmp_uint64);
  qsort(cycles_ropt,RUNS,sizeof(uint64_t),cmp_uint64);


  printf("|avx2|orig|alt |nat |nAWS|ref |bmi1|nat |ropt|\n");
  for(run = 0; run < RUNS; run++)
  {
    printf("|%" PRIu64 "|%" PRIu64 "|%" PRIu64 "|%" PRIu64 "|%"  PRIu64 "|%" PRIu64 "|%" PRIu64 "|%"  PRIu64 "|%" PRIu64 "|\n",
      cycles_avx2[run],
      cycles_orig[run],
      cycles_alt[run],
      cycles_native[run],
      cycles_native2[run],
      cycles_ref[run],
      cycles_bmi1[run],
      cycles_nat[run],
      cycles_ropt[run]
    );
  }

  printf("correctness ref_opt vs bmi1: %s\n",
    memcmp(ropt, bmi1, sizeof(uint64_t)*25) ? "MISMATCH" : "OK");
  printf("correctness ref_opt vs ref : %s\n",
    memcmp(ropt, ref, sizeof(uint64_t)*25) ? "MISMATCH" : "OK");

  free(_avx2);
  free(_orig);
  free(_alt);
  free(_native);
  free(_native2);
  free(_ref);
  free(_bmi1);
  free(_nat);
  free(_ropt);

  return 0;
}


int main()
{
  return run_bench();
}


