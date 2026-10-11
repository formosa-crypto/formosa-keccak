#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <stdbool.h>
#include <string.h>
#include <assert.h>



// State types
typedef uint64_t KeccakState[25] __attribute__((aligned(32)));
typedef uint64_t KeccakStateAvx2[28] __attribute__((aligned(32)));
typedef uint64_t KeccakStateX4[4*25] __attribute__((aligned(32)));

// Initialize a state array with the sequence 0, 1, 2, ...
#define INIT_STATE(s) \
  for (int i = 0; i < sizeof(s)/sizeof((s)[0]); i++) (s)[i] = (i)

// Apply INIT_STATE to each argument: INIT_STATES(s0, s1, s2);
#define FE_1(x)       INIT_STATE(x)
#define FE_2(x, ...)  INIT_STATE(x); FE_1(__VA_ARGS__)
#define FE_3(x, ...)  INIT_STATE(x); FE_2(__VA_ARGS__)
#define FE_4(x, ...)  INIT_STATE(x); FE_3(__VA_ARGS__)
#define FE_5(x, ...)  INIT_STATE(x); FE_4(__VA_ARGS__)
#define FE_6(x, ...)  INIT_STATE(x); FE_5(__VA_ARGS__)
#define FE_7(x, ...)  INIT_STATE(x); FE_6(__VA_ARGS__)
#define FE_8(x, ...)  INIT_STATE(x); FE_7(__VA_ARGS__)
#define FE_9(x, ...)  INIT_STATE(x); FE_8(__VA_ARGS__)
#define FE_10(x, ...) INIT_STATE(x); FE_9(__VA_ARGS__)
#define FE_11(x, ...) INIT_STATE(x); FE_10(__VA_ARGS__)
#define FE_12(x, ...) INIT_STATE(x); FE_11(__VA_ARGS__)
#define FE_13(x, ...) INIT_STATE(x); FE_12(__VA_ARGS__)

#define FE_NTH(_1,_2,_3,_4,_5,_6,_7,_8,_9,_10,_11,_12,_13,N,...) N
#define INIT_STATES(...) \
  FE_NTH(__VA_ARGS__, FE_13,FE_12,FE_11,FE_10,FE_9,FE_8,FE_7,FE_6,FE_5,FE_4,FE_3,FE_2,FE_1)(__VA_ARGS__)

// Time TIMINGS runs of a permutation call and store its median in results[idx].
// The call is variadic so its own argument commas are preserved.
#define BENCH_OP(idx, ...) \
  do { \
    for (i = 0; i < TIMINGS; i++) \
    { cycles[i] = cpucycles(); \
      __VA_ARGS__; \
    } \
    results[idx][loop] = cpucycles_median(cycles, TIMINGS); \
  } while (0)

// Jasmin entry-points
/* 0 */ extern void keccakf1600(KeccakState st);
/* 1 */ extern void keccakf1600_ref(KeccakState st);
/* 2 */ extern void keccakf1600_opt(KeccakState st);
/* 3 */ extern void keccakf1600_basic(KeccakState st);
/* 4 */ extern void keccakf1600_avx2(KeccakState st);
/* 5 */ extern void keccakf1600x1_avx2(KeccakStateAvx2 st);
/* 6 */ extern void keccakf1600x4(KeccakStateX4 st);
/* 7 */ extern void keccakf1600x4_ref(KeccakStateX4 st);
/* 8 */ extern void keccakf1600x4_alt(KeccakStateX4 st);
/* 9 */ extern void keccakf1600x4_nat(KeccakStateX4 st);

// External entry-points
/* 10 */ extern void KeccakF1600_StatePermute(KeccakState st);
/* 11 */ extern void sha3_keccak_f1600(KeccakState st, const uint64_t[24]);
#include "constants.h"
/* 12 */ extern int keccak_f1600_x4_avx2_asm(KeccakStateX4 states, const uint64_t rc[24],
                                    const uint64_t rho8[4],
                                    const uint64_t rho56[4]);
                             
//



//
#define TIMINGS 1000
#define RUNS 20
#define LOOPS 1
#define OP 13



// ////////////////////////////////////////////////////////////////////////////


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

  uint64_t cycles_ops[OP][RUNS];

  KeccakState s0, s1, s2, s3, s4;
  KeccakStateAvx2 s5;
  KeccakStateX4 s6, s7, s8, s9;
  KeccakState s10, s11;
  KeccakStateX4 s12;

  INIT_STATES(s0,s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12);

  for(run = 0; run < RUNS; run++)
  {
    for(loop = 0; loop < LOOPS; loop++)
    {
      BENCH_OP(0, keccakf1600(s0) );
      BENCH_OP(1, keccakf1600_ref(s1) );
      BENCH_OP(2, keccakf1600_opt(s2) );
      BENCH_OP(3, keccakf1600_basic(s3) );
      BENCH_OP(4, keccakf1600_avx2(s4) );
      BENCH_OP(5, keccakf1600x1_avx2(s5) );
      BENCH_OP(6, keccakf1600x4(s6) );
      BENCH_OP(7, keccakf1600x4_ref(s7) );
      BENCH_OP(8, keccakf1600x4_alt(s8) );
      BENCH_OP(9, keccakf1600x4_nat(s9) );
      BENCH_OP(10, KeccakF1600_StatePermute(s10) );
      BENCH_OP(11, sha3_keccak_f1600(s11,iotas) );
      BENCH_OP(12, keccak_f1600_x4_avx2_asm(s12,rc,rho8,rho56) );
    }
    median_fr(results);
    for (int op = 0; op < OP; op++)
      cycles_ops[op][run] = results[op][0];
  }

  for (int op = 0; op < OP; op++)
    qsort(cycles_ops[op],RUNS,sizeof(uint64_t),cmp_uint64);

  printf("KeccakF[1600] timings:\n");
  printf("======================\n");
  printf(" legend:  dflt - Jasmin Keccak defaults\n");
  printf("          ref  - Jasmin reference\n");
  printf("          opt  - Jasmin optimised\n");
  printf("          bas  - Jasmin basic\n");
  printf("          avx2 - Jasmin avx2 (st25)\n");
  printf("          stav - Jasmin (pure) avx2\n");
  printf("          xkcp - XKCP clang-22 -O3\n");
  printf("          s2n  - AWS's s2n-bignum \n\n");
  printf(" |dflt| ref| opt| bas|avx2|stav|xkcp| s2n|\n");
  for(run = 0; run < RUNS; run++)
  {
    printf(" |%4" PRIu64 "|%4" PRIu64 "|%4"      PRIu64 "|%4" PRIu64 "|%4"  PRIu64 "|%4" PRIu64 "|%4" PRIu64 "|%4"  PRIu64 "|\n",
      cycles_ops[0][run],
      cycles_ops[1][run],
      cycles_ops[2][run],
      cycles_ops[3][run],
      cycles_ops[4][run],
      cycles_ops[5][run],
      cycles_ops[10][run],
      cycles_ops[11][run]
    );
  }

  printf("\ncorrectness vs ref: %s %s %s %s %s %s %s\n\n",
    (memcmp(s1, s0, sizeof(s1)) ? "MISMATCH" : "OK"),
    (memcmp(s1, s2, sizeof(s1)) ? "MISMATCH" : "OK"),
    (memcmp(s1, s3, sizeof(s1)) ? "MISMATCH" : "OK"),
    (memcmp(s1, s4, sizeof(s1)) ? "MISMATCH" : "OK"),
    ("NA"),
    (memcmp(s1, s10, sizeof(s1)) ? "MISMATCH" : "OK"),
    (memcmp(s1, s11, sizeof(s1)) ? "MISMATCH" : "OK")
    );

  printf("KeccakF[1600]x4 timings:\n");
  printf("======================\n");
  printf(" legend:  dflt - Jasmin Keccak defaults\n");
  printf("          ref  - Jasmin reference\n");
  printf("          alt  - Jasmin alternative\n");
  printf("          nat  - Jasmin native port\n");
  printf("          aws  - AWS's optimized\n\n");
  printf(" |dflt| ref| alt| nat| aws|\n");
  for(run = 0; run < RUNS; run++)
  {
    printf(" |%" PRIu64 "|%" PRIu64 "|%" PRIu64 "|%" PRIu64 "|%" PRIu64 "|\n",
      cycles_ops[6][run],
      cycles_ops[7][run],
      cycles_ops[8][run],
      cycles_ops[9][run],
      cycles_ops[12][run]
    );
  }

  printf("\ncorrectness vs ref: %s %s %s %s \n\n",
    (memcmp(s7, s6, sizeof(s1)) ? "MISMATCH" : "OK"),
    (memcmp(s7, s8, sizeof(s1)) ? "MISMATCH" : "OK"),
    (memcmp(s7, s9, sizeof(s1)) ? "MISMATCH" : "OK"),
    (memcmp(s7, s12, sizeof(s1)) ? "MISMATCH" : "OK")
    );

  return 0;
}


int main()
{
  return run_bench();
}


