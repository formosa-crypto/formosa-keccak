// Focused benchmark: C-ref (clang) vs Jasmin bmi1 / ref_opt / ref_opt2.
// Excludes the (flaky) native variant so the unit builds reliably with
// -auto-spill-all.  See Makefile target bench_opt2.
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <inttypes.h>

#define TIMINGS 10000
#define RUNS 20
#define OP 4

typedef uint64_t KeccakState[25];

extern void KeccakF1600_StatePermute(KeccakState st); // clang C, from fips202.s
extern void testF_bmi1(KeccakState st);
extern void testF_ref_opt(KeccakState st);
extern void testF_ref_opt2(KeccakState st);

static inline uint64_t cpucycles(void) {
  uint64_t r;
  __asm__ volatile ("rdtsc; shlq $32,%%rdx; orq %%rdx,%%rax" : "=a"(r) : : "%rdx");
  return r;
}
static int cmp_u64(const void *a, const void *b) {
  uint64_t x = *(const uint64_t*)a, y = *(const uint64_t*)b;
  return (x > y) - (x < y);
}
static uint64_t median(uint64_t *l, size_t n) {
  qsort(l, n, sizeof(uint64_t), cmp_u64);
  return n % 2 ? l[n/2] : (l[n/2-1] + l[n/2]) / 2;
}
static uint64_t cpucycles_median(uint64_t *c, size_t n) {
  for (size_t i = 0; i < n - 1; i++) c[i] = c[i+1] - c[i];
  return median(c, n - 1);
}

int main(void) {
  uint64_t cycles[TIMINGS];
  uint64_t res[OP][RUNS];
  _Alignas(64) KeccakState ref = {0}, bmi1 = {0}, o1 = {0}, o2 = {0};

  for (int run = 0; run < RUNS; run++) {
    for (int i = 0; i < TIMINGS; i++) { cycles[i] = cpucycles(); KeccakF1600_StatePermute(ref); }
    res[0][run] = cpucycles_median(cycles, TIMINGS);
    for (int i = 0; i < TIMINGS; i++) { cycles[i] = cpucycles(); testF_bmi1(bmi1); }
    res[1][run] = cpucycles_median(cycles, TIMINGS);
    for (int i = 0; i < TIMINGS; i++) { cycles[i] = cpucycles(); testF_ref_opt(o1); }
    res[2][run] = cpucycles_median(cycles, TIMINGS);
    for (int i = 0; i < TIMINGS; i++) { cycles[i] = cpucycles(); testF_ref_opt2(o2); }
    res[3][run] = cpucycles_median(cycles, TIMINGS);
  }

  for (int op = 0; op < OP; op++) qsort(res[op], RUNS, sizeof(uint64_t), cmp_u64);

  printf("| Cref | bmi1 | ropt | ropt2|\n");
  for (int run = 0; run < RUNS; run++)
    printf("|%6"PRIu64"|%6"PRIu64"|%6"PRIu64"|%6"PRIu64"|\n",
           res[0][run], res[1][run], res[2][run], res[3][run]);

  printf("\ncorrectness (all permuted %d times from zero state):\n", TIMINGS*RUNS);
  printf("  ref_opt  vs bmi1 : %s\n", memcmp(o1, bmi1, sizeof(KeccakState)) ? "MISMATCH" : "OK");
  printf("  ref_opt2 vs bmi1 : %s\n", memcmp(o2, bmi1, sizeof(KeccakState)) ? "MISMATCH" : "OK");
  printf("  ref_opt2 vs Cref : %s\n", memcmp(o2, ref,  sizeof(KeccakState)) ? "MISMATCH" : "OK");
  return 0;
}
