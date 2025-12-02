#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <stdbool.h>


#define RUNS 10          
#define LOOPS 5        
#define TIMINGS 1000     
#define OP 6             

#define LEN_KECCAK 800 


#include "../../common/cpucycles.c"
#include "../../common/median.c"
#include "../../common/alignedcalloc.c"


extern void get_params_avx2x4(uint64_t*);

// AVX2x4
typedef uint64_t KeccakState[25];
typedef uint64_t KeccakStateX4[4*25];

extern void init_state_avx2x4(uint8_t* st);
extern void TEST_ONESHOT__absorb_avx2x4(uint8_t* st, const uint8_t buf0[], const uint8_t buf1[], const uint8_t buf2[], const uint8_t buf3[]);
extern void TEST_ONESHOT__squeeze_avx2x4(uint8_t buf0[], uint8_t buf1[], uint8_t buf2[], uint8_t buf3[], uint8_t* st);
extern void TEST_ONESHOT__absorb_bcast_avx2x4(uint8_t* st, const uint8_t buf[]);
extern void TEST_ONESHOT__addstate_bcast_avx2x4(uint8_t* st, const uint8_t buf[]);
extern void TEST_ONESHOT__dumpstate_avx2x4(uint8_t buf0[], uint8_t buf1[], uint8_t buf2[], uint8_t buf3[], uint8_t* st);

typedef uint64_t KeccakUpdState[26];
typedef uint64_t KeccakUpdStateX4[4*25+1];

// extern void init_updstate_avx2x4(KeccakUpdStateX4 st, const uint8_t r64, const uint8_t trailb);
// extern void unpack_updstate_avx2x4(KeccakUpdState s0, KeccakUpdState s1, KeccakUpdState s2, KeccakUpdState s3, KeccakUpdStateX4 st);
// extern void ststatus_updstate_avx2x4(uint8_t status[3], const KeccakUpdStateX4 st);
// extern void finish_updstate_avx2x4(KeccakUpdStateX4 st);
// extern void absorb_updstate_avx2x4(KeccakUpdStateX4 st, const uint8_t buf0[], const uint8_t buf1[], const uint8_t buf2[], const uint8_t buf3[], uint64_t len);
// extern void squeeze_updstate_avx2x4(KeccakUpdStateX4 st, uint8_t buf0[], uint8_t buf1[], uint8_t buf2[], uint8_t buf3[], uint64_t len);


uint64_t bench_init_state_avx2x4(uint8_t *st, uint64_t len_st) {
    uint64_t cycles[TIMINGS];
    for (int i = 0; i < TIMINGS; i++, st += len_st)
      { 
        cycles[i] = cpucycles();
        init_state_avx2x4(st);
      }
    return cpucycles_median(cycles, TIMINGS);
}

uint64_t bench_absorb_avx2x4(uint8_t *st,  const uint8_t buf0[], const uint8_t buf1[], const uint8_t buf2[], const uint8_t buf3[], uint64_t len_st, uint64_t len_buf) {
    uint64_t cycles[TIMINGS];
    for (int i = 0; i < TIMINGS; i++, st += len_st, buf0 += len_buf, buf1 += len_buf, buf2 += len_buf, buf3 += len_buf)
      { 
        cycles[i] = cpucycles();
        TEST_ONESHOT__absorb_avx2x4(st, buf0, buf1, buf2, buf3);
      }
    return cpucycles_median(cycles, TIMINGS);
}

uint64_t bench_squeeze_avx2x4(uint8_t *st,  uint8_t buf0[], uint8_t buf1[], uint8_t buf2[], uint8_t buf3[], uint64_t len_st, uint64_t len_buf) {
    uint64_t cycles[TIMINGS];
    for (int i = 0; i < TIMINGS; i++, st += len_st, buf0 += len_buf, buf1 += len_buf, buf2 += len_buf, buf3 += len_buf)
      { 
        cycles[i] = cpucycles();
        TEST_ONESHOT__squeeze_avx2x4(buf0, buf1, buf2, buf3, st);
      }
    return cpucycles_median(cycles, TIMINGS);
}

uint64_t bench_absorb_bcast_avx2x4(uint8_t *st,  const uint8_t buf[], uint64_t len_st, uint64_t len_buf) {
    uint64_t cycles[TIMINGS];
    for (int i = 0; i < TIMINGS; i++, st += len_st, buf += len_buf)
      { 
        cycles[i] = cpucycles();
        TEST_ONESHOT__absorb_bcast_avx2x4(st, buf);
      }
    return cpucycles_median(cycles, TIMINGS);
}

uint64_t bench_addstate_bcast_avx2x4(uint8_t *st,  const uint8_t buf[], uint64_t len_st, uint64_t len_buf) {
    uint64_t cycles[TIMINGS];
    for (int i = 0; i < TIMINGS; i++, st += len_st, buf += len_buf)
      { 
        cycles[i] = cpucycles();
        TEST_ONESHOT__addstate_bcast_avx2x4(st, buf);
      }
    return cpucycles_median(cycles, TIMINGS);
}

uint64_t bench_dumpstate_avx2x4(uint8_t *st,  uint8_t buf0[], uint8_t buf1[], uint8_t buf2[], uint8_t buf3[], uint64_t len_st, uint64_t len_buf) {
    uint64_t cycles[TIMINGS];
    for (int i = 0; i < TIMINGS; i++, st += len_st, buf0 += len_buf, buf1 += len_buf, buf2 += len_buf, buf3 += len_buf)
      { 
        cycles[i] = cpucycles();
        TEST_ONESHOT__dumpstate_avx2x4(buf0, buf1, buf2, buf3, st);
      }
    return cpucycles_median(cycles, TIMINGS);
}



int run_bench(uint64_t rate8, uint64_t trail, uint64_t size, uint64_t bigsize) {
    uint64_t results[OP][LOOPS];
    uint64_t cycles_init[RUNS], cycles_absorb[RUNS], cycles_squeeze[RUNS], cycles_absorb_bcast[RUNS], cycles_addstate_bcast[RUNS], cycles_dumpstate[RUNS];
    uint8_t * _p_st;
    uint8_t * _buf_in0, * _buf_in1, * _buf_in2, * _buf_in3;
    uint8_t *p_st;
    uint8_t *buf_in0, *buf_in1, *buf_in2, *buf_in3;
    size_t len_st, len_buf;
    len_st = alignedcalloc_step(sizeof(KeccakStateX4));
    len_buf = alignedcalloc_step(bigsize);
    p_st = alignedcalloc(&_p_st, len_st * TIMINGS);
    buf_in0 = alignedcalloc(&_buf_in0, len_buf * TIMINGS);
    buf_in1 = alignedcalloc(&_buf_in1, len_buf * TIMINGS);
    buf_in2 = alignedcalloc(&_buf_in2, len_buf * TIMINGS);
    buf_in3 = alignedcalloc(&_buf_in3, len_buf * TIMINGS);
    printf("|     init_state_avx2x4    |     absorb_avx2x4     |     squeeze_avx2x4    |     absorb_bcast_avx2x4   |    addstate_bcast_avx2x4 |     dumpstate_avx2x4    |\n");
    printf("|------------------------|------------------------|------------------------|--------------------------|------------------------|------------------------|\n");
    for(int run = 0; run < RUNS; run++) {
        for(int loop = 0; loop < LOOPS; loop++) {
            uint8_t * current_buf0 = buf_in0;
            uint8_t * current_buf1 = buf_in1;
            uint8_t * current_buf2 = buf_in2;
            uint8_t * current_buf3 = buf_in3;
            uint8_t * current_st = p_st;
            results[0][loop] = bench_init_state_avx2x4(current_st, len_st);
            current_st = p_st;
            results[1][loop] = bench_absorb_avx2x4(current_st, current_buf0, current_buf1, current_buf2, current_buf3, len_st, len_buf);
            current_st = p_st;
            current_buf0 = buf_in0;
            current_buf1 = buf_in1;
            current_buf2 = buf_in2;
            current_buf3 = buf_in3;
            results[2][loop] = bench_squeeze_avx2x4(current_st, current_buf0, current_buf1, current_buf2, current_buf3, len_st, len_buf);
            current_st = p_st;
            current_buf0 = buf_in0;
            results[3][loop] = bench_absorb_bcast_avx2x4(current_st, current_buf0, len_st, len_buf);
            current_st = p_st;
            current_buf0 = buf_in0;
            results[4][loop] = bench_addstate_bcast_avx2x4(current_st, current_buf0, len_st, len_buf);
            current_st = p_st;
            current_buf0 = buf_in0;
            current_buf1 = buf_in1;
            current_buf2 = buf_in2;
            current_buf3 = buf_in3;
            results[5][loop] = bench_dumpstate_avx2x4(current_st, current_buf0, current_buf1, current_buf2, current_buf3, len_st, len_buf);
        }
        median_fr(results);
        cycles_init[run] = results[0][0];
        cycles_absorb[run] = results[1][0];
        cycles_squeeze[run] = results[2][0];
        cycles_absorb_bcast[run] = results[3][0];
        cycles_addstate_bcast[run] = results[4][0];
        cycles_dumpstate[run] = results[5][0];
    }
    qsort(cycles_init, RUNS, sizeof(uint64_t), cmp_uint64);
    qsort(cycles_absorb, RUNS, sizeof(uint64_t), cmp_uint64);
    qsort(cycles_squeeze, RUNS, sizeof(uint64_t), cmp_uint64);
    qsort(cycles_absorb_bcast, RUNS, sizeof(uint64_t), cmp_uint64);
    qsort(cycles_addstate_bcast, RUNS, sizeof(uint64_t), cmp_uint64);
    qsort(cycles_dumpstate, RUNS, sizeof(uint64_t), cmp_uint64);

    for(int run = 0; run < RUNS; run++)
    {
       printf("| %20" PRIu64 " | %20" PRIu64 " |  %20" PRIu64 " | %20" PRIu64 " | %20" PRIu64 " | %20" PRIu64 "|\n",
                 cycles_init[run],
                 cycles_absorb[run],
                 cycles_squeeze[run],
                 cycles_absorb_bcast[run],
                 cycles_addstate_bcast[run],
                 cycles_dumpstate[run]
                );
    }
    free(_p_st);
    free(_buf_in0);
    free(_buf_in1);
    free(_buf_in2);
    free(_buf_in3);
    return 0;
}


int main() {
  uint64_t params_avx2x4[4];
  int i;

  get_params_avx2x4(params_avx2x4);

  return run_bench(params_avx2x4[0], params_avx2x4[1], params_avx2x4[2], params_avx2x4[3]);
}


