#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <assert.h>
#include <inttypes.h>



#define RUNS 10          
#define LOOPS 3        
#define TIMINGS 10000     
#define OP 4             

#define LEN_KECCAK 800 



#include "../common/cpucycles.c"
#include "../common/median.c"
#include "../common/alignedcalloc.c"

extern void __keccakf1600_avx2x4_A(uint8_t state[LEN_KECCAK]);
extern void __keccakf1600_avx2x4_B(uint8_t state[LEN_KECCAK]);

extern void _keccakf1600_4x_round_A(uint8_t e[LEN_KECCAK],uint8_t a[LEN_KECCAK], uint8_t rc);
extern void _keccakf1600_4x_round_B(uint8_t e[LEN_KECCAK],uint8_t a[LEN_KECCAK], uint8_t rc);


int main(void)
{
  int run, loop, i;
  uint64_t cycles[TIMINGS];
  uint64_t results[OP][LOOPS];

  uint64_t cycles_A[RUNS];
  uint64_t cycles_B[RUNS];
  uint64_t cycles_round_A[RUNS];
  uint64_t cycles_round_B[RUNS];


  uint8_t *_p_state_A, *_p_state_B; 
  uint8_t *p_state_A, *p_state_B; 
  size_t len_keccak;


  len_keccak = alignedcalloc_step(LEN_KECCAK);


  p_state_A = alignedcalloc(&_p_state_A, len_keccak * TIMINGS);
  p_state_B = alignedcalloc(&_p_state_B, len_keccak * TIMINGS);

  printf("|    __keccakf1600_avx2x4_new  |  __keccakf1600_avx2x4_old   |  _keccakf1600_4x_round_new |  _keccakf1600_4x_round_old |\n");
  printf("|------------------------|------------------------|-------------------------|-------------------------|\n");

  for(run = 0; run < RUNS; run++)
  {
    for(loop = 0; loop < LOOPS; loop++)
    {
      uint8_t *current_state_A = p_state_A; 
      uint8_t *current_state_B = p_state_A;
    
      for (i = 0; i < TIMINGS; i++, current_state_A += len_keccak)
      { 
        cycles[i] = cpucycles();
        __keccakf1600_avx2x4_A(current_state_A); 
      }
      results[0][loop] = cpucycles_median(cycles, TIMINGS);

    
      for (i = 0; i < TIMINGS; i++, current_state_B += len_keccak)
      { 
        cycles[i] = cpucycles();
        __keccakf1600_avx2x4_B(current_state_B); 
      }
      results[1][loop] = cpucycles_median(cycles, TIMINGS);

      current_state_A = p_state_A;
      current_state_B = p_state_B;

      for (i = 0; i < TIMINGS; i++, current_state_B += len_keccak)
      { 
        cycles[i] = cpucycles();
        _keccakf1600_4x_round_A(current_state_A,current_state_B, 0x01); 
      }
      results[2][loop] = cpucycles_median(cycles, TIMINGS); 

      current_state_A = p_state_A;
      current_state_B = p_state_B;

      for (i = 0; i < TIMINGS; i++, current_state_B += len_keccak)
      { 
        cycles[i] = cpucycles();
        _keccakf1600_4x_round_B(current_state_A,current_state_B, 0x01); 
      }
      results[3][loop] = cpucycles_median(cycles, TIMINGS);
      
    }
    

    median_fr(results);
    cycles_A[run] = results[0][0];
    cycles_B[run] = results[1][0];
    cycles_round_A[run] = results[2][0];
    cycles_round_B[run] = results[3][0];
  }


  qsort(cycles_A, RUNS, sizeof(uint64_t), cmp_uint64);
  qsort(cycles_B, RUNS, sizeof(uint64_t), cmp_uint64);
  qsort(cycles_round_A, RUNS, sizeof(uint64_t), cmp_uint64);
  qsort(cycles_round_B, RUNS, sizeof(uint64_t), cmp_uint64);
  

   for(run = 0; run < RUNS; run++)
  {
    printf("| %20" PRIu64 " | %20" PRIu64 " |  %20" PRIu64 " |  %20" PRIu64 " | \n",
      cycles_A[run],
      cycles_B[run],
      cycles_round_A[run],
      cycles_round_B[run]);
  }


  free(_p_state_A);
  free(_p_state_B);

  return 0;
}