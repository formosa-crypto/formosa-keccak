#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <stdbool.h>



extern void get_params_ref(uint64_t*);
extern void get_params_avx2x4(uint64_t*);


// AVX2x4
typedef uint64_t KeccakState[25];
typedef uint64_t KeccakStateX4[4*25];

extern void init_state_avx2x4(KeccakStateX4 st);
extern void TEST_AT__absorb_avx2x4(KeccakStateX4 st, const uint8_t buf0[], const uint8_t buf1[], const uint8_t buf2[], const uint8_t buf3[]);
extern void TEST_ONESHOT__absorb_avx2x4(KeccakStateX4 st, const uint8_t buf0[], const uint8_t buf1[], const uint8_t buf2[], const uint8_t buf3[]);
extern void TEST_ONESHOT__squeeze_avx2x4(uint8_t buf0[], uint8_t buf1[], uint8_t buf2[], uint8_t buf3[], KeccakStateX4 st);


typedef uint64_t KeccakUpdState[26];
typedef uint64_t KeccakUpdStateX4[4*25+1];

extern void init_updstate_avx2x4(KeccakUpdStateX4 st, const uint8_t r64, const uint8_t trailb);
extern void unpack_updstate_avx2x4(KeccakUpdState s0, KeccakUpdState s1, KeccakUpdState s2, KeccakUpdState s3, KeccakUpdStateX4 st);
extern void ststatus_updstate_avx2x4(uint8_t status[3], const KeccakUpdStateX4 st);
extern void finish_updstate_avx2x4(KeccakUpdStateX4 st);
extern void TEST_UPD__update_updstate_avx2x4(KeccakUpdStateX4 st, const uint8_t buf0[], const uint8_t buf1[], const uint8_t buf2[], const uint8_t buf3[]);
extern void TEST_UPD__squeeze_updstate_avx2x4(uint8_t buf0[], uint8_t buf1[], uint8_t buf2[], uint8_t buf3[], KeccakUpdStateX4 st);

// REF

extern void init_updstate_ref(KeccakUpdState st, const uint8_t r64, const uint8_t trailb);
extern void TEST_UPD__update_updstate_ref(KeccakUpdState st, const uint8_t buf[]);
extern void finish_updstate_ref(KeccakUpdState st);
extern void TEST_UPD__squeeze_updstate_ref(uint8_t buf[], KeccakState st);






// TESTING CODE
void print_buf(char* str, uint8_t a[], size_t len) {
  int i, j;
  if (str!=NULL) printf("%s = ", str);
  for (i=0; i<len; i++)
    printf("%02X", a[i]);
  printf("\n");
}

void chkeq_buf(char *str, uint8_t a1[], uint8_t a2[], size_t len) {
  bool r;
  int i;

  r = true;
  for (i=0; r && i<len; i++)
    r = r && (a1[i]==a2[i]);
  if (r) i = -1; else i -= 1;

  if (str!=NULL) printf("TESTING %s:\n", str);
  if (i < 0) {
    printf("  Ok!\n");
  } else {
    printf("  Error at pos=%d\n", i);
    print_buf("L", a1, len);
    print_buf("R", a2, len);
  }
  printf("\n");
}




int run_test(uint64_t rate8, uint64_t trail, uint64_t size, uint64_t bigsize) {
  int r=0, i, niters=bigsize/size;

  KeccakUpdState s0ref, s1ref, s2ref, s3ref, su0, su1, su2, su3;
  _Alignas(32) KeccakUpdStateX4 s0, s1, s2, s3;
  uint8_t buf_in0[bigsize], buf_in1[bigsize], buf_in2[bigsize], buf_in3[bigsize];
  uint8_t buf_o1[bigsize], buf_o2[bigsize];

  // init input buffer
  uint8_t t8 = 0;
  for (i=0; i<bigsize; i++) {
    buf_in0[i] = t8++;
    buf_in1[i] = t8++;
    buf_in2[i] = t8++;
    buf_in3[i] = t8++;
  }

  // init states
  init_updstate_ref(s0ref, rate8/8, trail);
  init_updstate_ref(s1ref, rate8/8, trail);
  init_updstate_ref(s2ref, rate8/8, trail);
  init_updstate_ref(s3ref, rate8/8, trail);
  init_updstate_avx2x4(s0, rate8/8, trail);
  init_updstate_avx2x4(s1, 0, 0); // fixedsizes
  init_updstate_avx2x4(s2, 0, 0); // fixedsizes
  unpack_updstate_avx2x4(su0, su1, su2, su3, s0);
  chkeq_buf("init_updstate (ref0 vs. avx2x4_0)", (uint8_t*) s0ref, (uint8_t*) su0, 8*26);
  chkeq_buf("init_updstate (ref1 vs. avx2x4_1)", (uint8_t*) s1ref, (uint8_t*) su1, 8*26);
  chkeq_buf("init_updstate (ref2 vs. avx2x4_2)", (uint8_t*) s2ref, (uint8_t*) su2, 8*26);
  chkeq_buf("init_updstate (ref3 vs. avx2x4_3)", (uint8_t*) s3ref, (uint8_t*) su3, 8*26);

  for (i=0; i < niters; i++) {
    TEST_UPD__update_updstate_ref(s0ref,buf_in0+i*size);
    TEST_UPD__update_updstate_ref(s1ref,buf_in1+i*size);
    TEST_UPD__update_updstate_ref(s2ref,buf_in2+i*size);
    TEST_UPD__update_updstate_ref(s3ref,buf_in3+i*size);
    TEST_UPD__update_updstate_avx2x4(s0,buf_in0+i*size,buf_in1+i*size,buf_in2+i*size,buf_in3+i*size);
  }
  finish_updstate_ref(s0ref);
  finish_updstate_ref(s1ref);
  finish_updstate_ref(s2ref);
  finish_updstate_ref(s3ref);
  finish_updstate_avx2x4(s0);
  unpack_updstate_avx2x4(su0, su1, su2, su3, s0);
  chkeq_buf("update_updstate (ref0 vs. avx2x4)", (uint8_t*) s0ref, (uint8_t*) su0, 8*26);
  chkeq_buf("update_updstate (ref1 vs. avx2x4)", (uint8_t*) s1ref, (uint8_t*) su1, 8*26);
  chkeq_buf("update_updstate (ref2 vs. avx2x4)", (uint8_t*) s2ref, (uint8_t*) su2, 8*26);
  chkeq_buf("update_updstate (ref3 vs. avx2x4)", (uint8_t*) s3ref, (uint8_t*) su3, 8*26);
  TEST_ONESHOT__absorb_avx2x4(s1, buf_in0, buf_in1, buf_in2, buf_in3);
  chkeq_buf("absorb_avx2x4 (updstate vs. oneshot)", (uint8_t*) s0, (uint8_t*) s1, 8*(4*25));
  unpack_updstate_avx2x4(su0, su1, su2, su3, s1);
  chkeq_buf("update_updstate (ref0 vs. oneshot avx2x4)", (uint8_t*) s0ref, (uint8_t*) su0, 8*25);
  chkeq_buf("update_updstate (ref1 vs. oneshot avx2x4)", (uint8_t*) s1ref, (uint8_t*) su1, 8*25);
  chkeq_buf("update_updstate (ref2 vs. oneshot avx2x4)", (uint8_t*) s2ref, (uint8_t*) su2, 8*25);
  chkeq_buf("update_updstate (ref3 vs. oneshot avx2x4)", (uint8_t*) s3ref, (uint8_t*) su3, 8*25);
  TEST_AT__absorb_avx2x4(s2, buf_in0, buf_in1, buf_in2, buf_in3);
  chkeq_buf("absorb_avx2 (oneshot vs. increments)", (uint8_t*) s1, (uint8_t*) s2, 8*(4*25));

/*
  for (i=0; i < niters; i++) {
    TEST_UPD__squeeze_updstate_ref(buf_o2+i*size, s0);
    TEST_UPD__squeeze_updstate_avx2(buf_o1+i*size, s1);
  }
  chkeq_buf("squeeze_updstate (ref vs. avx2)", (uint8_t*) buf_o2, (uint8_t*) buf_o1, bigsize);
  TEST_ONESHOT__squeeze_avx2(buf_o2, s2);
  chkeq_buf("squeeze_avx2 (updstate vs. oneshot)", (uint8_t*) buf_o1, (uint8_t*) buf_o2, bigsize);
*/

  return 0;
}


int main() {
  uint64_t params_ref[4], params_avx2x4[4];
  int i;

  get_params_ref(params_ref);
  get_params_avx2x4(params_avx2x4);

  for (i=0; i<4; i++) 
    if (params_ref[i] != params_avx2x4[i] ) {
      printf("Error: mismatch between _ref and _avx2x4 parameters!\n");
      exit(1);
    }


  return run_test(params_avx2x4[0], params_avx2x4[1], params_avx2x4[2], params_avx2x4[3]);
}


