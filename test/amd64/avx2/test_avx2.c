#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <stdbool.h>



extern void get_params_ref(uint64_t*);
extern void get_params_avx2(uint64_t*);


// AVX2
typedef uint64_t KeccakState[25];
typedef uint64_t KeccakUpdState[26];

extern void init_state_avx2(KeccakState st);

extern void TEST_AT__absorb_avx2(KeccakState st, const uint8_t buf[]);
extern void TEST_ONESHOT__absorb_avx2(KeccakState st, const uint8_t buf[]);
extern void TEST_ONESHOT__squeeze_avx2(KeccakState st, uint8_t buf[]);

typedef uint64_t KeccakUpdState[26];
extern void init_updstate_avx2(KeccakUpdState st, const uint8_t r64, const uint8_t trailb);
extern void ststatus_updstate(uint8_t status[3], const KeccakUpdState st);
extern void finish_updstate_avx2(KeccakUpdState st);
extern void TEST_UPD__absorb_updstate_avx2(KeccakUpdState st, const uint8_t buf[], uint64_t len);
extern void TEST_UPD__squeeze_updstate_avx2(KeccakUpdState st, uint8_t buf[], uint64_t len);

// REF

extern void init_updstate_ref(KeccakUpdState st, const uint8_t r64, const uint8_t trailb);
extern void TEST_UPD__absorb_updstate_ref(KeccakUpdState st, const uint8_t buf[], uint64_t len);
extern void finish_updstate_ref(KeccakUpdState st);
extern void TEST_UPD__squeeze_updstate_ref(KeccakUpdState st, uint8_t buf[], uint64_t len);






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


/* test vectors for SHA3-256 (source: https://di-mgt.com.au/sha_testvectors.html) */
uint8_t t1_in[] = "";
uint8_t t1_out[] = { 0xa7, 0xff, 0xc6, 0xf8, 0xbf, 0x1e, 0xd7, 0x66
		   , 0x51, 0xc1, 0x47, 0x56, 0xa0, 0x61, 0xd6, 0x62
		   , 0xf5, 0x80, 0xff, 0x4d, 0xe4, 0x3b, 0x49, 0xfa
		   , 0x82, 0xd8, 0x0a, 0x4b, 0x80, 0xf8, 0x43, 0x4a
                   };

uint8_t t2_in[] = "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq";
uint8_t t2_out[] = { 0x41, 0xc0, 0xdb, 0xa2, 0xa9, 0xd6, 0x24, 0x08
		   , 0x49, 0x10, 0x03, 0x76, 0xa8, 0x23, 0x5e, 0x2c
		   , 0x82, 0xe1, 0xb9, 0x99, 0x8a, 0x99, 0x9e, 0x21
		   , 0xdb, 0x32, 0xdd, 0x97, 0x49, 0x6d, 0x33, 0x76
                   };


int run_test(uint64_t rate8, uint64_t trail, uint64_t size, uint64_t bigsize) {
  int r=0, i, niters=bigsize/size;

  _Alignas(32) KeccakUpdState s0, s1, s2, s3;
  uint8_t buf_in[bigsize];
  uint8_t buf_o1[bigsize], buf_o2[bigsize];

  init_updstate_avx2(s1, 136/8, 0x06);
  TEST_UPD__absorb_updstate_avx2(s1, t1_in, sizeof(t1_in)-1);
  finish_updstate_avx2(s1);
  TEST_UPD__squeeze_updstate_avx2(s1, buf_o2, sizeof(t1_out));
  chkeq_buf("test vector 1 (updstate)", (uint8_t*) buf_o2, (uint8_t*) t1_out, sizeof(t1_out));
  init_updstate_avx2(s1, 136/8, 0x06);
  TEST_UPD__absorb_updstate_avx2(s1, t2_in, sizeof(t2_in)-1);
  finish_updstate_avx2(s1);
  TEST_UPD__squeeze_updstate_avx2(s1, buf_o2, sizeof(t2_out));
  chkeq_buf("test vector 2 (updstate)", (uint8_t*) buf_o2, (uint8_t*) t2_out, sizeof(t2_out));
  

  // ADHOC TESTS (comparing implementations)
  // init input buffer
  uint8_t t8 = 0;
  for (i=0; i<bigsize; i++) {
    buf_in[i] = t8;
    t8++;
  }

  // init states
  init_updstate_ref(s0, rate8/8, trail);
  init_updstate_avx2(s1, rate8/8, trail);
  init_updstate_avx2(s2, 0, 0);
  init_updstate_avx2(s3, 0, 0);
  chkeq_buf("init_updstate (ref vs. avx2)", (uint8_t*) s0, (uint8_t*) s1, 8*26);


  for (i=0; i < niters; i++) {
    TEST_UPD__absorb_updstate_ref(s0,buf_in+i*size, size);
    TEST_UPD__absorb_updstate_avx2(s1,buf_in+i*size, size);
  }
  finish_updstate_ref(s0);
  finish_updstate_avx2(s1);
  chkeq_buf("update_updstate (ref vs. avx2)", (uint8_t*) s0, (uint8_t*) s1, 8*26);
  TEST_ONESHOT__absorb_avx2(s2, buf_in);
  chkeq_buf("absorb_avx2 (updstate vs. oneshot)", (uint8_t*) s1, (uint8_t*) s2, 8*25);
  TEST_AT__absorb_avx2(s3, buf_in);
  chkeq_buf("absorb_avx2 (oneshot vs. increments)", (uint8_t*) s2, (uint8_t*) s3, 8*25);

  for (i=0; i < niters; i++) {
    TEST_UPD__squeeze_updstate_ref(s0, buf_o2+i*size, size);
    TEST_UPD__squeeze_updstate_avx2(s1, buf_o1+i*size, size);
  }
  chkeq_buf("squeeze_updstate (ref vs. avx2)", (uint8_t*) buf_o2, (uint8_t*) buf_o1, bigsize);
  TEST_ONESHOT__squeeze_avx2(s2, buf_o2);
  chkeq_buf("squeeze_avx2 (updstate vs. oneshot)", (uint8_t*) buf_o1, (uint8_t*) buf_o2, bigsize);

  return 0;
}


int main() {
  uint64_t params_ref[4], params_avx2[4];
  int i;

  get_params_ref(params_ref);
  get_params_avx2(params_avx2);

  for (i=0; i<4; i++) 
    if (params_ref[i] != params_avx2[i] ) {
      printf("Error: mismatch between _ref and _avx2 parameters!\n");
      exit(1);
    }


  return run_test(params_avx2[0], params_avx2[1], params_avx2[2], params_avx2[3]);
}


