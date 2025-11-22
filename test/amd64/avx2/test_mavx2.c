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

extern void absorb_m_avx2(KeccakState st, const uint8_t buf[]);
extern void squeeze_m_avx2(KeccakState st, uint8_t buf[]);

// UPDSTATE
typedef uint64_t KeccakUpdState[26];

extern void init_updstate_avx2(KeccakUpdState st, const uint8_t r64, const uint8_t trailb);
extern void ststatus_updstate(uint8_t status[3], const KeccakUpdState st);
extern void finish_updstate_avx2(KeccakUpdState st);
extern void absorb_m_updstate_avx2(KeccakUpdState st, const uint8_t buf[], uint64_t len);
extern void squeeze_m_updstate_avx2(KeccakUpdState st, uint8_t buf[], uint64_t len);







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

  _Alignas(32) KeccakUpdState s0, s1, s2, s3;
  uint8_t buf_in[bigsize];
  uint8_t buf_o1[bigsize], buf_o2[bigsize];

  // init input buffer
  uint8_t t8 = 0;
  for (i=0; i<bigsize; i++) {
    buf_in[i] = t8;
    t8++;
  }

  // init states
  init_updstate_avx2(s1, rate8/8, trail);
  init_updstate_avx2(s2, 0, 0);
  chkeq_buf("init_updstate (ref vs. avx2)", (uint8_t*) s1, (uint8_t*) s2, 8*25);


  for (i=0; i < niters; i++) {
    absorb_m_updstate_avx2(s1, buf_in+i*size, size);
  }
  finish_updstate_avx2(s1);
  absorb_m_avx2(s2, buf_in);
  chkeq_buf("absorb (updstate vs. avx2)", (uint8_t*) s1, (uint8_t*) s2, 8*25);

  for (i=0; i < niters; i++) {
    squeeze_m_updstate_avx2(s1, buf_o1+i*size, size);
  }
  squeeze_m_avx2(s2, buf_o2);
  chkeq_buf("squeeze (updstate vs. avx2)", (uint8_t*) buf_o2, (uint8_t*) buf_o1, bigsize);

  return 0;
}


int main() {
  uint64_t params_avx2[4];
  int i;

  get_params_avx2(params_avx2);

  return run_test(params_avx2[0], params_avx2[1], params_avx2[2], params_avx2[3]);
}


