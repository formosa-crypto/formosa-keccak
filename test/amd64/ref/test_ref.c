#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <stdbool.h>


extern void get_params_ref(uint64_t*);

// FIXEDSIZES
typedef uint64_t KeccakState[25];

extern void init_state_ref(KeccakState st);
extern void TEST_AT__absorb_ref(KeccakState st, const uint8_t buf[]);
extern void TEST_ONESHOT__absorb_ref(KeccakState st, const uint8_t buf[]);
extern void TEST_ONESHOT__squeeze_ref(uint8_t buf[], KeccakState st);


// UPDSTATE
typedef uint64_t KeccakUpdState[26];

extern void init_updstate_ref(KeccakUpdState st, const uint8_t r64, const uint8_t trailb);
extern void ststatus_updstate_ref(uint8_t status[3], const KeccakUpdState st);
extern void finish_updstate_ref(KeccakUpdState st);
extern void TEST_UPD__update_updstate_ref(KeccakUpdState st, const uint8_t buf[]);
extern void TEST_UPD__squeeze_updstate_ref(uint8_t buf[], KeccakUpdState st);







// TESTING CODE
void print_buf(char* str, uint8_t a[], size_t len) {
  int i, j;
  if (str!=NULL) printf("%s = ", str);
  for (i=0; i<len; i++)
    printf("%02X", a[i]);
  printf("\n");
}

int chkeq_buf(char *str, uint8_t a1[], uint8_t a2[], size_t len) {
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

  return (i<0 ? 0 : 1);
}



int run_test(uint64_t rate8, uint64_t trail, uint64_t size, uint64_t bigsize) {
  int r=0, i, niters=bigsize/size;
  _Alignas(32) KeccakUpdState s1, s2, s3;

  uint8_t buf_in[bigsize];
  uint8_t buf_o1[bigsize], buf_o2[bigsize];

  // init input buffer
  uint8_t t8 = 0;
  for (i=0; i<bigsize; i++) {
    buf_in[i] = t8;
    t8++;
  }

  // init states
  init_updstate_ref(s1, rate8/8, trail);
  init_state_ref(s2);
  init_state_ref(s3);
  r = r || chkeq_buf("init", (uint8_t*) s1, (uint8_t*) s2, 8*25);


  for (i=0; i < niters; i++) {
    TEST_UPD__update_updstate_ref(s1,buf_in+i*size);
  }
  finish_updstate_ref(s1);
  TEST_ONESHOT__absorb_ref(s2, buf_in);
  r = r || chkeq_buf("absorb (updstate vs. oneshot)", (uint8_t*) s1, (uint8_t*) s2, 8*25);
  TEST_AT__absorb_ref(s3, buf_in);
  r = r || chkeq_buf("absorb (oneshot vs. increments)", (uint8_t*) s2, (uint8_t*) s3, 8*25);

  for (i=0; i < niters; i++) {
    TEST_UPD__squeeze_updstate_ref(buf_o1+i*size, s1);
  }
  TEST_ONESHOT__squeeze_ref(buf_o2, s2);
  r = r || chkeq_buf("squeeze", (uint8_t*) buf_o1, (uint8_t*) buf_o2, bigsize);

  return r;

}



int main() {
  uint64_t params[4];

  get_params_ref(params);

  return run_test(params[0], params[1], params[2], params[3]);
}

