#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <stdbool.h>



extern void get_params_ref(uint64_t*);
extern void get_params_avx2x4(uint64_t*);


// AVX2x4
typedef uint64_t KeccakState[25];
typedef uint64_t KeccakStateAvx2[28];
typedef uint64_t KeccakStateX4[4*25];

extern void testF_bmi1(KeccakState st);
extern void testF_native(KeccakState st);
extern void testF_avx2(KeccakStateAvx2 st);
extern void testF_avx2x4_orig(KeccakStateX4 st);
extern void testF_avx2x4_alt(KeccakStateX4 st);
extern void testF_avx2x4_native(KeccakStateX4 st);




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




int run_test() {
  int i, j;

  _Alignas(32) KeccakStateX4 s;
  _Alignas(32) KeccakStateX4 s0, s1, s2;

  // init input states

  // call permutation
  uint8_t t8 = 0;
  uint64_t t64 = 0;
  for (j=0; j<8; j++) {
    t64 <<= 8;
    t64 |= t8;
    t8++;
  }
  for (i=0; i<25; i++) {
    s0[4*i+0] = t64;
    s0[4*i+1] = t64;
    s0[4*i+2] = t64;
    s0[4*i+3] = t64;
    s1[4*i+0] = t64;
    s1[4*i+1] = t64;
    s1[4*i+2] = t64;
    s1[4*i+3] = t64;
    s2[4*i+0] = t64;
    s2[4*i+1] = t64;
    s2[4*i+2] = t64;
    s2[4*i+3] = t64;
  }

  testF_avx2x4_orig(s0);
  testF_avx2x4_alt(s1);
  testF_avx2x4_native(s2);

  // check outputs
  chkeq_buf("f1600 (orig vs. alt)", (uint8_t*) s0, (uint8_t*) s1, 8*25);
  chkeq_buf("f1600 (orig vs. native)", (uint8_t*) s0, (uint8_t*) s2, 8*25);

  return 0;
}


int main() {
  return run_test();
}


