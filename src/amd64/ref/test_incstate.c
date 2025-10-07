#include <stdint.h>
#include <stdio.h>
#include <stdbool.h>


#define LEN 11
#define ASIZE 11*100

#include "sha3_jasmin.h"

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


int main() {
  KeccakIncState s1, s2;
  uint64_t *p;
  uint8_t buf_in[ASIZE];
  uint8_t buf_o1[ASIZE], buf_o2[ASIZE];
  int i;
  uint8_t t8 = 0;

  for (i=0; i<ASIZE; i++) {
    buf_in[i] = t8;
    t8++;
  }

  keccak_init(s1, KECCAK_256_r64, KECCAK_SHAKE);
  shake256_array_init(s2);
  chkeq_buf("init", (uint8_t*) s1, (uint8_t*) s2, 8*25);


  for (i=0; i < ASIZE/LEN; i++) {
    keccak_update_ref(s1,buf_in+i*LEN);
  }
  keccak_finish(s1);
  shake256_absorb_ref(s2, buf_in);
  chkeq_buf("absorb", (uint8_t*) s1, (uint8_t*) s2, 8*25);

  for (i=0; i < ASIZE/LEN; i++) {
    keccak_squeeze_ref(buf_o1+i*LEN, s1);
  }
  shake256_squeeze_ref(buf_o2, s2);
  chkeq_buf("squeeze", (uint8_t*) buf_o1, (uint8_t*) buf_o2, ASIZE);

  return 0;
}

