#include <stdio.h>
#include <string.h>
#include <stdlib.h>

#include "../../../../submodules/XKCP/lib/high/Keccak/FIPS202/SimpleFIPS202.h"

extern void _sha3_256A_A1184(unsigned char *output, const unsigned char *input);
int main(void)
{
  unsigned char out0[32];
  unsigned char out1[32];
  unsigned char *in0 = malloc(1184);
  unsigned char *in1 = malloc(1184);
  if (in0 == NULL || in1 == NULL) { fprintf(stderr, "malloc failed\n"); exit(1); }
  for (int i = 0; i < 1184; ++i) {
      in0[i] = (unsigned char)(i & 0xFF);
      in1[i] = in0[i];
  }
  in1[1183] ^= 0xFF;

  /* TEST SHA3 */
  SHA3_256(out0, in0, 1184);
  _sha3_256A_A1184(out1, in1);


  for(int i=0;i<32;i++)
    if(out0[i] == out1[i]) { printf("error sha3: %d\n", i); exit(-1); }

  return 0;
}
