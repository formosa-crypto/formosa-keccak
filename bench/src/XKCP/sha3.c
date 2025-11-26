#include "../../../submodules/XKCP/lib/high/Keccak/FIPS202/SimpleFIPS202.h"

#include <stdint.h>

int XKCP_sha3_256(
  uint8_t *out,
  uint8_t *in
){
  return SHA3_256(out, in, 1184);
}