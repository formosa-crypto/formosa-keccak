#include "../../../submodules/XKCP/lib/high/Keccak/FIPS202/SimpleFIPS202.h"

#include <stdint.h>

int XKCP_sha3_256(
  uint8_t *out,
  uint8_t *in
){
  return SHA3_256(out, in, 1184);
}

int XKCP_shake256(
  uint8_t *out,
  uint8_t *seed,
  uint8_t *nonce
){
  return SHAKE256(out, 128, seed, 32);
}

int XKCP_shake256x4(
  uint8_t *out1,
  uint8_t *out2,
  uint8_t *out3,
  uint8_t *out4,
  uint8_t *seed,
  uint8_t *nonce
){
  SHAKE256(out1, 128, seed, 32);
  SHAKE256(out2, 128, seed, 32);
  SHAKE256(out3, 128, seed, 32);
  SHAKE256(out4, 128, seed, 32);
  return   SHAKE256(out4, 128, seed, 32);

}