#ifndef JASMIN_OLD_REF_API_H
#define JASMIN_OLD_REF_API_H

#include <stdint.h>


int jasmin_old_ref_sha3_256(
  uint8_t *out,
  uint8_t *in
);

int jasmin_old_ref_shake256(
  uint8_t *out,
  uint8_t *seed,
  uint8_t *nonce
);

int jasmin_old_ref_shake256x4(
  uint8_t *out1,
  uint8_t *out2,
  uint8_t *out3,
  uint8_t *out4,
  uint8_t *seed,
  uint8_t *nonce
);




#endif