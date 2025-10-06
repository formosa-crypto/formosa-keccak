#include <stdint.h>

typedef uint64_t KeccakIncState[26];
typedef uint64_t KeccakState[25];


extern void keccak_init(KeccakIncState st, const uint8_t r64, const uint8_t trailb);
extern void keccak_ststatus(uint8_t status[3], const KeccakIncState st);
extern void keccak_finish(KeccakIncState st);
extern void keccak_update_ref(KeccakIncState st, const uint8_t buf[LEN]);
extern void keccak_squeeze_ref(uint8_t buf[LEN], KeccakIncState st);


#define KECCAK_128_r64 21
#define KECCAK_224_r64 18
#define KECCAK_256_r64 17
#define KECCAK_384_r64 13
#define KECCAK_512_r64 9

#define KECCAK_SHA3 0x06
#define KECCAK_SHAKE 0x1F


extern void shake256_array_init(KeccakState st);
extern void shake256_absorb_ref(KeccakState st, const uint8_t buf[LEN]);
extern void shake256_squeeze_ref(uint8_t buf[LEN], KeccakState st);


