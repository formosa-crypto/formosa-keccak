#include <stdint.h>
#include <stdio.h>
#include <string.h>

/* Jasmin exports (return the state pointer in rax; declared void here). */
extern void testF_ref(uint64_t st[25]);
extern void testF_native(uint64_t st[25]);

/* Canonical Keccak-f[1600] output for the all-zero input state. */
static const uint64_t kat_zero[25] = {
  0xF1258F7940E1DDE7ULL, 0x84D5CCF933C0478AULL, 0xD598261EA65AA9EEULL,
  0xBD1547306F80494DULL, 0x8B284E056253D057ULL, 0xFF97A42D7F8E6FD4ULL,
  0x90FEE5A0A44647C4ULL, 0x8C5BDA0CD6192E76ULL, 0xAD30A6F71B19059CULL,
  0x30935AB7D08FFC64ULL, 0xEB5AA93F2317D635ULL, 0xA9A6E6260D712103ULL,
  0x81A57C16DBCF555FULL, 0x43B831CD0347C826ULL, 0x01F22F1A11A5569FULL,
  0x05E5635A21D9AE61ULL, 0x64BEFEF28CC970F2ULL, 0x613670957BC46611ULL,
  0xB87C5A554FD00ECBULL, 0x8C3EE88A1CCF32C8ULL, 0x940C7922AE3A2614ULL,
  0x1841F924A2C509E4ULL, 0x16F53526E70465C2ULL, 0x75F644E97F30A13BULL,
  0xEAF1FF7B5CECA249ULL
};

static void fill_pseudo(uint64_t *s, uint64_t seed)
{
  uint64_t x = seed ? seed : 0x123456789ABCDEF0ULL;
  for (int i = 0; i < 25; i++) {
    x ^= x << 13; x ^= x >> 7; x ^= x << 17;
    s[i] = x;
  }
}

int main(void)
{
  int fail = 0;

  /* Equivalence: testF_native must match testF_ref on every input. */
  for (int trial = 0; trial < 8; trial++) {
    uint64_t a[25], b[25];

    if (trial == 0)      memset(a, 0x00, sizeof a);
    else if (trial == 1) memset(a, 0xFF, sizeof a);
    else                 fill_pseudo(a, 0x1000ULL + (uint64_t)trial);

    memcpy(b, a, sizeof a);
    testF_ref(a);
    testF_native(b);

    if (memcmp(a, b, sizeof a) != 0) {
      printf("MISMATCH ref vs native at trial %d:\n", trial);
      for (int i = 0; i < 25; i++)
        if (a[i] != b[i])
          printf("  lane %2d  ref=%016llx  native=%016llx\n",
                 i, (unsigned long long)a[i], (unsigned long long)b[i]);
      fail = 1;
    }
  }

  /* Known-answer for the zero state (guards against both being wrong). */
  {
    uint64_t z[25];
    memset(z, 0, sizeof z); testF_native(z);
    if (memcmp(z, kat_zero, sizeof z) != 0) { printf("KAT zero-state FAILED (native)\n"); fail = 1; }
    memset(z, 0, sizeof z); testF_ref(z);
    if (memcmp(z, kat_zero, sizeof z) != 0) { printf("KAT zero-state FAILED (ref)\n");    fail = 1; }
  }

  if (!fail)
    printf("ALL OK: testF_native matches testF_ref over 8 inputs and the zero-state KAT.\n");

  return fail;
}
