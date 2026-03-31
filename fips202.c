/*
 * Copyright (c) The mldsa-native project authors
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
 *
 * C harness for the formosa-keccak AVX2 FIPS 202 implementation.
 *
 * The actual Keccak-f[1600] computation is performed by Jasmin-compiled
 * assembly (fips202.jazz → fips202.s).  This file is a thin bridge that
 * maps the mld_shake128ctx / mld_shake256ctx structs to the u64[26]
 * "keccak_updstate" format expected by the Jasmin functions.
 *
 * Layout compatibility
 * --------------------
 * Both context structs have the layout:
 *
 *   bytes   0-199 : s[25]  (25 × uint64_t – the Keccak-f[1600] state)
 *   bytes 200-203 : pos    (unsigned int  – byte offset in current rate block)
 *   bytes 204-207 : pad    (4-byte struct padding to reach 8-byte alignment)
 *
 * Total: 208 bytes = 26 × 8, exactly matching the Jasmin keccak_updstate
 * type (u64[26]).  The 26th word (bytes 200-207) carries Jasmin metadata:
 *
 *   word[25] = (trailb << 16) | ((r64-1) << 8) | at_position
 *
 * where  trailb = 0x1F (SHAKE domain separator),
 *        r64    = rate_in_bytes / 8,
 *        at_position = pos (byte offset within the current rate block).
 *
 * Before each Jasmin call the metadata word is written into bytes 200-207
 * via memcpy (avoiding strict-aliasing UB).  After the call the updated
 * at_position is read back and stored into state->pos.  No copying of the
 * 25 Keccak state words is required.
 *
 * Alignment
 * ---------
 * The AVX2 permutation requires the state to be 32-byte aligned.  Each
 * public function asserts this at entry (disabled when NDEBUG is defined).
 * Callers must declare context variables with _Alignas(32).
 */

#include <assert.h>
#include <stdint.h>
#include <string.h>

#include "fips202.h"

/* Verify that the struct layout is compatible with Jasmin's keccak_updstate. */
_Static_assert(sizeof(mld_shake128ctx) == 26 * sizeof(uint64_t),
               "mld_shake128ctx layout incompatible with Jasmin keccak_updstate");
_Static_assert(sizeof(mld_shake256ctx) == 26 * sizeof(uint64_t),
               "mld_shake256ctx layout incompatible with Jasmin keccak_updstate");

/* ---------------------------------------------------------------------------
 * Jasmin-exported AVX2 updstate functions.
 *
 * The first argument is a pointer to a 208-byte, 32-byte-aligned buffer
 * (the keccak_updstate).  Declared as uint64_t[] so that the array decays
 * to uint64_t* in the C prototype, matching the Jasmin calling convention.
 * --------------------------------------------------------------------------- */
typedef uint64_t KeccakUpdState[26];

extern void finish_updstate_avx2(KeccakUpdState st);
extern void absorb_m_updstate_avx2(KeccakUpdState st, const uint8_t *buf,
                                   uint64_t len);
extern void squeeze_m_updstate_avx2(KeccakUpdState st, uint8_t *buf,
                                    uint64_t len);

/* ---------------------------------------------------------------------------
 * Internal helpers
 * --------------------------------------------------------------------------- */

/* SHAKE multi-rate padding suffix byte. */
#define SHAKE_TRAIL UINT8_C(0x1F)

/* Rate in 64-bit words: r64 = rate_in_bytes / 8. */
#define SHAKE128_R64 (SHAKE128_RATE / 8u) /* 21 */
#define SHAKE256_R64 (SHAKE256_RATE / 8u) /* 17 */

/* Byte offset of the metadata word within the context struct (= 25 × 8). */
#define META_OFFSET (MLD_KECCAK_LANES * sizeof(uint64_t)) /* 200 */

/*
 * Pack the Jasmin metadata word.
 * Format: (trailb << 16) | ((r64-1) << 8) | at_position
 */
static inline uint64_t pack_meta(unsigned int r64, unsigned int pos)
{
    return ((uint64_t)SHAKE_TRAIL << 16) | ((uint64_t)(r64 - 1u) << 8) |
           (uint64_t)pos;
}

/*
 * Enforce 32-byte alignment required by the AVX2 permutation.
 * The assert is compiled out when NDEBUG is defined.
 */
#define ASSERT_ALIGNED(ptr) assert(((uintptr_t)(ptr) & 31u) == 0)

/*
 * Write the Jasmin metadata word into bytes [META_OFFSET, META_OFFSET+8)
 * of the context struct, then read back the updated metadata afterward.
 *
 * The memcpy calls are the sanctioned way to alias unrelated types in C
 * without invoking undefined behaviour from the strict-aliasing rule.
 */
static inline void write_meta(uint64_t *s, unsigned int r64, unsigned int pos)
{
    uint64_t meta = pack_meta(r64, pos);
    memcpy((uint8_t *)s + META_OFFSET, &meta, sizeof(meta));
}

static inline unsigned int read_pos(const uint64_t *s)
{
    uint64_t meta;
    memcpy(&meta, (const uint8_t *)s + META_OFFSET, sizeof(meta));
    return (unsigned int)(meta & 0xFFu);
}

/* ---------------------------------------------------------------------------
 * SHAKE128
 * --------------------------------------------------------------------------- */

MLD_INTERNAL_API
void mld_shake128_init(mld_shake128ctx *state)
{
    ASSERT_ALIGNED(state);
    memset(state->s, 0, sizeof(state->s));
    state->pos = 0;
}

MLD_INTERNAL_API
void mld_shake128_absorb(mld_shake128ctx *state, const uint8_t *in,
                         size_t inlen)
{
    ASSERT_ALIGNED(state);
    write_meta(state->s, SHAKE128_R64, state->pos);
    absorb_m_updstate_avx2(state->s, in, (uint64_t)inlen);
    state->pos = read_pos(state->s);
}

MLD_INTERNAL_API
void mld_shake128_finalize(mld_shake128ctx *state)
{
    ASSERT_ALIGNED(state);
    write_meta(state->s, SHAKE128_R64, state->pos);
    finish_updstate_avx2(state->s);
    state->pos = read_pos(state->s);
}

MLD_INTERNAL_API
void mld_shake128_squeeze(uint8_t *out, size_t outlen, mld_shake128ctx *state)
{
    ASSERT_ALIGNED(state);
    write_meta(state->s, SHAKE128_R64, state->pos);
    squeeze_m_updstate_avx2(state->s, out, (uint64_t)outlen);
    state->pos = read_pos(state->s);
}

MLD_INTERNAL_API
void mld_shake128_release(mld_shake128ctx *state)
{
    volatile uint64_t *p = (volatile uint64_t *)state->s;
    size_t i;
    for (i = 0; i < MLD_KECCAK_LANES; i++)
        p[i] = 0;
    state->pos = 0;
}

/* ---------------------------------------------------------------------------
 * SHAKE256
 * --------------------------------------------------------------------------- */

MLD_INTERNAL_API
void mld_shake256_init(mld_shake256ctx *state)
{
    ASSERT_ALIGNED(state);
    memset(state->s, 0, sizeof(state->s));
    state->pos = 0;
}

MLD_INTERNAL_API
void mld_shake256_absorb(mld_shake256ctx *state, const uint8_t *in,
                         size_t inlen)
{
    ASSERT_ALIGNED(state);
    write_meta(state->s, SHAKE256_R64, state->pos);
    absorb_m_updstate_avx2(state->s, in, (uint64_t)inlen);
    state->pos = read_pos(state->s);
}

MLD_INTERNAL_API
void mld_shake256_finalize(mld_shake256ctx *state)
{
    ASSERT_ALIGNED(state);
    write_meta(state->s, SHAKE256_R64, state->pos);
    finish_updstate_avx2(state->s);
    state->pos = read_pos(state->s);
}

MLD_INTERNAL_API
void mld_shake256_squeeze(uint8_t *out, size_t outlen, mld_shake256ctx *state)
{
    ASSERT_ALIGNED(state);
    write_meta(state->s, SHAKE256_R64, state->pos);
    squeeze_m_updstate_avx2(state->s, out, (uint64_t)outlen);
    state->pos = read_pos(state->s);
}

MLD_INTERNAL_API
void mld_shake256_release(mld_shake256ctx *state)
{
    volatile uint64_t *p = (volatile uint64_t *)state->s;
    size_t i;
    for (i = 0; i < MLD_KECCAK_LANES; i++)
        p[i] = 0;
    state->pos = 0;
}

/* ---------------------------------------------------------------------------
 * SHAKE256 – non-incremental one-shot API
 * --------------------------------------------------------------------------- */

MLD_INTERNAL_API
void mld_shake256(uint8_t *out, size_t outlen, const uint8_t *in, size_t inlen)
{
    _Alignas(32) mld_shake256ctx state;
    mld_shake256_init(&state);
    mld_shake256_absorb(&state, in, inlen);
    mld_shake256_finalize(&state);
    mld_shake256_squeeze(out, outlen, &state);
    mld_shake256_release(&state);
}
