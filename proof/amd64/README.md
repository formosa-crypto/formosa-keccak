# proof/amd64 — functional correctness (old array model)

This tree proves the functional correctness of the Keccak implementations in
`src/amd64` against the FIPS 202 specification of
`submodules/crypto-specs/fips202`: every absorb, squeeze and streaming
procedure, and every Keccak-f[1600] permutation, computes what the
specification says. There are no admits.

The proofs are about code extracted with `jasmin2ec --array-model=old`, a
model that Jasmin has deprecated: polymorphic arrays `ArrayN` with `WArrayN`
byte views. `proof/amd64-barray` holds the same proofs for the current
`barray` model, and also the safety proofs.

## What is proved

| Implementation | Fixed-size, memory | Fixed-size, array | Streaming, memory | Streaming, array |
| --- | --- | --- | --- | --- |
| `ref` (1-way, `u64[25]` state) | ✓ | ✓ | ✓ | ✓ |
| `avx2` (1-way, `u256[7]` state) | ✓ | ✓ | as `ref` ¹ | as `ref` ¹ |
| `avx2x4` (4-way, `u256[25]` state) | ✓ ² | ✓ ² | ✓ ² | ✓ ² |

1. The 1-way streaming API has a single implementation,
   `src/amd64/ref/keccak1600_updstate{,_ASIZE}.jinc`, whose whole-lane loops
   branch on `KECCAK_FEATURES` (AVX2 or scalar). Both branches are proved.
2. Absorb with four buffers, and with one buffer broadcast to the four lanes
   (`bcast`).

*Fixed-size* procedures absorb or squeeze a whole buffer whose length is a
compile-time parameter. *Streaming* (`updstate`) procedures keep the state
and a status word between calls, and accept any length. *Memory* variants
take a pointer; *array* variants take an array whose size is a parameter
(`_ASIZE`).

| Cell | File (theory) | Main lemmas |
| --- | --- | --- |
| ref fixed-size, memory | `ref/Keccak1600_fixedsizes_ref.ec` | `absorb_m_h`, `squeeze_m_h` |
| ref fixed-size, array | same file (`KeccakArrayRef`) | `absorb_h`, `squeeze_h` |
| ref streaming, memory | `ref/Keccak1600_updstate_ref.ec` | `init_updstate_export_h`, `absorb_m_updstate_export_h`, `finish_updstate_export_h`, `squeeze_m_updstate_export_h` |
| ref streaming, array | same file (`KeccakUpdstateRef`) | `absorb_updstate_export_h`, `squeeze_updstate_export_h` |
| avx2 fixed-size, memory | `avx2/Keccak1600_fixedsizes_avx2.ec` | `absorb_m_avx2_h`, `squeeze_m_avx2_h` |
| avx2 fixed-size, array | same file (`KeccakArrayAvx2`) | `absorb_avx2_h`, `squeeze_avx2_h` |
| avx2x4 fixed-size, memory | `avx2/Keccak1600_fixedsizes_avx2x4.ec` | `absorb_m_avx2x4_h`, `absorb_m_bcast_avx2x4_h`, `squeeze_m_avx2x4_h` |
| avx2x4 fixed-size, array | same file (`KeccakArrayAvx2x4`) | `absorb_avx2x4_h`, `absorb_bcast_avx2x4_h`, `squeeze_avx2x4_h` |
| avx2x4 streaming, memory | `avx2/Keccak1600_updstate_avx2x4.ec` | `init_updstate_avx2x4_export_h`, `absorb_m_updstate_avx2x4_export_h`, `absorb_m_bcast_updstate_avx2x4_export_h`, `finish_updstate_avx2x4_export_h`, `squeeze_m_updstate_avx2x4_export_h` |
| avx2x4 streaming, array | same file (`KeccakUpdstateAvx2x4`) | `absorb_updstate_avx2x4_export_h`, `absorb_bcast_updstate_avx2x4_export_h`, `squeeze_updstate_avx2x4_export_h` |

Every procedure behind these entry points (add-state, dump-state, the
streaming steps, the sub-reads and sub-writes) has its own contract too. Each
procedure has a Hoare contract (`_h`) and a losslessness lemma (`_ll`); most
also have their combination as a total-correctness `phoare` (`_ph`). The
contracts are stated against the specification: an absorb takes a state that
has absorbed a list `l` (`pabsorb_spec`) to the state that has absorbed `l`
followed by the buffer, or, with a trail byte, to `ABSORB1600`; a squeeze
writes `SQUEEZE1600` and returns the permuted state; the streaming procedures
preserve `absorbing_spec` / `squeezing_spec` on the state and its status word.

### Permutations

| Permutation | Source (`src/amd64/`) | Proof | Main lemma |
| --- | --- | --- | --- |
| ref | `ref/keccakf1600_ref.jinc` | `ref/Keccakf1600_ref.ec` | `keccakf1600_ref_h` |
| basic | `ref/keccakf1600_basic.jinc` | `ref/Keccakf1600_basic.ec` | `keccakf1600_basic_h` |
| opt | `ref/keccakf1600_opt.jinc` | `ref/Keccakf1600_opt.ec` | `keccakf1600_opt_h` |
| avx2 | `avx2/keccakf1600.jinc` | `avx2/Keccakf1600_avx2.ec` | `keccakf1600_avx2_h`, `keccakf1600_st25_avx2_h` |
| 1-way dispatcher `_keccakf1600` | `ref/keccakf1600.jinc` | `ref/Keccakf1600.ec` | `keccakf1600_h` |
| 4-way ref | `avx2/keccakf1600x4_ref.jinc` | `avx2/Keccakf1600_avx2x4_ref.ec` | `keccakf1600_avx2x4_ref_h` |
| 4-way nat | `avx2/keccakf1600x4_nat.jinc` | `avx2/Keccakf1600_avx2x4_nat.ec` | `keccakf1600_avx2x4_nat_h` |
| 4-way alt | `avx2/keccakf1600x4_alt.jinc` | `avx2/Keccakf1600_avx2x4_alt.ec` | `keccakf1600_avx2x4_alt_h` |
| 4-way dispatcher `_keccakf1600_avx2x4` | `avx2/keccakf1600x4.jinc` | `avx2/Keccakf1600_avx2x4.ec` | `keccakf1600_avx2x4_h` |

Each states that the procedure computes `keccak_f1600_op` (4-way: on each of
the four lanes). The dispatchers select the implementation through the
`KECCAK_PERMUTATION` parameter; their lemmas hold for every choice. The
permutation proofs use EasyCrypt's `circuit` tactic.

## Layout

| Path | Content |
| --- | --- |
| `extracted/` | The models: `Keccak1600_Jazz.ec` (module `M`: memory variants and everything that does not depend on the array size, from `toEC_keccak1600.jazz`) and `Keccak1600_Jazz_ASIZE.ec` (array variants at the dummy size `_ASIZE = 999`, from `toEC_keccak1600_ASIZE.jazz`); the `*_checkXtr.ec` sanity checks; per-implementation wrappers, also used by the constant-time checks (`make -C extracted ct`). |
| `common/Keccak1600_statebytes.ec` | Byte view of the 25-lane state and its additive updates, shared by all fixed-size proofs. |
| `common/Keccak1600_subreadwrite.ec` | Sub-reads and sub-writes of memory and arrays (theory `ReadWriteArray` for the array ones). |
| `common/Keccak1600_updstate.ec`, `Keccak1600_updstate_finish.ec` | Streaming state: status word, `absorbing_spec` / `squeezing_spec`; finish and status export. |
| `common/keccak_bindings.ec`, `avx2.spec` | `circuit` bindings for machine words, and semantics of the AVX2 instructions the default spec lacks. |
| `ref/Keccak1600_ref.ec` | Specification side of the 1-way state (`absorb_spec_ref`, `pabsorb_spec_ref`), state init and rate bit. |
| `ref/Keccakf1600*.ec` | 1-way scalar permutations and the dispatcher. |
| `ref/Keccak1600_fixedsizes_ref.ec`, `ref/Keccak1600_updstate_ref.ec` | ref fixed-size and streaming procedures. |
| `avx2/Keccak1600_avx2.ec`, `avx2/Keccak1600_avx2x4.ec` | AVX2 state layout (`u256[7]`) and the 4-way state (lanes, pack, unpack), related to the 25-lane state. |
| `avx2/Keccakf1600_avx2*.ec` | AVX2 and 4-way permutations and the 4-way dispatcher. |
| `avx2/Keccak1600_fixedsizes_avx2{,x4}.ec`, `avx2/Keccak1600_updstate_avx2x4.ec` | AVX2 and 4-way fixed-size and streaming procedures. |
| `avx2/Avx2_extra.ec`, `kck_bindings.ec`, `kck_abs_bindings.ec` | `circuit` bindings for AVX2 words and arrays. |

## Array variants

The array procedures are extracted once, at the dummy size `_ASIZE = 999`.
Each array layer is an abstract theory parametrised by the size (`op
_ASIZE`, `clone PolyArray as A`, `clone WArray as WA`), whose module `MM` is
a copy of the procedures with `Array999`/`WArray999` replaced by `A`/`WA`,
followed by their contracts and proofs:

| Theory | File | Sanity check |
| --- | --- | --- |
| `ReadWriteArray` | `common/Keccak1600_subreadwrite.ec` | `extracted/Keccak1600_subreadwrite_checkXtr.ec` |
| `KeccakArrayRef` | `ref/Keccak1600_fixedsizes_ref.ec` | `extracted/Keccak1600_fixedsizes_ref_checkXtr.ec` |
| `KeccakUpdstateRef` | `ref/Keccak1600_updstate_ref.ec` | `extracted/Keccak1600_updstate_ref_checkXtr.ec` |
| `KeccakArrayAvx2` | `avx2/Keccak1600_fixedsizes_avx2.ec` | `extracted/Keccak1600_fixedsizes_avx2_checkXtr.ec` |
| `KeccakArrayAvx2x4` | `avx2/Keccak1600_fixedsizes_avx2x4.ec` | `extracted/Keccak1600_fixedsizes_avx2x4_checkXtr.ec` |
| `KeccakUpdstateAvx2x4` | `avx2/Keccak1600_updstate_avx2x4.ec` | `extracted/Keccak1600_updstate_avx2x4_checkXtr.ec` |

Each sanity check instantiates its theory at 999 and proves `M.f ~ MM.f :
={arg} ==> ={res}` by `sim` for every procedure, which shows that `MM` is
the code that was extracted. A client using a given array size follows the
same steps: clone the theory at that size, prove its own extracted procedure
equivalent to `MM.f` by `sim`, and transfer the contract. The `MM` blocks are
maintained by hand; `scripts/asize_transform.py --model old --theory <preset>
--mm-only` produces a starting point from the extraction.

## Checking

From the repository root:

```
make -C proof/amd64/extracted re_extract      # regenerate the models
make -C proof/amd64/extracted checkXtr        # the sanity checks
easycrypt runtest config/tests.config keccak_amd64_<x>   # <x>: extracted, common, ref, avx2
make check                                    # re-extract all models, then check this tree
```

CI runs the extraction check (the regenerated models must equal the
committed ones, up to whitespace) and the four scenarios. The toolchain,
pinned in `shell.nix`, is described in the top-level `README.md`
(*Toolchain*). The specification comes from the `crypto-specs` submodule
(`git submodule update --init`).
