# proof/amd64-barray — functional correctness and safety (`barray` model)

This tree proves, for the Keccak implementations in `src/amd64` extracted
with `jasmin2ec --array-model=barray` (Jasmin's default model: monomorphic
byte arrays `BArrayN`, sub-arrays through `SBArrayB_S` theories):

- **functional correctness** against the FIPS 202 specification of
  `submodules/crypto-specs/fips202`: the same results as `proof/amd64`, with
  the same file, theory and lemma names (this tree started as its replica);
- **safety**, in `safety/` (see `safety/README.md`): every array and memory
  access in bounds, no read of an uninitialised array cell, no `ui64`
  overflow, and every `#[safety]` contract of the sources met.

There are no admits. `Notes.md` records the design of the port and the
issues met on the way.

## What is proved

C: functional correctness (this directory). S: safety (`safety/`).

| Implementation | Fixed-size, memory | Fixed-size, array | Streaming, memory | Streaming, array |
| --- | --- | --- | --- | --- |
| `ref` (1-way, `u64[25]` state) | C S | C S | C S | C S |
| `avx2` (1-way, `u256[7]` state) | C S | C S | as `ref` ¹ | as `ref` ¹ |
| `avx2x4` (4-way, `u256[25]` state) | C S ² | C S ² | C S ² | C S ² |

1. The 1-way streaming API has a single implementation,
   `src/amd64/ref/keccak1600_updstate{,_ASIZE}.jinc`, whose whole-lane loops
   branch on `KECCAK_FEATURES` (AVX2 or scalar). Both branches are proved.
2. Absorb with four buffers, and with one buffer broadcast to the four lanes
   (`bcast`).

| Cell | Correctness: file (theory) | Safety: file (theory) |
| --- | --- | --- |
| ref fixed-size, memory | `ref/Keccak1600_fixedsizes_ref.ec` | `safety/ref/Keccak1600_safety.ec` |
| ref fixed-size, array | same (`KeccakArrayRef`) | same (`KeccakArrayRefSafety`) |
| ref streaming, memory | `ref/Keccak1600_updstate_ref.ec` | `safety/ref/Keccak1600_safety.ec` |
| ref streaming, array | same (`KeccakUpdstateRef`) | same (`KeccakUpdstateRefSafety`) |
| avx2 fixed-size, memory | `avx2/Keccak1600_fixedsizes_avx2.ec` | `safety/avx2/Keccak1600_avx2_safety.ec` |
| avx2 fixed-size, array | same (`KeccakArrayAvx2`) | same (`KeccakArrayAvx2Safety`) |
| avx2x4 fixed-size, memory | `avx2/Keccak1600_fixedsizes_avx2x4.ec` | `safety/avx2x4/Keccak1600x4_safety.ec` |
| avx2x4 fixed-size, array | same (`KeccakArrayAvx2x4`) | same (`KeccakArrayAvx2x4Safety`) |
| avx2x4 streaming, memory | `avx2/Keccak1600_updstate_avx2x4.ec` | `safety/avx2x4/Keccak1600x4_safety.ec` |
| avx2x4 streaming, array | same (`KeccakUpdstateAvx2x4`) | same (`KeccakUpdstateAvx2x4Safety`) |
| sub-reads and sub-writes | `common/Keccak1600_subreadwrite.ec` (`ReadWriteArray`) | `safety/common/Keccak1600_common_safety.ec` (`ReadWriteArraySafety`) |

The main correctness lemmas of each cell are listed in
`proof/amd64/README.md`; every procedure behind them has its own contract,
with a Hoare contract (`_h`), a losslessness lemma (`_ll`) and mostly a
`phoare` (`_ph`). Here the contracts are stated through views of the byte
arrays (`st25`, `stavx2`, `st4x`; see *Conventions*). On the safety side,
every procedure `f` of the two safety models has a lemma `f_proof` proving
the specification `f_spec` that the extraction derives from its contract.

### Permutations

| Permutation | Correctness | Safety |
| --- | --- | --- |
| ref, basic, opt, 1-way dispatcher `_keccakf1600` | `ref/Keccakf1600_{ref,basic,opt}.ec`, `ref/Keccakf1600.ec` | `safety/ref/Keccakf1600_safety.ec` |
| avx2 | `avx2/Keccakf1600_avx2.ec` | `safety/ref/Keccakf1600_safety.ec` |
| 4-way ref, nat, alt, 4-way dispatcher `_keccakf1600_avx2x4` | `avx2/Keccakf1600_avx2x4_{ref,nat,alt}.ec`, `avx2/Keccakf1600_avx2x4.ec` | `safety/avx2x4/Keccakf1600x4_safety.ec` |

The correctness lemmas state that the procedure computes `keccak_f1600_op`
(4-way: on each lane) and hold for every choice of `KECCAK_PERMUTATION`.
They use EasyCrypt's `circuit` tactic, which here needs the bindings of
byte arrays described in *Circuit bindings*.

## Layout

| Path | Content |
| --- | --- |
| `extracted/` | The models `Keccak1600_Jazz.ec` (module `M`: memory variants and everything independent of the array size) and `Keccak1600_Jazz_ASIZE.ec` (array variants at the dummy size `_ASIZE = 999`; `toEC_keccak1600_ASIZE.jazz` reuses `toEC_keccak1600.jazz`); the `*_checkXtr.ec` sanity checks. |
| `common/Keccak1600_barrays.ec` | The views between the byte arrays and the specification states, and the bridge lemmas (see below). |
| `common/barray_abs_bindings.ec`, `keccak_barray_bindings.ec` | `circuit` bindings of the byte arrays (see below). |
| `common/Keccak1600_statebytes.ec`, `Keccak1600_subreadwrite.ec`, `Keccak1600_updstate{,_finish}.ec`, `keccak_bindings.ec`, `avx2.spec` | As in `proof/amd64`: state bytes, sub-reads and sub-writes, streaming state, word bindings, AVX2 instruction semantics. |
| `ref/`, `avx2/` | The same files as in `proof/amd64` (see its README). |
| `safety/` | The safety proofs: models, generated proof files, generator. |
| `Notes.md` | Design rationale of the port, the EasyCrypt patch, issues, limitations. |

## Array variants

As in `proof/amd64`, each array layer is an abstract theory parametrised by
the size, whose module `MM` is the extracted code with `BArray999` replaced
by the parameter, and whose sanity check in `extracted/` instantiates it at
999 and proves `M.f ~ MM.f` by `sim`. Here the parameter is a single
`clone ByteArray as A` (no word view), named `BA` in `KeccakUpdstateAvx2x4`
(see *Conventions*). The safety theories follow the same pattern, with their
own sanity checks in `safety/extracted/`.

## Checking

From the repository root:

```
make -C proof/amd64-barray/extracted re_extract      # regenerate the models
make -C proof/amd64-barray/extracted checkXtr        # the sanity checks
easycrypt runtest config/tests.config keccak_amd64barray_<x>   # <x>: extracted, common, ref, avx2
```

and, for the safety proofs, the scenarios `keccak_amd64barray_safety_<x>`
(see `safety/README.md`).

The permutation proofs, and every file that requires
`common/keccak_barray_bindings.ec` (five of the six sanity checks do,
through their dependencies), need an EasyCrypt whose `bind op` has the
operator kinds `uextract`, `uinsert` and `oflist` (see `Notes.md`, §3.3).
These are not in EasyCrypt's `main` branch yet, which `shell.nix` follows,
so with the pinned toolchain those files fail to load. CI therefore runs the
extraction check of the models, the scenario `keccak_amd64barray_extracted`
(which fails until the EasyCrypt patch is available), and the safety
scenarios (which do not need it). The safety proofs need no `circuit`.
The rest of the toolchain is described in the top-level `README.md`
(*Toolchain*).

EasyCrypt loads `require`d files with proof checking off, so a sanity check
only needs the statements of its dependencies to elaborate.

## Conventions

- Contracts over extracted procedures go through view ops
  (`common/Keccak1600_barrays.ec`), e.g.
  `st25 st = _st ==> st25 res.`1 = addstate_at _st _at l`.
  Views: `st25` (BArray200 → state), `st5` (BArray40), `stavx2` (BArray224 →
  `W256.t Array7.t`), `st4x` (BArray800 → state4x), `st4x_get`,
  `ust_state`/`ust_status` (BArray208), `ust_st4x`/`ust4x_status` (BArray808).
  Inverse views: `st200` (state → BArray200), `stavx2_of` (Array7 → BArray224),
  `st4x_of` (state4x → BArray800).
- The Array25-level lane accessor of the old `Keccak1600_avx2x4.ec` is renamed
  `st4x_lane` (the name `st4x_get` is the BArray800 view).
- The abstract theories clone `ByteArray as A` (single clone, no `WA`);
  checkXtr instantiates `theory A <- BArray999`. Exception:
  `KeccakUpdstateAvx2x4` names it `BA` (after `import RW.`, `A` would resolve
  to the nested `FX.RW.A`, which lost its type `t` in the two-level theory
  substitution).
- `toEC_keccak1600_ASIZE.jazz` reuses `toEC_keccak1600.jazz`, so both models
  share the dispatcher constants and the 4-way checkXtr files need no
  `circuit` bridge.

## Bridge lemmas (`common/Keccak1600_barrays.ec`)

State bridges are stated in byte-offset (`d`) form, because `/>` and `/=`
normalise `BArray200.set64 st 24` to `set64d st 192`; word-index forms are
corollaries.

- `BAExtra` (cloned as `BX40 BX200 BX208 BX224 BX800 BX808`): `uNbytes_getNd`
  (word = bytes it covers), `setNd_fill`, `get64d_get256d`.
- BArray200 and the state: `get8_st200`, `stbytes_st25` (the byte-view pivots),
  `st25K`, `st200K`, injectivity, `st25_set64d`, `st25_set256d`,
  `bytes2state_to_list`, `to_list_st25`, `sub_st25`.
- Stores and loads: `set{64,128,256}d_addstate_at` (and `'` variants for the
  `t ^ get` operand order), `set8d_addratebit`, `u{64,128,256}bytes_getNd_st25`.
- AVX2 and 4-way views: `stavx2_set256d`, `stavx2_xor256d`, `stavx2_inj`,
  `stavx2_of` with `stavx2K`/`stavx2_ofK` and the simplification hint
  `get256d_stavx2_of`, `st4x_set256d`, `st4x_inj`, `st4x_of` with
  `st4xK`/`st4x_ofK` and the hints `get256d_st4x_of`/`get64d_st4x_of`/`st4x_ofK`,
  `st4x_getE`,
  `st4x_get_set64d`, `st4x_get_xor64d`; updstate views over the sub-array ops.

## Porting recipe for proof scripts

- In proof blocks, the program state `st` (with or without a memory tag) is
  always used as a spec state: write `(st25 st)`.
- `|>` now eliminates the spec variable `_st` (from `st25 st = _st`) instead of
  the program variable, so explicit instantiations use `(st25 st{m})`, and an
  intro list may need one more `?`.
- An invariant conjunct `st25 st = e` is no longer substituted: it becomes a
  hypothesis (`Hst`), used with `rewrite Hst`.
- After a call whose postcondition is `st25 res = f ...`, the goal keeps
  `forall r, st25 r = f ... =>`; add `? ->` (or `r Er; rewrite Er`).
- Loop-entry goals need the memory named in the intro (`&hr`).
- Dump proofs: rather than wrapping, switch the precondition to
  `st = st200 _st` with `conseq` (`st25K`); `|>` then substitutes the program
  state as before, and `get{64,128,256}d_st200` turn reads back into the old
  `getN_direct (stbytes _st) o` terms, so the old scripts apply.
- Offsets are normalised by `/>` and `/=` (`8*25` becomes `200`, `8*0` becomes
  `0`): bridge lemmas over sub-arrays take the offset as a variable with an
  `o = 0` premise, and status-word lemmas are stated at `200`.
- AVX2 dumps: the same trick with `st = stavx2_of _st` (`stavx2K`); the hint
  `get256d_stavx2_of` turns `get256 (stavx2_of _st) k` back into `_st.[k]`, so
  the old `dump_avx2_w*` applications are unchanged.
- `circuit` handles BArray terms once `Keccak_barray_bindings` is required
  (see *Circuit bindings* below), so `proc; circuit` proofs carry over
  unchanged. Outside `circuit`, lift the stores to the views first
  (`st25_xor0`, `stavx2_xor256d`, `st4x_xor0`), generalise the view
  (`move: (stavx2 _st) => S`), and keep the invariant as a goal premise
  (introduce it with `[#]`, not `/>`, which splits it).
- Round constants: the program reads `BArray192.get64 kECCAK1600_RC i`;
  `kECCAK1600_RC_E` (in `ref/Keccakf1600_ref.ec`) turns it into `rc_spec.[i]`
  for `0 <= i < 24`. When `/>` has already normalised the offset (`8*0` to `0`),
  instantiate it first (`have K0 := kECCAK1600_RC_E 0 _`), or use the
  offset form `kECCAK1600_RC_Ed` (in `avx2/Keccakf1600_avx2x4_alt.ec`).
  Invariants `rC = rc_spec` become `rC = kECCAK1600_RC`. Unlike `Array24`,
  the out-of-range read is not `witness`, so a contract that may read entry
  24 needs the bound (e.g. `0 <= to_uint c < 23` in `Keccakf1600_opt.ec`).
- 4-way contracts (`st4x st = _st`): a `conseq` right after `proc` switches the
  precondition to `st = st4x_of _st`, so `|>` substitutes the program state and
  every explicit `_st` of the old scripts stays valid. Invariants `st = _st`
  become `st = st4x_of _st`; other state positions are wrapped as `(st4x st)`.
  The lane lemmas of `Keccak1600_fixedsizes_avx2x4.ec` (`st4x_get_xor64x4`,
  `st4x_get_xorbcast256`, `get{64,256}_init256_at`) are restated over BArray800
  with byte offsets as premises.
- 4-way updstate: the BArray808 helpers (`A25u256toA101u64E`, `A101_xor256`,
  `A101_clear`, `A101_set800`, `A25_set64d_800`) are proved byte-wise from
  `A25_get8`. The key state `stk : BArray800.t` is wrapped as `(st4x stk)`; when
  a later rewrite reintroduces `st4x stk`, keep its invariant as a named
  hypothesis instead of consuming it with `->`.
- Old store lemmas `set{64,128,256}_addstate_at` / `setw_addstate_at` become
  `set{64,128,256}d_addstate_at`; dump-side words are `getNd st{m} o`, related
  to the spec byte view by `u{64,128,256}bytes_get{64,128,256}d_st25`.

## Regenerating

```
make -C proof/amd64-barray/extracted re_extract
python3 scripts/asize_transform.py --theory <preset> [--array-name BA] --mm-only \
    proof/amd64-barray/extracted/Keccak1600_Jazz_ASIZE.ec -o MM.ec
```
Presets: `subreadwrite fixedsizes_ref updstate_ref fixedsizes_avx2
fixedsizes_avx2x4 updstate_avx2x4` (the last one with `--array-name BA`).

## Circuit bindings

`circuit` sees a byte array `BArrayN.t` as a bitstring of `8*N` bits (byte
`i` at bits `8*i .. 8*i+7`).

- `common/barray_abs_bindings.ec`: abstract theories, proved once.
  - `BArrayBS` binds a `ByteArray` (`bind bitstring`, `get8` as `aextract`,
    `set8`/`set8d` as `uinsert`). Its nested `GetSet16` .. `GetSet256` bind the
    word accessors `getKd`/`setKd` (`uextract`/`uinsert`, unit `W8`, so the
    offsets are in bytes as in the extraction) and the constant tables
    `of_listK` (`oflist`).
  - `SubBArrayBS` binds `get_sub`/`set_sub` of a `SubByteArray`.
- `common/keccak_barray_bindings.ec`: the instances for every size used here,
  `ArrayN.init` as `painit`, and the views `st25`, `st5`, `stavx2`, `st4x`
  (and `st200`, `stavx2_of`, `st4x_of`) as `b2a`/`a2b`, so `circuit` does not
  unfold them. Add a clone line when the extraction starts using a new
  (array size, word size) pair.

The word bitstring bindings come from `common/keccak_bindings.ec`.

## Open issue

Upstream the EasyCrypt operator kinds `uextract`, `uinsert` and `oflist`
(or pin a branch that has them in `shell.nix`), so that CI can check the
permutation proofs and the sanity checks of this tree, and add the scenarios
`keccak_amd64barray_{common,ref,avx2}` to the workflow.
