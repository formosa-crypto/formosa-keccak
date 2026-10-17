# proof/amd64-barray — WIP port to the `barray` array model

Replica of `proof/amd64` for code extracted with
`jasmin2ec --array-model=barray` (monomorphic byte arrays `BArrayN`,
`SBArrayB_S` sub-array theories) instead of the deprecated `old` model.

`safety/` holds the safety proofs, extracted with `jasmin2ec -m safety` in the
same array model (see `safety/README.md`).

## Status

| Layer | State |
|---|---|
| `extracted/` (models, generated array theories) | done; reproducible with the CI Jasmin (`git diff -w`) |
| parametric `MM` modules of the six abstract theories | regenerated from the barray ASIZE model |
| statements (ops, types, contracts) of every file | ported; every file elaborates |
| `extracted/*_checkXtr.ec` | **green** (`make -C extracted checkXtr`) |
| bridge lemmas, `common/Keccak1600_barrays.ec` | **done**, fully checked |
| proofs of `ref/Keccak1600_ref.ec` | **ported**, fully checked |
| proofs of `common/Keccak1600_subreadwrite.ec` | **ported**, fully checked, no admits |
| proofs of `ref/Keccak1600_fixedsizes_ref.ec` | **ported**, fully checked, no admits |
| proofs of `ref/Keccakf1600_ref.ec` | **ported**, fully checked, no admits |
| proofs of `common/Keccak1600_updstate{,_finish}.ec`, `ref/Keccak1600_updstate_ref.ec` | **ported**, fully checked, no admits |
| proofs of `avx2/Keccak1600_avx2.ec`, `avx2/Keccak1600_fixedsizes_avx2.ec` | **ported**, fully checked, no admits |
| proofs of `avx2/Keccak1600_avx2x4.ec`, `avx2/Keccakf1600_avx2x4.ec` (dispatcher), `avx2/Keccak1600_{fixedsizes,updstate}_avx2x4.ec` | **ported**, fully checked, no admits |
| permutation proofs (`ref/Keccakf1600_{basic,opt}.ec`, `avx2/Keccakf1600_avx2.ec`, `avx2/Keccakf1600_avx2x4_{ref,nat,alt}.ec`) | **ported**, fully checked, no admits |
| `circuit` over BArray | **done**: `common/barray_abs_bindings.ec`, `common/keccak_barray_bindings.ec` (needs an EasyCrypt with the `uextract`/`uinsert`/`oflist` operator kinds) |

EasyCrypt loads `require`d files with proof checking off, so the checkXtr
files only need the statements of their dependencies.

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

## Next steps

1. Upstream the EasyCrypt operator kinds `uextract`, `uinsert` and `oflist`
   (`shell.nix` follows EasyCrypt `main`, which does not have them yet).
