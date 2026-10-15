# proof/amd64-barray — WIP port to the `barray` array model

Replica of `proof/amd64` (without `safety/`) for code extracted with
`jasmin2ec --array-model=barray` (monomorphic byte arrays `BArrayN`,
`SBArrayB_S` sub-array theories) instead of the deprecated `old` model.

## Status

| Layer | State |
|---|---|
| `extracted/` (models, generated array theories) | done; reproducible with the CI Jasmin (`git diff -w`) |
| parametric `MM` modules of the six abstract theories | regenerated from the barray ASIZE model |
| statements (ops, types, contracts) of every file | ported; every file elaborates |
| `extracted/*_checkXtr.ec` | **green** (`make -C extracted checkXtr`) |
| proof scripts in `common/ ref/ avx2/` | **not yet ported** — compiling these files directly fails |
| `circuit` over BArray | not investigated (permutation proofs) |

EasyCrypt loads `require`d files with proof checking off, so the checkXtr
files only need the statements of their dependencies.

## Conventions

- Contracts over extracted procedures go through view ops
  (`common/Keccak1600_barrays.ec`), e.g.
  `st25 st = _st ==> st25 res.`1 = addstate_at _st _at l`.
  Views: `st25` (BArray200 → state), `st5` (BArray40), `stavx2` (BArray224 →
  `W256.t Array7.t`), `st4x` (BArray800 → state4x), `st4x_get`,
  `ust_state`/`ust_status` (BArray208), `ust_st4x`/`ust4x_status` (BArray808).
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

## Regenerating

```
make -C proof/amd64-barray/extracted re_extract
python3 scripts/asize_transform.py --theory <preset> [--array-name BA] --mm-only \
    proof/amd64-barray/extracted/Keccak1600_Jazz_ASIZE.ec -o MM.ec
```
Presets: `subreadwrite fixedsizes_ref updstate_ref fixedsizes_avx2
fixedsizes_avx2x4 updstate_avx2x4` (the last one with `--array-name BA`).

## Next steps

1. Bridge lemmas in `common/Keccak1600_barrays.ec` (byte/word views,
   `setNd`/`getNd` ↔ `addstate_at`, `stbytes`, `sub`, `fill`).
2. Port proof scripts in dependency order: `ref/Keccak1600_ref.ec`,
   `common/Keccak1600_subreadwrite.ec` (array part), `ref/*`, updstate, avx2,
   avx2x4. Old-model helper lemmas over `WArray800`/`WArray200` round trips
   (e.g. `st4x_get_xor64x4`) are still present and should be replaced by
   BArray800 counterparts.
3. `circuit` bindings for BArray, then the permutation proofs.
