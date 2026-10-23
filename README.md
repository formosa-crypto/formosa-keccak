# formosa-keccak
Implementation of Keccak and related functions (SHA3, SHAKE, etc.)


## Caution! Work in progres...


## Toolchain

`shell.nix` pins the toolchain, and CI runs everything inside it
(`nix-shell`):

| Tool | Version |
| --- | --- |
| Jasmin: `jasminc`, `jasmin-ct`, `jasmin2ec`, and its EasyCrypt library (eclib) | the `safety-assert2` branch, not a release: commit `c1cae60e` of the `jasmin-compiler` repository (GitLab), generated from `1e7479a2` of `jasmin` (GitHub); both were the branch head on 2026-10-23 |
| EasyCrypt | `main`, at its head when the shell is built (not pinned) |
| SMT solvers | Z3 4.13.4, CVC5 1.3.2 (the `easycrypt.project` files ask for `Z3@4.13`, `CVC5@1.3`) |
| bitwuzla-cxx, for EasyCrypt's `circuit` tactic | 0.9.0 (with 0.8.2 the permutation proofs are over 10× slower) |
| FIPS 202 specification | submodule `submodules/crypto-specs` |

What each proof tree needs:

| Tree | `jasmin2ec` | Jasmin eclib | EasyCrypt |
| --- | --- | --- | --- |
| `proof/amd64`: correctness, old array model | release 2026.03.1 or the snapshot | the snapshot or 2026.03.1 ¹ | `main` |
| `proof/amd64-barray`: correctness, `barray` model | release 2026.03.1 or the snapshot | the snapshot or 2026.03.1 ¹ | `main`, plus an unmerged patch for the permutation proofs and five of the sanity checks ² |
| `proof/amd64-barray/safety`: safety | the snapshot only (`-m safety`) | the snapshot only (`JSafety.ec`) | `main` |

- The committed correctness models were extracted with release 2026.03.1.
  CI re-extracts them with the snapshot and requires the same files up to
  whitespace (`git diff -w`).
- ¹ CI checks the proofs against the snapshot's eclib only. For the
  correctness proofs the two eclibs differ only in the shift count of
  `VPSLL`/`VPSRL`/`VPSRA` (the snapshot takes the whole 128-bit count,
  2026.03.1 its low 64 bits); the rest of the difference is additions for
  the safety proofs. The files that depend on these shifts
  (`common/Keccak1600_subreadwrite.ec`, `common/keccak_bindings.ec` and
  `avx2/kck_bindings.ec`, in both trees) also check against the 2026.03.1
  eclib (2026-10-23). The full trees have not been run against it.
- ² The `bind op` kinds `uextract`, `uinsert` and `oflist`; see
  `proof/amd64-barray/README.md` and `proof/amd64-barray/Notes.md`, §3.3.
  CI cannot check these files until the patch is in EasyCrypt.

Without nix: install a Jasmin built from the `safety-assert2` branch,
EasyCrypt and the provers, run `easycrypt why3config`, initialise
`submodules/crypto-specs`, and point EasyCrypt to that Jasmin's eclib, e.g.
for an opam switch:

```
export EC_RDIRS="Jasmin:$(opam var lib)/easycrypt/jasmin"
```

`submodules/jasmin`, which the `easycrypt.project` files name, is not the
pinned Jasmin, and CI does not use it.
