# Safety proofs (amd64)

This directory proves that the Jasmin implementations in `src/amd64` are
**safe**: every array and memory access is in bounds, no array cell is read
before it is written, no `ui64` arithmetic overflows, and every function meets
the safety contract (`#[safety = { requires, res, ensures }]`) attached to it in
the sources. All implementations are covered: `ref`, `avx2` and `avx2x4`, with
their memory and array (`_ASIZE`) variants, fixed-size absorb/squeeze and the
streaming (`updstate`) API, and every Keccak-f[1600] permutation (ref, basic,
opt, avx2; 4-way ref, alt, nat).

## Status

The extraction, the array theories and the sanity checks are complete and
checked in CI (scenario `keccak_safety_amd64_extracted`). The proofs are work
in progress: the proof files are generated but do not all check yet (a known
open point is the loop body of the `opt` permutation), so CI does not run the
`common`, `ref`, `avx2` and `avx2x4` scenarios yet.

## Toolchain

The models are produced by `jasmin2ec -m safety`, which is only available on
the `safety-assert2` branch of Jasmin (pinned in `shell.nix`). Its eclib also
provides `JSafety.ec`.

## Extraction: same strategy as the correctness proofs

The extraction follows the pattern of `proof/amd64-barray`:

* **Memory variants** (and everything that does not depend on the array
  size: permutations, helpers, memory absorb/squeeze, streaming API) are
  extracted directly: `extracted/Keccak1600_Jazz_safety.ec`, module `M`
  (`make -C extracted re_extract_mem`, from `toEC_keccak1600.jazz`).
* **Array variants** are extracted under the dummy size `_ASIZE = 999`:
  `extracted/Keccak1600_Jazz_ASIZE_safety.ec` (`make -C extracted
  re_extract_array`, from `toEC_keccak1600_ASIZE.jazz`). This extraction is
  abstracted over the size by textual manipulation
  (`scripts/asize_transform.py --safety`): each layer becomes an abstract
  theory, parametrised by the array (`op _ASIZE`, `clone ByteArray as A`),
  whose module `MM` holds the abstracted procedures (`BArray999` -> `A`,
  `999` -> `_ASIZE`; callees of other layers taken from `RW.MM`, callees that
  do not depend on the size taken from the memory extraction's `M`), followed
  by their safety specifications restated over `MM`, and by the proofs. The
  layers mirror the correctness theories:

  | Theory | File | Procedures |
  | --- | --- | --- |
  | `ReadWriteArraySafety` | `common/Keccak1600_common_safety.ec` | array sub-reads/sub-writes |
  | `KeccakArrayRefSafety` | `ref/Keccak1600_safety.ec` | ref fixed-size array absorb/squeeze |
  | `KeccakUpdstateRefSafety` | `ref/Keccak1600_safety.ec` | ref array streaming API |
  | `KeccakArrayAvx2Safety` | `avx2/Keccak1600_avx2_safety.ec` | avx2 fixed-size array absorb/squeeze |
  | `KeccakArrayAvx2x4Safety` | `avx2x4/Keccak1600x4_safety.ec` | 4-way fixed-size array absorb/squeeze |
  | `KeccakUpdstateAvx2x4Safety` | `avx2x4/Keccak1600x4_safety.ec` | 4-way array streaming API |

  The theories other than `ReadWriteArraySafety` clone it as `RW`.
* **Sanity checks**: `extracted/<layer>_checkXtr.ec` instantiates each theory
  at `_ASIZE = 999`, `A = BArray999`, proves `M.f ~ MM.f : ={arg} ==> ={res}`
  by `sim` for each procedure of the layer, and transfers each safety lemma of
  the theory to the corresponding specification of the extraction
  (`conseq`). The transfer also checks that the specifications restated over
  `MM` are those of the extraction (`make -C extracted checkXtr`).
* **Client use** at a given size follows the same steps: clone the theory with
  the concrete array, prove the client's extracted procedure equivalent to
  `MM.f` by `sim`, and transfer the safety lemma with `conseq`.

## Layout

| Path | Content |
| --- | --- |
| `extracted/` | The two models, their array theories, the wrappers, the `*_checkXtr.ec` checks. |
| `common/Keccak1600_common_safety.ec` | Helpers: feature query, shifts, rho offsets, memory sub-reads/sub-writes, 4-way pack/unpack, status-word decoder; bitmap and word lemmas; theory `ReadWriteArraySafety`. |
| `ref/Keccakf1600_safety.ec` | 1-way permutations (ref, basic, opt, avx2) and the dispatcher `_keccakf1600`. |
| `ref/Keccak1600_safety.ec` | ref memory absorb/squeeze and streaming API; the two ref array theories. |
| `avx2/Keccak1600_avx2_safety.ec` | AVX2 state helpers, memory absorb/squeeze; the avx2 array theory. |
| `avx2x4/Keccakf1600x4_safety.ec` | 4-way permutations (ref, alt, nat), dispatcher, 4-way state init and rate bit. |
| `avx2x4/Keccak1600x4_safety.ec` | 4-way memory absorb/squeeze and streaming API; the two 4-way array theories. |
| `gen/` | The generator of the proof files and of the `*_checkXtr.ec` files. |

Check with `easycrypt runtest config/tests.config keccak_safety_amd64_<x>`,
for `<x>` in `extracted`, `common`, `ref`, `avx2`, `avx2x4`.

## How the models and the specifications look

In the models every procedure returns, besides its results, a *trace*: the
list of the safety conditions met along the execution (bounds of each array or
memory access, initialisation of each array read, range of each `ui64`
operation, the callee contracts). For each procedure `f` the extraction
defines

```
op f_spec args = hoare [M.f : args = ... /\ requires ==> ensures /\ valid res.`trace]
```

where `requires`/`ensures` come from the contract of `f` (a function without
contract gets the default one: its array arguments are fully initialised on
entry and on exit). Array initialisation is tracked by byte bitmaps `b_x`
(`BArrayN.is_init b_x k l`), and memory validity by `is_valid ptr_modulus
Glob.mem_v p l`. The lemma `f_proof` proves `f_spec` (about `M.f`, or about
`MM.f` inside an array theory).

## How the proofs are produced

The proof files and the checks are generated: do not edit them, edit
`gen/cfg_<layer>.py` and rerun it (e.g. `python3 gen/cfg_ref.py`). The
generator (`gen/gen.py`) parses the models and builds a proof script for each
procedure:

* the pure helpers (`__HAS_FEATURE`, `__KECCAK_F`, the shifts,
  `__stavx2_pos_avx2`, ...) are inlined;
* conditionals are split forward (`sp n; if`): this version of EasyCrypt's
  `sp` executes through conditionals, and `wp` over a sequence of
  conditionals blows up the goal;
* straight-line code is closed backward, calls through the callee lemma
  (`wp; ecall (g_proof args)`, `RW.g_proof` for a subreadwrite callee of an
  array theory), and the remaining goal by a fixed closer
  (`rewrite /is_init /valid /=; ...; smt(...)`);
* the only manual input is given in `gen/cfg_*.py`, as formulas over the
  program and lemma variables: loop invariants `INV<k>` (k-th `while` of the
  procedure), cuts `CUT<k>` (state before the k-th conditional, when calls
  precede it) and `BEFORE<k>` (state before the k-th call, to split long
  call chains), and extra `smt` hints (`SMT`). For the array procedures they
  are written for the 999 extraction and abstracted like the code. A few
  procedures with word-level reasoning have hand-written proofs
  (`gen/common_manual.json`).

The absorb and squeeze code of the avx2 implementation reads and writes the
state through a cascade of fixed-length sub-reads (resp. sub-writes) at fixed
positions. `gen/cascade.py` describes the state reached after the cascade has
processed the state up to byte `c` (`J c`: position, remaining length, trail
byte and pointer; `W k`: bytes written so far), and each cut is one of these.

After changing a contract or an implementation: re-extract (`make -C
extracted`), regenerate every layer, and rerun the checks. The annotations are
keyed by loop/conditional/call ordinals, so they survive changes to the
assertions, but not to the control structure of a procedure.

## Notes on the contracts

* The extractor adds, for every `ui64` subterm of an `ensures`, an unguarded
  range condition. The fixed-length memory sub-reads therefore state the
  pointer advance as `final_buf - buf == (...)` with the case analysis inside
  the right-hand side, so that this condition always holds.
* The fixed-length sub-reads require the whole remaining input
  (`is_mem_init(buf, LEN)`, resp. `is_arr_init(buf, offset+DELTA, min(LEN, W))`),
  which their callers always have.
