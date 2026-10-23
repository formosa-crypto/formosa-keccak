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

Every proof checks: all procedures of all layers, memory and array variants,
fixed-size and streaming. CI runs the extraction check and the scenarios
`keccak_amd64barray_safety_<x>` for `<x>` in `extracted`, `common`, `ref`,
`avx2`, `avx2x4`. Fresh compile times on a 10-core laptop (OCaml 5.4.1, two
files compiling at a time; `gen/profile.py` gives the breakdown):

| File | Time | Before the merge/closer work |
| --- | --- | --- |
| `common/Keccak1600_common_safety.ec` | 2.5 min | 9 min |
| `ref/Keccakf1600_safety.ec` | 14 s | 22 s |
| `ref/Keccak1600_safety.ec` | 3 min | 12 min |
| `avx2/Keccak1600_avx2_safety.ec` | 4 min | 80 min |
| `avx2x4/Keccakf1600x4_safety.ec` | 16 s | 22 min |
| `avx2x4/Keccak1600x4_safety.ec` | 10 min | 29 min |

What is left is in the 4-way absorb/squeeze file: fourteen closers of the
four-buffer add-state and streaming steps take 20–60 s each (440 s of its
560 s), because with four buffers in context every `smt` call costs about
0.5 s and their goals have 25–60 atoms. Shrinking the context those calls see
(step 4 of the plan behind this work) is the remaining lever.

## Toolchain

The models are produced by `jasmin2ec -m safety`, which is only available on
the `safety-assert2` branch of Jasmin (pinned in `shell.nix`). Its eclib also
provides `JSafety.ec`. The full toolchain, and what the other proof trees
need, is in the top-level `README.md` (*Toolchain*).

## Extraction: same strategy as the correctness proofs

The extraction follows the pattern of the correctness proofs of the enclosing
tree (`proof/amd64-barray`), whose `barray` array model it shares:

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

Check with `easycrypt runtest config/tests.config keccak_amd64barray_safety_<x>`,
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
* a conditional followed by a loop or by another conditional with calls is
  proved once, as a step `seq : (JOIN)` whose two branches are closed
  inside it, and the rest of the procedure continues once from `JOIN`
  (otherwise the rest would be proved once per branch, and a sequence of
  such conditionals once per path: the avx2 dump cascade had 200 closers
  for 9 conditionals). `JOIN` is the annotation `MERGE<k>` of the k-th
  conditional, or, when the next loop or conditional follows through
  assignments only, its own `INV<k>`/`CUT<k>`, which describes the same
  point. The generator prints on stderr the formula that would allow a
  further merge (`note: <proc>: a join formula ...`); the per-procedure
  option `MERGE` is `auto` (default), `all` (merge everywhere, missing
  formulas appear as `(* MISSING *)`) or `off`;
* straight-line code is closed backward, calls through the callee lemma
  (`wp; ecall (g_proof args)`, `RW.g_proof` for a subreadwrite callee of an
  array theory), and the remaining goal by a fixed closer: unfold `is_init`
  and `valid`, introduce, then split the conjunction two levels deep and
  call `smt` on each part (the full split, one `smt` call per atom, is the
  fallback: an `smt` call costs 0.2–0.6 s whatever its size, and a goal has
  typically 40–60 atoms, so this is 8–15× faster). The per-procedure option
  `SPLIT` gives the depths to try, default `(2, 'all')`;
* the only manual input is given in `gen/cfg_*.py`, as formulas over the
  program and lemma variables: loop invariants `INV<k>` (k-th `while` of the
  procedure), cuts `CUT<k>` (state before the k-th conditional, when calls
  precede it), joins `MERGE<k>` (state after the k-th conditional) and
  `BEFORE<k>` (state before the k-th call, to split long call chains), and
  extra `smt` hints (`SMT`). For the array procedures they are written for
  the 999 extraction and abstracted like the code. A few procedures with
  word-level reasoning have hand-written proofs (`gen/common_manual.json`).
  Two more options:
  * `STEPWP`, for long straight-line bodies (the permutation rounds): the
    proof reduces the projections of the result tuple right after `proc`, so
    that the word computations become irrelevant to the postcondition, then
    runs `wp` a few instructions at a time with `simplify` in between, so that
    they are dropped as they appear. A single `wp` followed by `/=` would
    substitute the whole chain of `let`s and blow up.
  * `SMT2`, a fallback hint list: the closer ends with `(smt(SMT) || smt(SMT2))`.
    With four buffers in context, `smt` can time out on the full hint list
    where a short one succeeds.

The absorb and squeeze code of the avx2 implementation reads and writes the
state through a cascade of fixed-length sub-reads (resp. sub-writes) at fixed
positions. `gen/cascade.py` describes the state reached after the cascade has
processed the state up to byte `c` (`J c`: position, remaining length, trail
byte and pointer; `W k`: bytes written so far), and each cut is one of these.

After changing a contract or an implementation: re-extract (`make -C
extracted`), regenerate every layer, and rerun the checks. The annotations are
keyed by loop/conditional/call ordinals, so they survive changes to the
assertions, but not to the control structure of a procedure.

`python3 gen/profile.py <file.ec>` compiles a proof file with EasyCrypt's
`-tstats` and reports where the time goes: per command kind, per lemma (with
its number of closers and conditionals), and the slowest commands. The time
is essentially the closers' `smt` calls, so the number of closers (the
merges above) and the number of calls per closer (the split depth) are the
two levers.

## Checking time: findings and workarounds

Measured with `gen/profile.py` on the generated proofs (EasyCrypt r2026.09,
Z3 4.13 and CVC5 1.3 in parallel, 5 s timeout). The status table above has
the resulting times; this section records what was found, since it shapes
the generator.

1. **All the time is in the closers, and a closer is a number of `smt`
   calls.** Every other command (`sp`, `if`, `seq`, `ecall`, `while`,
   declarations) is negligible. After the intros a closer's goal has 40–60
   atoms (mostly the `ui64` range facts of the trace, then bitmap cells and
   the cut formula); one `smt` call costs 0.2–0.6 s whatever the size of
   its goal (0.5–0.9 s with four buffers in context), and only two atoms
   out of 59 were closable without a prover. So the time is (number of
   closers) × (calls per closer) × (cost per call).

2. **Branch duplication.** The generator proved a conditional by duplicating
   the rest of the procedure into both branches, so a sequence of sibling
   conditionals was proved once per path: the avx2 dump cascade, nine
   conditionals, had 200 closers. *Workaround:* the join cuts (`MERGE<k>`,
   or the next `CUT`/`INV`; see above), 19 closers.

3. **Shallow splitting.** One `smt` call on a conjunction of ~15 atoms
   succeeds as often as not and costs the same as one call on an atom, so
   splitting two levels and calling `smt` on each part is 8–15× faster
   than one call per atom. Two caveats. The goal is right-nested, so `do
   2!(split ...)` peels two atoms and leaves everything else as one
   conjunct; that conjunct fails when it holds a hard atom (a pair of
   modular equalities, or, with four buffers, anything once the word-bound
   lemmas `W8/W64.to_uint_cmp` are among the hints), and a failing call
   costs the whole 5 s timeout. *Workaround:* shallow attempt, then the
   full split on what is left (`SPLIT` option, default `(2, 'all')`;
   `('all',)` for the procedures where the attempt always fails, the 1-way
   permutation drivers).

4. **A failing `smt` is not caught by `try` or `||`.** In strict proof mode
   (the default when checking) `smt` fails with an *uncatchable* error
   (`EcLowGoal.t_smt`: `tc_error ~catchable:false "cannot prove goal
   (strict)"`), and `FApi.t_try` rethrows uncatchable errors. The earlier
   `(smt(H) || smt(H2))` fallback therefore never fell back. The tactical
   `try! t` runs `t` in sloppy mode (catchable) and restores the goal on
   failure; it is only legal in strict mode, so it cannot be nested.
   `smt(timeout=...)` does not parse. *Workaround:* the shallow attempt is
   `(try! smt(...))`, the final one a plain strict `smt`.

5. **Goals that are hypotheses.** The alt driver's closers only had to
   match the validity of a trace variable with the hypothesis saying so;
   `smt` took 11 s per closer on these (24 closers), `done` nothing.
   *Workaround:* `try done` before every `smt`.

6. **Long straight-line bodies.** For the `nat` 4-way round (308
   instructions) the symbolic execution before the prover took 54 s and the
   prover 0.3 s: one `wp` followed by `/=` substitutes the whole chain of
   lets. *Workaround:* `STEPWP` (projections first, then `wp` ten
   instructions at a time), as for the `opt` round.

7. **Hint lists.** A short list (no word-bound lemmas) proves in 0.4 s the
   four-buffer conjunct that times out with the full list, but used as the
   default first attempt it tripled the ref file and doubled the 4-way one:
   it fails on most conjuncts, each failure costing the timeout. So `SMT2`
   stays an explicit, per-procedure option (the 4-buffer absorb loop), and
   the atoms always get the full list.

8. **Load.** The same file varies by up to 2× between a quiet and a busy
   machine (each `smt` call starts two provers; the CI runner has four
   vCPUs for `ECRJOBS: 4` jobs). Compare times from single runs with care;
   the table above was measured two files at a time.

What remains: the fourteen closers of the four-buffer 4-way add-state and
streaming steps (20–60 s each, 440 s of that file's 560 s). Their cost is
the per-call price of a context holding four buffers' validity and bitmap
facts, times 25–60 atoms; fewer or cheaper calls there need either a
smaller context for the range atoms or bitmap lemmas proved once in the
array theories, neither of which is done.

## Changes to the sources made for the proofs

The proofs required one change to the executable code and several changes to
the contracts. None of them changes what the code computes: the correctness
proofs of `proof/amd64` and `proof/amd64-barray` check against the changed
code, and the Jasmin tests pass.

### Pointer advance in the streaming absorb/dump (commit `16d8a25`)

When a streaming absorb or dump starts in the middle of a state word
(`at8 = at % 8 != 0`) and more words follow, the buffer pointer (memory
variants) or the offset (array variants) must advance by `8 - at8`. The code
did it in two steps; it now adds `8 - at8` in one:

```
// before                // after
buf += 8;                len = 8;
buf -= (64ui) at8;       len -= (64ui) at8;
                         buf += len;
```

In the safety model every `ui64` operation is range-checked. The contracts
only guarantee that the input ends below 2^64 (`is_mem_init(buf, upto - at)`),
so the intermediate `buf + 8` can exceed 2^64-1 by up to 7 although the final
pointer is in range; the same holds for the offset in the abstract array
theories, where `_ASIZE` is any size below 2^64. These range checks cannot be
proved. The one-step sum never exceeds the end of the input. `len` is dead at
that point, the instruction count is the same, and the 4-way memory code
(`_add_m_updstate_avx2x4`, `_dump_m_updstate_avx2x4`) already did this.

| File | Functions |
| --- | --- |
| `src/amd64/ref/keccak1600_updstate.jinc` | `_add_m_updstate`, `_dump_m_updstate` |
| `src/amd64/ref/keccak1600_updstate_ASIZE.jinc` | `_add_updstate`, `_dump_updstate` |
| `src/amd64/avx2/keccak1600x4_updstate.jinc` | `_add_m_bcast_updstate_avx2x4` |
| `src/amd64/avx2/keccak1600x4_updstate_ASIZE.jinc` | `_add_bcast_updstate_avx2x4`, `_add_updstate_avx2x4`, `_dump_updstate_avx2x4` |

On the correctness side, the hand-maintained `MM` blocks of the updstate
theories follow the new code, and a few pointer rewrites changed in
`ref/Keccak1600_updstate_ref.ec` and `avx2/Keccak1600_updstate_avx2x4.ec`
(both trees).

### Length bound on the array streaming contracts (commit `16d8a25`)

The streaming absorb and squeeze loops start with `len += at`, where
`at < r8 <= 200`. The memory contracts require `len <= 0xFFFFFFFFFFFFFF00`
for this; the array contracts only had `len <= _ASIZE`, which does not suffice
in the abstract theories. They now carry the same bound, which any real array
size implies: `_absorb_updstate`, `_squeeze_updstate`, `absorb_updstate`,
`squeeze_updstate` (`ref/keccak1600_updstate_ASIZE.jinc`), their 4-way
counterparts and the two 4-way broadcast absorbs
(`avx2/keccak1600x4_updstate_ASIZE.jinc`).

### Contract fixes and additions (commit `cac4567`)

Contracts only; the correctness models did not change.

* Fixed-size absorb (ref, avx2, avx2x4, memory and array): the contracts
  required `AT + LEN + (TRAILB != 0) < 200` (or only `AT < 200`) and gave the
  final position as `AT + LEN + (TRAILB != 0)`. Both hold only when no
  permutation runs, so they excluded or misdescribed multi-block absorbs. They
  now require `AT < RATE8` and give `(AT + LEN) % RATE8 + (TRAILB != 0)`.
  The add-state helpers bound the position by
  `AT + LEN + (TRAILB != 0) <= 200` (was `< 200`, or only `AT < 200`).
* ref fixed-size absorb/squeeze: the contracts had been copied from avx2 and
  described a 224-byte state (`7*32`); they now describe the 200-byte state.
* Memory sub-reads (`common/subreadwrite_imem.jinc`): they require the whole
  remaining input and state the pointer advance in case form (see the notes
  below). Array sub-reads/sub-writes (`common/subreadwrite_ASIZE.jinc`):
  `0 <= LEN` and case-form ensures.
* New contracts: the streaming functions, the status-word decoders, the 4-way
  `alt` kernels, the `opt` loop body (`rax <=u 22`, final `rax == rax + 2`),
  `__not_lane_basic` (`idx < 25`), `__f1600_loopbody_native` (`i < 24`) and
  `__pround_basic_inlined`.

## Notes on the contracts

* The extractor adds, for every `ui64` subterm of an `ensures`, an unguarded
  range condition. The fixed-length memory sub-reads therefore state the
  pointer advance as `final_buf - buf == (...)` with the case analysis inside
  the right-hand side, so that this condition always holds.
* The fixed-length sub-reads require the whole remaining input
  (`is_mem_init(buf, LEN)`, resp. `is_arr_init(buf, offset+DELTA, min(LEN, W))`),
  which their callers always have.
