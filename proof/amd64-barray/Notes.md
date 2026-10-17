# Notes on the port to the `barray` array model

Companion to [README.md](README.md), which is the operational reference
(status table, conventions, porting recipe). This file records the reasoning:
why the port is shaped the way it is, what went wrong on the way, what is
known to be weak, and where to go next.

Contents

1. [Context](#1-context)
2. [Strategy of the port](#2-strategy-of-the-port)
3. [`circuit` over BArray: the binding strategy and the EasyCrypt patch](#3-circuit-over-barray-the-binding-strategy-and-the-easycrypt-patch)
4. [Issues met during the port, and workarounds](#4-issues-met-during-the-port-and-workarounds)
5. [Limitations of the current approach](#5-limitations-of-the-current-approach)
6. [Follow-ups](#6-follow-ups)

---

## 1. Context

`jasmin2ec` has three array models. `proof/amd64` is checked against the
`old` model (polymorphic `ArrayN` of words, with `WArrayN` byte views and
`init64`/`get256_direct`-style casts in the extracted code). The `barray`
model, now the default, extracts every array as a monomorphic byte array
`BArrayN.t` (`JByte_array.ByteArray`, i.e. `MonoArray` over `W8.t`, cloned at
size `N`) and every sub-array access through a `SBArrayB_S` theory. Word
accesses become `BArrayN.getKd a o` / `setKd a o w` with a byte offset `o`,
sub-array accesses `SBArrayB_S.get_sub a o` / `set_sub a o s`, and global
tables `BArrayN.of_listK [...]`.

The port happened in two phases:

- commits `f583352` and `755be3f`: extraction, generated array theories,
  parametric `MM` modules, bridge lemmas, and the proofs of every file that
  does not use `circuit` (ref, updstate, avx2 absorb/squeeze, avx2x4
  dispatcher);
- the permutation proofs (`ref/Keccakf1600_{basic,opt}.ec`,
  `avx2/Keccakf1600_avx2.ec`, `avx2/Keccakf1600_avx2x4_{ref,nat,alt}.ec`),
  which are `circuit`-based and needed `circuit` to understand BArray terms.
  This is what sections 3–5 are mostly about.

All 28 files of `common/`, `ref/` and `avx2/` check with no admits
(`config/tests.config`, scenarios `keccak_amd64barray_{common,ref,avx2}`).

## 2. Strategy of the port

The guiding decision was to **keep the specifications, the spec-side lemmas and
the shape of every proof script, and absorb the representation change in a
thin layer of views and bridge lemmas**. Concretely:

- **Views, not new specs.** The spec types stay `W64.t Array25.t` (`state`),
  `W256.t Array7.t`, `W256.t Array25.t` (`state4x`). Each extracted buffer type
  gets a view op into the spec type: `st25 : BArray200.t -> state`,
  `st5`, `stavx2`, `st4x`, `st4x_get`, `ust_state`, `ust_st4x`
  (`common/Keccak1600_barrays.ec`). Contracts are stated through the views:
  `st25 st = _a ==> st25 res = f _a` where the old tree had `st = _a ==> res = f _a`.
  Inverse views (`st200`, `stavx2_of`, `st4x_of`) exist for the places where a
  proof wants to substitute the *program* state.

- **Bridge lemmas in byte-offset form.** `/>` and `/=` normalise
  `BArray200.set64 st 24` into `set64d st 192` (the scaled accessors are
  abbreviations, see §4.1), so the bridge lemmas are stated on the `d` forms
  with the offset as a variable and a divisibility premise
  (`st25_set64d a o w : 0 <= o < 200 => o %% 8 = 0 => ...`); the word-index
  forms are corollaries. The generic byte-array facts live in the abstract
  theory `BAExtra`, cloned once per size.

- **Mechanical script edits, catalogued.** The README "Porting recipe" lists
  the recurring edits (`(st25 st)` in `ecall` instantiations, one more `?` or
  a named `&hr` in intro patterns, `? ->` after a call, invariant conjuncts
  that become hypotheses). The permutation files followed the same recipe; the
  diff against `proof/amd64` is 14–40 lines per file.

- **Abstraction over the buffer size where the old tree had it.** The
  `ASIZE` variants (`extracted/Keccak1600_Jazz_ASIZE.ec`,
  `scripts/asize_transform.py`) and the six abstract theories keep the
  `MM`-module approach of the old tree; they clone `ByteArray as A` and the
  `*_checkXtr.ec` files instantiate `theory A <- BArray999`.

- **`circuit` proofs unchanged.** With the bindings of §3 in scope, every
  `proc; circuit` / `by circuit` of the old tree goes through unchanged on the
  BArray program. The only `circuit`-related script edits were deletions
  (§4.6).

What was *not* done: no change to the specifications, no re-proof of
spec-side lemmas, no change to the extracted code, no `proc change` rewriting
of BArray accesses into bindable wrappers (which is how the old tree handled
`WArray` casts, and would have meant one `proc change` per access).

## 3. `circuit` over BArray: the binding strategy and the EasyCrypt patch

### 3.1 The problem

`circuit` works on types declared through `bind bitstring` (fixed-width bit
vectors) and `bind array` (polymorphic `'a t` containers of bitstrings), plus a
catalog of `bind op` kinds. `BArrayN.t` fits neither: `bind array` requires a
type constructor of arity exactly one, and that requirement is baked into five
independent places of EasyCrypt (the `add_array` check, the clone of
`QFABV.A` whose operators are polymorphic, the `lookup_array*` functions that
read the element width from the type argument, the `A` check of `bind op`,
and every `BVOperators` array theory, written over `BV1.bv A.t`). A
`bind barray` kind would have had to touch all of them, add monomorphic copies
of the QFABV array theories, *and* still lacked kinds for byte-offset slices
and for array-to-array slices (`get_sub`/`set_sub`).

### 3.2 The choice: BArray as a bitstring

A byte array of `N` bytes is bound as a **bitstring of `8*N` bits** (byte `i`
at bits `8*i .. 8*i+7`, little-endian within the byte, as in `W8.w2bits`).
This needs no change to the binding kinds: `bind bitstring` accepts any
monomorphic named type, and the circuit backend already represents arrays as a
flat register (`CArray {width; count}` over `width*count` bits), so the array
tag buys nothing for byte arrays. The `tobits/ofbits/touint/tosint/ofint`
witnesses and the seven `BV` obligations are proved once, generically, in
`abstract theory BArrayBS` (`common/barray_abs_bindings.ec`), parameterised
by `clone import ByteArray as BA`.

Accessors are then slice operators on that bitstring:

| extracted op | binding | where |
|---|---|---|
| `t.[i]` (get8, get8d) | `"aextract"` `[BA.t & W8.t]` | `BArrayBS` |
| `t.[i <- w]` (set8, set8d) | `"uinsert"` `[BA.t & W8.t & W8.t]` | `BArrayBS` |
| `getKd t o` | `"uextract"` `[BA.t & WK.t & W8.t]` | `BArrayBS.GetSetK` |
| `setKd t o w` | `"uinsert"` `[BA.t & WK.t & W8.t]` | `BArrayBS.GetSetK` |
| `of_listK [...]` | `"oflist"` `[BA.t & WK.t]` | `BArrayBS.GetSetK` |
| `get_sub a o` / `set_sub a o s` | `"uextract"` / `"uinsert"` `[Abig.t & Asmall.t & W8.t]` | `SubBArrayBS` |
| `ArrayN.init` | `"painit"` | `keccak_barray_bindings.ec` |
| views `st25 st5 stavx2 st4x` | `"b2a"` | `keccak_barray_bindings.ec` |
| inverse views `st200 stavx2_of st4x_of` | `"a2b"` | `keccak_barray_bindings.ec` |

The `GetSetK` theories (K = 16..256) are nested in `BArrayBS` so that they are
only cloned for sizes that actually hold a word; the obligations
(`bvuextractP`, `bvuinsertP`, `bvoflistP`) are proved from the eclib lemmas
`getKd_byte`, `get8_setKdE`, `get8_of_listK` and `WRu8.bits8iE`, bitwise.
`common/keccak_barray_bindings.ec` instantiates everything for the sizes of
this extraction (10 byte-array sizes, the word sizes that fit, two sub-array
theories), binds `ArrayN.init` for N = 5, 7, 24, 25 as `painit`, and binds
the views. Binding a view as `b2a`/`a2b` tells `circuit` that it is a
reinterpretation of the same bits, so a contract `st4x res = ...` is checked
without unfolding `Array25.init (BArray800.get256 a)`.

The word bitstring bindings (`W8.t .. W256.t`) are the existing ones of
`common/keccak_bindings.ec`.

### 3.3 The EasyCrypt patch

Two gaps in the operator catalog had to be filled; both are small and generic.

1. **Unit-scaled extract/insert (`uextract`, `uinsert`).** The extracted
   program never contains `get64 a i`: `getK`, `setK`, `get_subK`, `set_subK`
   are *abbreviations*, so after typing the program contains `get64d a (8*i)`,
   with a **byte** offset. Every slice kind in the catalog counts its offset
   in bits (`extract`, `insert`, `asliceget/set`) or in units of the output
   width (`aextract`), and there is no aligned insert at all. The patch
   generalises the internal kinds
   `` `Extract of size_in * size_out * aligned:bool `` and
   `` `Insert of size_in * size_ins `` to carry an **offset unit**
   (`binding_size`): `extract`/`insert` use unit 1, `aextract` uses the output
   width, and the new surface names `uextract`/`uinsert` take the unit from a
   third bound type (`bind op [T_in & T_out & T_unit] op "uextract"`). The
   low-level translation is one multiplication (`unit * offset`) before
   `circuit_slice` / `circuit_slice_insert`. Theories `BVUExtract`,
   `BVUInsert` in `theories/datatypes/QFABV.ec` state the obligations with
   `base * BV3.size` as the bit offset and no divisibility condition (a 64-bit
   read at byte offset 3 is legitimate).

2. **Bitstring from a list (`oflist`).** Global tables are extracted as
   `BArrayN.of_listK [w0; w1; ...]` (an abbreviation, so the literal list is
   in the program), and `of_listK` is defined through the abstract `init`, so
   it neither reduces nor matched any kind. The new kind
   `` `BvOfList of size_out * size_elem `` (`bind op [T & W] f "oflist"`)
   concatenates the elements (first element in the low bits) and zero-pads or
   truncates to the target size, which is exactly `of_list'S`'s semantics.
   Only literal lists are translated (the argument goes through the existing
   `form_list_of_form`). Theory `BVOfList` in `QFABV.ec`.

Files touched in the EasyCrypt repository: `src/ecDecl.{ml,mli}` (kinds),
`src/ecScope.ml` (`add_bvoperator` cases), `src/ecSubst.ml`,
`src/ecLowCircuits.ml` (translation), `src/ecCircuits.ml` (parametric-kind
list), `src/ecPrinting.ml`, `theories/datatypes/QFABV.ec`,
`doc/tactics/bindings.rst` (catalog: the three new entries, a corrected
description of `aextract`, and the previously undocumented `painit`), and two
tests, `tests/circuits/bind_uextract.ec` and `tests/circuits/bind_oflist.ec`
(positive lemmas plus `fail` negative controls). The unit suite passes
(131 files).

The patch is **not upstream yet**; see §5.1.

### 3.4 Why not `proc change` into bindable wrappers

The old tree's technique for `WArray` casts (define `sliceget25_64_256` whose
first branch is the old-model expression, bind it as `asliceget`, and
`proc change` each access into it) would have worked here too, but costs one
`proc change` with a side proof per access, and the bound op's first branch
has to reproduce the exact extraction pattern, which changes with the Jasmin
version. Binding the extraction's own operators (`get64d`, `set_sub`, ...)
makes the proofs independent of how the access was spelled.

## 4. Issues met during the port, and workarounds

### 4.1 Abbreviations change what the program contains

`BArrayN.getK a i` is `abbrev getK t i = getKd t (r*i)`, and
`kECCAK1600_RC`, `rOL8`, `rOL56` are abbreviations for `of_listK [...]`
literals. After typing and after `/>`, goals contain `get64d a (8 * i)`,
`get64d (of_list64 [one; of_int 32898; ...]) (8 * c)`, and
`set64d e 0 (get64d e 0 `^` rc)`. Consequences:

- bindings must target the `d` operators (§3.3);
- bridge lemmas are stated on the `d` forms (`st25_xor0`, `stavx2_xor256d`,
  `st4x_xor0`);
- `kECCAK1600_RC_E i : BArray192.get64 kECCAK1600_RC i = rc_spec.[i]`
  (`ref/Keccakf1600_ref.ec`) does not match once `/>` has normalised the
  offset. Either instantiate it *before* simplification
  (`have K0 := kECCAK1600_RC_E 0 _; first done. move: K0 => /= K0.`) or use the
  offset form `kECCAK1600_RC_Ed o : o %% 8 = 0 => get64d kECCAK1600_RC o =
  rc_spec.[o %/ 8]` (`avx2/Keccakf1600_avx2x4_alt.ec`). Loop invariants
  `rC = rc_spec` become `rC = kECCAK1600_RC`.

### 4.2 Out-of-range reads differ between the models

`Keccakf1600_opt.ec`'s loop-body contract `keccakf1600_dround_opt_h` was
stated for `0 <= to_uint c < 24` while the body reads round constants `c` and
`c+1`. At `c = 23` that reads entry 24: in the old model both sides of the
goal were the same out-of-range `Array24` read (`witness`), and the proof went
through by accident; in the BArray model `get64d` past the end yields zero
bytes (`MonoArray.get_out` gives `dfl = W8.zero`), and the statement is false.
The contract now requires `to_uint c < 23` (all call sites pass an even `c`
below 24), and the losslessness loop invariant carries `2 %| to_uint rax` to
establish it. This is the only contract whose statement changed.

### 4.3 Loop proofs after `ecall` with a view contract

With contracts `st25 res = f ...` instead of `res = f ...`, the goal after an
`ecall` keeps the result as a universally quantified BArray plus an equation;
the old `-> /=` patterns become `r1 E1 r2 E2` followed by rewriting with the
bridge lemma and the equations (see the `while` steps of
`ref/Keccakf1600_basic.ec`, `avx2/Keccakf1600_avx2.ec`,
`avx2/Keccakf1600_avx2x4_ref.ec`). The final `forall r, st25 r = ... =>`
after the last call needs `r ->` (or `? ->`). Invariants over the program
state are written `st4x a = ...`, and `move: (st4x a{hr}) => sa` generalises
the view before spec-side rewriting.

### 4.4 The `/>` split of `a && b` postconditions

`auto => />` on the `phoare`/losslessness loops produces `A && B` where `A`
holds the contract preconditions; the old `split; first smt()` now faces an
extra `0 <= to_uint rax /\ (0 <= to_uint rax => to_uint rax < 23)` and a
`2 %| to_uint rax` conjunct (§4.2). `smt(dvdzE W64.to_uint_cmp)` closes them;
the intro pattern needs one more `_`.

### 4.5 Operator lookup of `"_.[_<-_]"`

`ByteArray` exports several abbreviations named `"_.[_<-_]"` (the
`Notation16..256` sub-theories alias `set16..set256` to the bracket syntax)
besides the `MonoArray` operator. `bind op` resolves its operator with a
first-match `EcEnv.Op.lookup`. In practice it resolved to the `MonoArray`
operator (the `set8`/`set8d` lemmas and the extracted `BArray3.set8`,
`BArray208.set8d` go through `circuit`), but this is not type-directed and
could silently pick an abbreviation after an eclib change. A type-directed
lookup in `bind op` (using `EcEnv.Op.all` and the expected signature, as
`bind circuit` already does) is the robust fix.

### 4.6 Dead old-model machinery

`avx2/Keccakf1600_avx2.ec` proved `stavx2_pack_h`/`stavx2_unpack_h` with five
`proc change` steps each, rewriting old-model slicing into
`sliceget25_64_256`/`sliceset25_64_256` (bound as `asliceget`/`asliceset`).
In the BArray program those accesses are `get256d`/`set256d` and the two
contracts are now `by proc; circuit`. The `sliceget25_64_256` /
`sliceset25_64_256` operators, their bindings and the `WArray200` import are
still in the file but unused and should be deleted.

### 4.7 Name capture inside the abstract bindings

Inside `WordBS`-style theories, the `BVA_*` clone produced by `bind bitstring`
exports a `size`, which makes a bare `size` ambiguous in the proofs that
follow (`more than one variable or constant matches size`). In this tree the
word bindings predate the port and are not affected; the generic byte-array
theory avoids the problem by only using `BA.size`.

### 4.8 Checking time

Times of the permutation files (seconds, this machine, barray file checked on
its own vs. the six old-model files run together):

| file | barray | old |
|---|---|---|
| `ref/Keccakf1600_basic.ec` | 25 | 28 |
| `ref/Keccakf1600_opt.ec` | 486 | 397 |
| `avx2/Keccakf1600_avx2.ec` | 35 | 38 |
| `avx2/Keccakf1600_avx2x4_ref.ec` | 72 | 37 |
| `avx2/Keccakf1600_avx2x4_nat.ec` | 77 | 72 |
| `avx2/Keccakf1600_avx2x4_alt.ec` | 328 | 162 |

The two 4-way files whose state is `BArray800` are about twice as slow. Not
investigated; the circuits are semantically the same (a flat 6400-bit
register in both models), so the candidates are the extra `b2a`/`a2b`
retagging nodes, the `painit`-based lane views (`st4x_lane`, 25 `uextract`
slices each), or a different node ordering sent to the SMT solver.
`pragma +Circuit:timing` is the place to start.

## 5. Limitations of the current approach

1. **Unmerged EasyCrypt dependency.** The six permutation files, and
   everything that `require`s `Keccak_barray_bindings`, need an EasyCrypt with
   the `uextract`/`uinsert`/`oflist` kinds. `shell.nix` follows EasyCrypt
   `main`, which does not have them, so the nix shell fails on these files
   until the patch is upstreamed (or `shell.nix` pins a branch).

2. **Per-project boilerplate.** `keccak_barray_bindings.ec` is ~70 clone and
   `bind` lines that merely enumerate the (array size, word size) pairs of this
   extraction; every project using the barray model would need its own copy,
   and `barray_abs_bindings.ec` itself is duplicated from the scloudplus
   project. The five `GetSetK` theories are textual copies of each other
   (only `K`, `r` and `WRu8` differ). See §6.2.

3. **Constant indices only.** As before, `circuit` needs every offset to
   reduce to an integer; loops over array indices still have to be unrolled or
   `cfold`ed before `circuit`.

4. **`oflist` translates literal lists only.** A table built with `mkseq`,
   `map`, or an opaque list would not be translated.

5. **No element-structured operations on byte arrays.** Since a `BArrayN` is
   a bitstring, kinds that need the array tag (`ainit`, `map`,
   `asliceget`/`asliceset` over elements) are not available on it. Nothing in
   this extraction needs them; `init`, `darray` and live `witness` values are
   likewise unbound (a dead `x <- witness` is fine; a live one becomes an
   opaque input).

6. **Semantic drift between models** can invalidate contracts that relied on
   out-of-range behaviour (§4.2). This is a property of the models, not of the
   bindings, but it means a port is not purely syntactic.

7. **Fragile operator resolution** for overloaded names (§4.5).

8. **Not exercised:** `extens`/bdep over BArray values (the backend only
   supports bitstrings there, so it should now work on BArray, but no proof in
   this tree uses it), and printing of the new kinds (cosmetic: the printer
   recovers `extract`/`aextract`/`uextract` from the number of bound types).

9. **Throughput** of the 4-way files (§4.8).

## 6. Follow-ups

### 6.1 One proof tree for both array models

Today `proof/amd64` and `proof/amd64-barray` are near-identical copies that
diverge only in the representation of arrays, and every fix must be applied
twice. The two trees already share the specifications (`crypto-specs`) and
the spec-side lemmas; what differs is the extracted module `M`, the contracts'
types, and the bridge layer. Options, from least to most invasive:

- **Same statements in both trees, via views.** Adopt the view-based contract
  style (`st25 st = _a ==> st25 res = f _a`) in the old tree as well, with
  `st25` defined as the identity (`W64.t Array25.t` *is* the spec type) and
  the bridge lemmas proved trivially. The proof scripts then become identical
  modulo the `require` lines, and the `circuit` lemmas are already identical.
  Mechanically: one source file per proof, and per-model `common/` directories
  providing the same lemma names (`st25_xor0`, `stavx2_xor256d`,
  `kECCAK1600_RC_E`, ...) with model-specific proofs. The README recipe's
  edits (`&hr`, `? ->`, `(st25 st)`) would have to be accepted in the old tree
  too, which is harmless there. This removes most of the duplication at the
  cost of a slightly heavier old-tree script.

- **Shared core over an array interface, plus per-model frontends.** Extend
  the existing `ASIZE`/`MM` approach: state the layer theorems about `MM`
  modules living in abstract theories parameterised by an array interface
  (`clone ByteArray as A` today), and have one thin frontend per model that
  (i) instantiates the interface (`theory A <- BArray200` here; an adapter
  theory presenting `W64.t Array25.t` through the same `get64d`/`set64d`
  signature for the old model), (ii) proves the `M.f ~ MM.f` equivalences
  (the `*_checkXtr.ec` files), and (iii) restates the contracts in the
  model's native types. The six non-circuit layers already have this shape.
  Two caveats: the interface has to be rich enough for both models (the old
  model's `WArray` casts do not map onto byte-offset accessors without the
  bridge lemmas the old tree already has), and `circuit` lemmas cannot live in
  the shared core, because `circuit` needs concrete bindings and `clone` does
  not re-run proof scripts: the `proc; circuit` contracts of the kernels stay
  per-frontend (about ten per permutation file), with the glue (loop
  invariants, composition, spec rewriting) shared.

- **Generate the frontends.** Since the extracted code of the two models is
  the same Jasmin source, a `jasmin2ec`-side or script-side generator
  (`scripts/asize_transform.py` is a start) could emit the per-model
  `checkXtr` files and the view/bridge instantiations, leaving only the
  per-model `circuit` lemmas to be written by hand.

The first option is the cheapest and can be done file by file; the second is
the one that scales to more array models and more targets.

### 6.2 A more structured and efficient BArray support in EasyCrypt

- **Ship the bindings with the array model.** The right home for
  `BArrayBS`/`SubBArrayBS` is next to `ByteArray` in Jasmin's eclib (a
  `JByte_array_circuits.ec`, or inside `ByteArray` itself if eclib may depend
  on `QFABV`). `bind` commands inside an abstract theory are replayed on
  `clone`, so `clone include ByteArray with op size <= N` would then bind
  every `BArrayN` at generation time, with the obligations proved once. The
  per-project file would shrink to the views. Alternatively, `jasmin2ec` can
  emit the clone lines, since it knows the (array size, word size) pairs.

- **Fold the five `GetSetK` copies into one theory** parameterised by the
  word theory (`theory W <- W64`, `theory WRu8 <- W8u8`, `op r <- 8`), in the
  style of jasmin-nist's `BSWAS`.

- **Type-directed operator lookup in `bind op`** (§4.5).

- **Cheaper bindings.** Each `bind` clones a `BVA_*` theory; the ~70 bindings
  of `keccak_barray_bindings.ec` take ~10 s to load before any proof runs.
  Recording the obligations without a full theory clone, or at least sharing
  the `BV` sub-clones between bindings of the same type, would help every
  project with many sizes.

- **Upstream the patch** (`uextract`, `uinsert`, `oflist`, docs, tests), and
  then bump `shell.nix`. A possible refinement before upstreaming: a single
  surface name with an optional unit (`extract` with a unit type) instead of
  three names, since the internal kind is already unified.

- **Investigate the 4-way slowdown** (§4.8); if the `b2a`/`a2b` retag or the
  `painit` views are the cause, caching slices of the same register or
  translating a `b2a`-bound view as a no-op would be the fix.

- **Byte arrays as arrays, if ever needed.** Should a future extraction use
  element-wise operations on byte arrays (`ainit`-style loops, `map`), a
  monomorphic array kind (`CArray {width = 8}`) would be the way to get them;
  for the Keccak code base nothing needs it, and the bitstring view is both
  simpler and what `extens` wants.

- **`oflist` beyond literals**, e.g. accepting `mkseq`/`map`-built tables
  after reduction, if some extraction produces them.
