#!/usr/bin/env python3
"""
asize_transform.py — turn a concrete jasmin2ec extraction (with _ASIZE=999
baked in as Array999 / WArray999 / BArray999 / 999-literals) into the
parametric `module MM` companion used by the *_checkXtr.ec equivalence
proofs (`equiv M.<proc> ~ MM.<proc> by sim.`).

The output is NEVER required by a real proof file: those are hand-maintained
in the natural fixedsizes style.  The script gives a developer a starter MM
block that is known-equivalent to the concrete extraction at _ASIZE=999.

Array models (--model):
  old     (deprecated jasmin2ec model)   Array999.t -> A.t, Array999 -> A,
                                         WArray999 -> WA, 999 -> _ASIZE
  barray  (default)                      BArray999.t -> A.t, BArray999 -> A,
                                         999 -> _ASIZE

Procedure selection (--theory PRESET): only the procs of the preset are kept
(in extraction order); everything else is dropped.  Call sites are rewritten
to match the hand-maintained MM blocks:
  - calls to kept procs (siblings)                 : unchanged
  - calls to subreadwrite procs (__a_ilen_*/__a_rlen_*): RW.MM.<name>
    (except in preset `subreadwrite`, where they are siblings)
  - calls to any other proc of `module M`         : M.<name>
    (size-independent procs of the memory extraction, Keccak1600_Jazz)

Usage:
    python3 scripts/asize_transform.py [--model old|barray] --theory PRESET
                                       [--mm-only] <concrete.ec> -o <out.ec>
  --array-name N  name of the byte-array parameter theory (default A; the
              updstate_avx2x4 theory uses BA, see the comment there)
  --mm-only   emit just `module MM = { ... }.` (to splice into the hand-
              maintained abstract theory); otherwise a standalone
              `abstract theory KeccakAsizeParam` file is produced.
"""

import argparse
import re
import sys

# Subreadwrite primitives (src/amd64/common/subreadwrite_ASIZE.jinc); they
# live in RW.MM (cloned from ReadWriteArray) in the parametric layout.
SUBRW_PROCS = (
    "__a_ilen_read_upto8_at",
    "__a_ilen_read_upto16_at",
    "__a_ilen_read_upto32_at",
    "__a_ilen_read_bcast_upto8_at",
    "__a_ilen_write_upto8",
    "__a_ilen_write_upto16",
    "__a_ilen_write_upto32",
    "__a_rlen_read_upto8",
    "__a_rlen_write_upto8",
)

PRESETS = {
    "subreadwrite": SUBRW_PROCS,
    "fixedsizes_ref": ("__addstate", "__absorb", "__dumpstate", "__squeeze"),
    "updstate_ref": ("_add_updstate", "_absorb_updstate", "_dump_updstate",
                     "_squeeze_updstate", "absorb_updstate", "squeeze_updstate"),
    "fixedsizes_avx2": ("__addstate_avx2", "__absorb_avx2", "__dumpstate_avx2",
                        "__squeeze_avx2"),
    "fixedsizes_avx2x4": ("__addstate_bcast_avx2x4", "__absorb_bcast_avx2x4",
                          "__addstate_avx2x4", "__absorb_avx2x4",
                          "__dumpstate_avx2x4", "__squeeze_avx2x4"),
    "updstate_avx2x4": ("_add_bcast_updstate_avx2x4",
                        "_absorb_bcast_updstate_avx2x4",
                        "_add_updstate_avx2x4", "_absorb_updstate_avx2x4",
                        "_dump_updstate_avx2x4", "_squeeze_updstate_avx2x4",
                        "absorb_bcast_updstate_avx2x4", "absorb_updstate_avx2x4",
                        "squeeze_updstate_avx2x4"),
}

MODULE_M_OPEN = re.compile(r"^module M\s*=\s*\{\s*$")
MODULE_CLOSE = re.compile(r"^\}\.\s*$")
# jasmin2ec emits procs of `module M` at a two-space indent; a proc body ends
# with `}` at exactly that indent (nested blocks are deeper).
PROC_OPEN = re.compile(r"^  proc\s+([A-Za-z_0-9]+)\b")
PROC_CLOSE = re.compile(r"^  \}\s*$")
CALL_SITE = re.compile(r"<@\s+([A-Za-z_0-9]+)\s*\(")


def body_subst(line: str, model: str, aname: str = "A") -> str:
    """Array-size substitutions used inside MM proc bodies."""
    if model == "old":
        line = line.replace("Array999.t", "A.t")
        line = re.sub(r"\bArray999\b", "A", line)
        line = re.sub(r"\bWArray999\b", "WA", line)
    else:
        line = line.replace("BArray999.t", aname + ".t")
        line = re.sub(r"\bBArray999\b", aname, line)
    line = re.sub(r"\b999\b", "_ASIZE", line)
    return line


def call_subst(line: str, kept, subrw_sibling: bool) -> str:
    def repl(m):
        name = m.group(1)
        if name in kept:
            return m.group(0)
        if name in SUBRW_PROCS and not subrw_sibling:
            return m.group(0).replace(name, "RW.MM." + name, 1)
        return m.group(0).replace(name, "M." + name, 1)
    return CALL_SITE.sub(repl, line)


def require_subst(text: str, model: str) -> str:
    """Drop the size-999 theories from the file-level require block."""
    names = r"Array999|WArray999" if model == "old" else r"Array999|BArray999"
    text = re.sub(r"\b(" + names + r")\b\s*", "", text)
    text = re.sub(r"[ \t]+\n", "\n", text)
    text = re.sub(r"  +", " ", text)
    return text


def preamble(model: str, preset: str) -> str:
    out = ["", "require import Keccak_bindings.",
           "require import Keccak1600_subreadwrite.", ""]
    if model == "barray":
        out.insert(1, "from Jasmin require import JByte_array.")
    out += ["abstract theory KeccakAsizeParam.", "",
            "op _ASIZE: int.", "",
            "axiom _ASIZE_ge0: 0 <= _ASIZE.",
            "axiom _ASIZE_u64: _ASIZE < W64.modulus.", ""]
    if model == "old":
        out += ["clone import PolyArray as A",
                " with op size <- _ASIZE",
                "      proof ge0_size by exact _ASIZE_ge0.", "",
                "clone import WArray as WA",
                " with op size <- _ASIZE.", ""]
    else:
        out += ["clone import ByteArray as A",
                " with op size <- _ASIZE",
                "      proof ge0_size by exact _ASIZE_ge0.", ""]
    if preset != "subreadwrite":
        out += ["clone import ReadWriteArray as RW",
                " with op _ASIZE <- _ASIZE,",
                "      theory A <- A" + (",", "")[model != "old"]]
        if model == "old":
            out += ["      theory WA <- WA"]
        out += ["      proof _ASIZE_ge0 by exact _ASIZE_ge0",
                "      proof _ASIZE_u64 by exact _ASIZE_u64.", ""]
    return "\n".join(out) + "\n"


def split_module_m(lines):
    """Return (before, procs, after) where procs = [(name, [lines])]."""
    before, after, procs = [], [], []
    i = 0
    while i < len(lines) and not MODULE_M_OPEN.match(lines[i]):
        before.append(lines[i]); i += 1
    if i == len(lines):
        sys.exit("error: `module M = {` not found")
    i += 1
    cur = None
    while i < len(lines) and not MODULE_CLOSE.match(lines[i]):
        line = lines[i]
        m = PROC_OPEN.match(line)
        if m and cur is None:
            cur = (m.group(1), [line])
        elif cur is not None:
            cur[1].append(line)
            if PROC_CLOSE.match(line):
                procs.append(cur); cur = None
        # non-proc lines inside module M (none expected in the normal model)
        i += 1
    if cur is not None:
        sys.exit("error: unterminated proc %s" % cur[0])
    after = lines[i + 1:] if i < len(lines) else []
    return before, procs, after


def transform(src: str, model: str, preset: str, mm_only: bool, aname: str = "A") -> str:
    lines = src.splitlines(keepends=True)
    before, procs, _after = split_module_m(lines)
    kept = set(PRESETS[preset])
    found = {name for name, _ in procs}
    missing = kept - found
    if missing:
        sys.exit("error: procs not found in extraction: %s" % sorted(missing))
    subrw_sibling = preset == "subreadwrite"

    mm = ["module MM = {\n"]
    for name, plines in procs:
        if name not in kept:
            continue
        for line in plines:
            mm.append(call_subst(body_subst(line, model, aname), kept, subrw_sibling))
    mm.append("}.\n")
    if mm_only:
        return "".join(mm)

    # standalone file: header (require block filtered) + preamble + MM
    head = "".join(before)
    head = re.sub(r"(require import\n(?:[^\n]*\n)*?[^\n]*\.\n)",
                  lambda m: require_subst(m.group(1), model), head, count=1)
    return head + preamble(model, preset) + "".join(mm) + \
        "\nend KeccakAsizeParam.\n"


def main():
    p = argparse.ArgumentParser(description=__doc__,
                                formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument("input", help="concrete ASIZE .ec extraction")
    p.add_argument("-o", "--output", required=True)
    p.add_argument("--model", choices=("old", "barray"), default="barray")
    p.add_argument("--theory", choices=sorted(PRESETS), required=True,
                   help="which procs to keep in MM")
    p.add_argument("--array-name", default="A",
                   help="name of the byte-array theory parameter (barray model; default A)")
    p.add_argument("--mm-only", action="store_true",
                   help="emit only the `module MM = { ... }.` block")
    args = p.parse_args()
    with open(args.input) as f:
        src = f.read()
    out = transform(src, args.model, args.theory, args.mm_only, args.array_name)
    with open(args.output, "w") as f:
        f.write(out)
    print(f"wrote {args.output}", file=sys.stderr)


if __name__ == "__main__":
    main()
