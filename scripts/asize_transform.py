#!/usr/bin/env python3
"""
asize_transform.py — turn a concrete jasmin2ec extraction (with _ASIZE=999
baked in as Array999 / WArray999 / 999-literals) into a parametric companion
file wrapped in `abstract theory ... { module MM = { ... } }`.

The output is consumed only by *_checkXtr.ec equivalence proofs (`equiv
M.<proc> ~ MM.<proc> by sim.`). It is NEVER required by a real proof file —
those are hand-maintained in the natural fixedsizes style. The script's role
is to give a developer a starter MM block that's known-equivalent to the
concrete extraction at _ASIZE=999.

Substitutions applied (textual, line-based):

  Array999.t                      ->  A.t
  Array999                        ->  A         (e.g. Array999.init -> A.init)
  WArray999                       ->  WA
  bare 999                        ->  _ASIZE
  call:  X(...)  for X in SUBRW_PROCS  ->  RW.MM.X(...)

Subreadwrite proc DEFINITIONS (`__a_ilen_*` / `__a_rlen_*` inside `module M`)
are dropped from MM — they live in `RW.MM` (cloned from ReadWriteArray) in the
parametric layout.

Usage:
    python3 scripts/asize_transform.py <concrete.ec> -o <param.ec>
"""

import argparse
import re
import sys

# Procs that are pulled out of M and live in RW.MM in the parametric version.
# These are the subreadwrite primitives defined in
# src/amd64/common/subreadwrite_ASIZE.jinc.
SUBRW_PROCS = (
    "__a_ilen_read_upto8_at",
    "__a_ilen_read_upto16_at",
    "__a_ilen_read_upto32_at",
    "__a_ilen_read_bcast_upto8_at",
    "__a_ilen_read_upto8",
    "__a_ilen_read_bcast_upto8",
    "__a_ilen_read_upto16",
    "__a_ilen_read_upto32",
    "__a_ilen_write_upto8",
    "__a_ilen_write_upto16",
    "__a_ilen_write_upto32",
    "__a_rlen_read_upto8",
    "__a_rlen_read_upto8_noninline",
    "__a_rlen_write_upto8",
)

# A regex alternation that matches any subreadwrite proc name as a whole word.
SUBRW_RE = re.compile(
    r"\b(" + "|".join(re.escape(p) for p in SUBRW_PROCS) + r")\b"
)

# Regex matching a top-level `module M = {` line.
MODULE_M_OPEN = re.compile(r"^module M\s*=\s*\{\s*$")
# Regex matching the matching `}.` that closes module M (column 0).
MODULE_CLOSE = re.compile(r"^\}\.\s*$")

# Regex matching the start of a subreadwrite proc definition inside M, at the
# usual two-space indent jasmin2ec emits.
PROC_DEF_OPEN = re.compile(
    r"^(\s*)proc\s+(" + "|".join(re.escape(p) for p in SUBRW_PROCS) + r")\b"
)
# Matching close of a proc body is *indent-sensitive*: it's a `}` at the same
# column as the `proc` keyword opener. Internal nested `if {...}` / `while {...}`
# blocks use deeper indentation, so a flat regex "any `}` line" would fire too
# early. We track the opener's indent and match `<exactly that many spaces>}`.


def transform_body_line(line: str) -> str:
    """Apply the textual substitutions used inside MM proc bodies."""
    line = line.replace("Array999.t", "A.t")
    # Substitute bare Array999 (as module/namespace name) — careful not to
    # double-substitute Array999.t (already handled).
    line = re.sub(r"\bArray999\b", "A", line)
    line = re.sub(r"\bWArray999\b", "WA", line)
    # Bare 999 as integer literal -> _ASIZE.
    line = re.sub(r"\b999\b", "_ASIZE", line)
    # Prefix subreadwrite proc *call sites* with RW.MM. (it's safe to do this
    # everywhere in the body; the proc *definition* lines were filtered out
    # before we get here, so the only matches here are call sites).
    line = SUBRW_RE.sub(r"RW.MM.\1", line)
    return line


def transform_require_import(text: str) -> str:
    """In the file-level `require import ... Array999 ... WArray999.` block,
    drop Array999 and WArray999 (the parametric file pulls A/WA from clones
    instead). Other arrays (Array25, WArray800, etc.) stay — they're used for
    state representation, not buffer parameterisation."""
    return re.sub(
        r"\b(Array999|WArray999)\b\s*",
        "",
        text,
    )


PARAM_PREAMBLE = """
require import Keccak_bindings.
require import Keccak1600_subreadwrite.

abstract theory KeccakAsizeParam.

op _ASIZE: int.

axiom _ASIZE_ge0: 0 <= _ASIZE.
axiom _ASIZE_u64: _ASIZE < W64.modulus.

clone import PolyArray as A
 with op size <- _ASIZE
      proof ge0_size by exact _ASIZE_ge0.

clone import WArray as WA
 with op size <- _ASIZE.

clone import ReadWriteArray as RW
 with op _ASIZE <- _ASIZE,
      theory A <- A,
      theory WA <- WA
      proof _ASIZE_ge0 by exact _ASIZE_ge0
      proof _ASIZE_u64 by exact _ASIZE_u64.

"""

PARAM_POSTAMBLE = """
end KeccakAsizeParam.
"""


def transform(src: str) -> str:
    lines = src.splitlines(keepends=True)
    out = []

    i = 0
    in_module_m = False
    skip_subrw_proc_indent: int | None = None
    require_block_buf: list[str] = []
    in_require_block = False

    while i < len(lines):
        line = lines[i]

        # Handle the multi-line `require import\nArray3 Array5 ... WArray999.`
        # block at the file top: collect, strip Array999/WArray999, emit.
        if not in_module_m and (
            line.strip() == "require import" or line.startswith("require import\n")
        ):
            require_block_buf = [line]
            in_require_block = True
            i += 1
            while i < len(lines):
                require_block_buf.append(lines[i])
                if lines[i].rstrip().endswith("."):
                    break
                i += 1
            joined = "".join(require_block_buf)
            # Only filter when the block actually mentions Array999/WArray999.
            if re.search(r"\b(Array999|WArray999)\b", joined):
                joined = transform_require_import(joined)
                # Collapse runs of whitespace introduced by token deletion.
                joined = re.sub(r"[ \t]+\n", "\n", joined)
                joined = re.sub(r"  +", " ", joined)
            out.append(joined)
            in_require_block = False
            i += 1
            continue

        # Detect entering module M.
        if not in_module_m and MODULE_M_OPEN.match(line):
            # Inject the parametric preamble + open MM.
            out.append(PARAM_PREAMBLE)
            out.append("module MM = {\n")
            in_module_m = True
            i += 1
            continue

        # Inside module M.
        if in_module_m:
            # Detect the closing `}.` of module M.
            if MODULE_CLOSE.match(line):
                out.append("}.\n")
                out.append(PARAM_POSTAMBLE)
                in_module_m = False
                i += 1
                continue

            # If we're skipping a subreadwrite proc definition, watch for its
            # closing brace at exactly the opener's indent column.
            if skip_subrw_proc_indent is not None:
                close_marker = " " * skip_subrw_proc_indent + "}"
                stripped_right = line.rstrip()
                if stripped_right == close_marker:
                    skip_subrw_proc_indent = None
                i += 1
                continue

            # Detect start of a subreadwrite proc to skip.
            m = PROC_DEF_OPEN.match(line)
            if m:
                skip_subrw_proc_indent = len(m.group(1))
                i += 1
                continue

            # Otherwise transform the line.
            out.append(transform_body_line(line))
            i += 1
            continue

        # Outside module M (preamble, abbrevs, helper clones): pass through.
        out.append(line)
        i += 1

    return "".join(out)


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("input", help="concrete .ec extraction file")
    p.add_argument("-o", "--output", required=True, help="parametric .ec output")
    args = p.parse_args()

    with open(args.input) as f:
        src = f.read()

    out = transform(src)

    with open(args.output, "w") as f:
        f.write(out)

    print(f"wrote {args.output}", file=sys.stderr)


if __name__ == "__main__":
    main()
