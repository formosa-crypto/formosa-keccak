#!/usr/bin/env python3
"""Where does the checking time of a generated proof file go?

    python3 gen/profile.py ref/Keccak1600_safety.ec            # compiles with -tstats, then reports
    python3 gen/profile.py ref/Keccak1600_safety.ec stats.txt  # reports from an existing -tstats file

The report gives the total, the time per command kind (the closers are the
`auto; <CL>` / `skip; <CL>` sentences), the time per lemma with its number of
closers and conditionals, the distribution of the closer times, and the
slowest commands. Run from proof/amd64-barray/safety (the easycrypt.project
there gives the load path). The stats file is written next to the proof file
as <name>.tstats unless given.
"""
import collections, os, re, statistics, subprocess, sys, time

def run(ec_file, stats):
    t0 = time.time()
    log = os.path.splitext(stats)[0] + ".log"
    with open(log, "w") as out:   # EasyCrypt's progress output and messages go to the log
        r = subprocess.run(["easycrypt", "compile", "-no-eco", "-tstats", stats, ec_file], stdout=out, stderr=subprocess.STDOUT)
    print(f"easycrypt compile: exit {r.returncode}, {time.time() - t0:.0f} s wall (output in {log})")
    if r.returncode:
        print(open(log).read().replace("\r", "\n").splitlines()[-3:]); sys.exit(r.returncode)

def rows_of(stats):
    rows = []
    for l in open(stats):
        m = re.match(r'(\d+):\d+ (\d+):\d+ ([\d.]+)', l)
        if m: rows.append((int(m.group(1)), int(m.group(2)), float(m.group(3))))
    return rows

def kind(text):
    t = text.strip()
    if re.match(r'^\+ \(\*.*\*\)\s*\n', t): t = t.split("\n", 1)[1].strip()   # bullet + sentence
    if t.startswith(("auto;", "skip;")) and "smt(" in t: return "closer"
    if t.startswith(("wp; ecall", "ecall")): return "ecall"
    if t.startswith(("wp; while", "while")): return "while"
    for p in ("seq", "sp", "if", "wp", "simplify", "inline", "conseq", "case"):
        if t.startswith(p): return p
    if t.startswith(("lemma", "proof", "qed")): return "lemma"
    if t.startswith(("op ", "module", "clone", "require", "abstract", "end ", "hint", "import", "axiom", "type")): return "decl"
    return "other"

def report(ec_file, rows):
    src = open(ec_file).read().splitlines()
    lem = [(i, l.split()[1]) for i, l in enumerate(src, 1) if l.startswith("lemma ")]
    def owner(line):
        o = "(header)"
        for i, n in lem:
            if i <= line: o = n
        return o
    tot = sum(r[2] for r in rows)
    print(f"{ec_file}: {tot:.0f} s over {len(rows)} commands")
    byk = collections.Counter(); nk = collections.Counter()
    per = collections.Counter(); perc = collections.Counter(); peri = collections.Counter(); pern = collections.Counter()
    closers = []
    for s, e, t in rows:
        k = kind("\n".join(src[s-1:e])); byk[k] += t; nk[k] += 1
        o = owner(s); per[o] += t; pern[o] += 1
        if k == "closer": perc[o] += 1; closers.append((t, s, o))
        if k == "if": peri[o] += 1
    print("by command kind:")
    for k, t in byk.most_common():
        if t >= 1: print(f"  {t:7.0f} s  {nk[k]:5d} cmds  avg {t/nk[k]:6.2f} s  {k}")
    print("per lemma (slowest 12):")
    for n, t in per.most_common(12):
        print(f"  {t:7.0f} s  {n:40s} closers {perc[n]:4d} (avg {t/max(1,perc[n]):5.1f} s)  if {peri[n]:3d}  cmds {pern[n]:4d}")
    if closers:
        ts = sorted(t for t, _, _ in closers)
        print(f"closers: {len(ts)}, total {sum(ts):.0f} s, median {statistics.median(ts):.1f} s, max {ts[-1]:.1f} s,"
              f" > 5 s: {sum(1 for x in ts if x > 5)} ({sum(x for x in ts if x > 5):.0f} s)")
    print("slowest commands:")
    for t, s, o in sorted(closers, reverse=True)[:10]:
        print(f"  {t:6.1f} s  line {s:5d}  {o}")

if __name__ == '__main__':
    ec_file = sys.argv[1]
    stats = sys.argv[2] if len(sys.argv) > 2 else os.path.splitext(ec_file)[0] + ".tstats"
    if len(sys.argv) <= 2 or not os.path.exists(stats): run(ec_file, stats)
    report(ec_file, rows_of(stats))
