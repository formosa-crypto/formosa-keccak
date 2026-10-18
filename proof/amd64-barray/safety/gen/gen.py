"""Generate EasyCrypt safety proof scripts from the jasmin2ec -m safety model.

Strategy per procedure (after inlining pure helpers):
  * split conditionals forward (`sp n; if`),
  * close straight-line suffixes backward (`wp; ecall (f_proof args)` ...; `auto; CL`),
  * loops: `while (INV<id>)` (invariant supplied in ANN),
  * calls before a loop: `seq n : (INV<id>)`,
  * calls before a conditional containing calls: `seq n : (CUT<id>)` (supplied in ANN),
  * conditional after a loop: `seq n : (INV<id> /\ !(cond))`.
"""
import re, sys, copy
import model

# The closer. After the intros, the goal is a conjunction of (typically) dozens of
# atoms: the ui64 range facts of the trace, bitmap cells, the cut formula. Each
# `smt` call costs 0.2-0.6 s whatever its size, so splitting all the way down
# (one call per atom) is 8-15x slower than a shallow split (one call per
# conjunction of ~15 atoms). A conjunction can be too big for one call (a pair of
# modular equalities already is), so the shallow attempt must be allowed to fail:
# a failing `smt` is an uncatchable error in strict proof mode (`try` and `||` do
# not catch it); `try! t` runs t in sloppy mode and restores the goal on failure.
# So: shallow split, `try! smt` on each part, then the full split and a strict
# `smt` on whatever is left. SMTCALL (sloppy) and SMTLAST (strict) are filled in
# by `subst`.
SPLIT = "split; try (move=> *; rewrite ?List.all_cat /=)"
INTROS = ("rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); "
          "rewrite ?List.all_cat /=")
def closer(depths=(2, 'all')):
    # `try done` first: a goal that is a hypothesis (e.g. the validity of a trace
    # variable, or of a callee's trace) costs nothing here and seconds in smt
    shallow = "".join(f"try (do {d}!({SPLIT})); try done; (try! SMTCALL); " for d in depths if d != 'all')
    return INTROS + "; " + shallow + f"do ?({SPLIT}); try done; SMTLAST."
CL = closer()
INLINE = ['__HAS_FEATURE', '__KECCAK_F', '__KECCAK_Fx4', '__SHLQ', '__SHLDQ', '__SHLQ_256',
          'keccakf1600_index', '__stavx2_pos_avx2']

def number(ss, ctr):
    # ctr = [stmt counter, if counter, while counter]; names use the if/while ordinals
    for s in ss:
        ctr[0] += 1; s.id = ctr[0]
        if s.kind == 'if':
            ctr[1] += 1; s.ord = ctr[1]
            number(s.then, ctr); number(s.els, ctr)
        if s.kind == 'while':
            ctr[2] += 1; s.ord = ctr[2]
            number(s.body, ctr)
        if s.kind == 'call':
            ctr[3] += 1; s.cord = ctr[3]

def nparams(P_sig, f):
    return P_sig[f]

def instrs(ss):
    return [s for s in ss if s.kind != 'comment' and not (s.kind == 'asgn' and s.text.startswith('return'))]

def mark_inl(ss):
    # statements inlined from a callee keep the callee's ordinals: never key an
    # annotation on them
    for s in ss:
        s.inl = True
        if s.kind == 'if': mark_inl(s.then); mark_inl(s.els)
        if s.kind == 'while': mark_inl(s.body)

def expand(ss, P, sig, used):
    """simulate EasyCrypt `inline` of INLINE procs: params + body + result."""
    out = []
    for s in instrs(ss):
        if s.kind == 'call' and s.f in INLINE:
            used.add(s.f)
            out += [model.Stmt('asgn', text='(inline param)') for _ in range(sig[s.f])]
            body = expand(copy.deepcopy(P[s.f]), P, sig, used); mark_inl(body)
            out += body
            out.append(model.Stmt('asgn', text='(inline result)'))
        elif s.kind == 'if':
            t = copy.copy(s); t.then = expand(s.then, P, sig, used); t.els = expand(s.els, P, sig, used); out.append(t)
        elif s.kind == 'while':
            t = copy.copy(s); t.body = expand(s.body, P, sig, used); out.append(t)
        else:
            out.append(s)
    return out

def hard(s):
    return s.kind == 'while' or (s.kind == 'if' and model.has(s.then + s.els, {'call', 'while'}))

def has_hard(ss):
    return any(hard(s) for s in ss)

QUAL = {}       # callee -> theory prefix of its lemma (e.g. "RW."), set by Gen.script

def ecall(s):
    args = ' '.join(a if re.fullmatch(r'[A-Za-z0-9_]+', a) else '(' + a + ')' for a in s.args)
    return f"ecall ({QUAL.get(s.f, '')}{s.f}_proof{(' ' + args) if args else ''})."

BEFORE = set()   # names BEFORE<k> available for the current procedure (set by Gen.script)
KEYS = set()     # all formula annotations of the current procedure (set by Gen.script)
MERGE_MODE = 'auto'

def cut_name(s):
    return f"INV{s.ord}" if s.kind == 'while' else f"CUT{s.ord}"

def next_hard(ss, i):
    return next((j for j in range(i, len(ss)) if hard(ss[j])), None)

def join_for(ss, k, ctx):
    """Formula at the join of the conditional ss[k], and the index where the
    continuation resumes, or None (then the continuation is duplicated into
    both branches). Merging needs the state at the join: an explicit
    MERGE<ord>, or, when the next hard statement follows through assignments
    only, its CUT<ord>/INV<ord>, which is the same point."""
    head, rest = ss[k], ss[k+1:]
    if MERGE_MODE == 'off': return None
    if not getattr(head, 'inl', False) and f"MERGE{head.ord}" in KEYS: return f"MERGE{head.ord}", k + 1
    if not has_hard(rest): return None      # merging a tail without hard statements costs a closer
    j = next_hard(ss, k + 1)
    straight = all(s.kind == 'asgn' for s in ss[k+1:j]) and not getattr(ss[j], 'inl', False)
    want = (cut_name(ss[j]), j) if straight else (f"MERGE{head.ord}", k + 1)
    if want[0] in KEYS or MERGE_MODE == 'all': return want
    ctx['hint'].add(want[0]); return None

def cutpos(ss, i):
    # move the cut before the parameter set-up of the call at index i
    while i > 0 and ss[i-1].kind == 'asgn' and re.match(r'(b_)?param(_\d+)? <-', ss[i-1].text): i -= 1
    return i

def backward(ss, ind, ctx=None):
    out = []
    pts = [(cutpos(ss, i), f"BEFORE{s.cord}") for i, s in enumerate(ss)
           if s.kind == 'call' and f"BEFORE{s.cord}" in BEFORE]
    pts = [(p, n) for (p, n) in pts if p > 0]
    if pts:
        p, n = pts[0]
        if ctx is not None: ctx['need'].add(n)
        out.append(ind + f"seq {p} : ({n}).")
        out.append(ind + "+ (* cut *)")
        out += backward(ss[:p], ind + "  ", ctx)
        out += backward(ss[p:], ind, ctx)
        return out
    for c in reversed([s for s in ss if s.kind == 'call']):
        out.append(ind + "wp; " + ecall(c))
    out.append(ind + "auto; " + CL)
    return out

SPLIT_IFS = 2

def nifs(ss):
    n = 0
    for s in ss:
        if s.kind == 'if': n += 1 + nifs(s.then) + nifs(s.els)
        if s.kind == 'while': n += nifs(s.body)
    return n

def fwd(ss, ind, ctx):
    out = []
    k = 0
    while k < len(ss) and ss[k].kind == 'asgn': k += 1
    if not has_hard(ss):
        # split leading conditionals forward when there are several (avoids wp blow-up)
        if not (k < len(ss) and ss[k].kind == 'if' and nifs(ss) >= SPLIT_IFS):
            return backward(ss, ind, ctx)
    head = ss[k]
    if head.kind == 'if':
        if k: out.append(ind + f"sp {k}.")
        jn = join_for(ss, k, ctx)
        if jn:
            # prove the conditional once, up to the join, then continue once
            name, h2 = jn; ctx['need'].add(name)
            out.append(ind + f"seq {h2 - k} : ({name}).")
            out.append(ind + "+ (* join *)")
            out.append(ind + "  if.")
            out.append(ind + "  + (* then *)")
            out += fwd(head.then + ss[k+1:h2], ind + "    ", ctx)
            out.append(ind + "  + (* else *)")
            out += fwd(head.els + ss[k+1:h2], ind + "    ", ctx)
            out += fwd(ss[h2:], ind, ctx)
            return out
        out.append(ind + "if.")
        out.append(ind + "+ (* then *)")
        out += fwd(head.then + ss[k+1:], ind + "  ", ctx)
        out.append(ind + "+ (* else *)")
        out += fwd(head.els + ss[k+1:], ind + "  ", ctx)
        return out
    if head.kind == 'call':
        h = next_hard(ss, k)
        name = cut_name(ss[h])
        ctx['need'].add(name)
        out.append(ind + f"seq {h} : ({name}).")
        out.append(ind + "+ (* cut *)")
        out += backward(ss[:h], ind + "  ", ctx)
        out += fwd(ss[h:], ind, ctx)
        return out
    if head.kind == 'while':
        rest = ss[k+1:]
        name = f"INV{head.ord}"; ctx['need'].add(name)
        if has_hard(rest):
            out.append(ind + f"seq {k+1} : ({name} /\\ !({head.cond})).")
            out.append(ind + "+ (* loop *)")
            out += fwd(ss[:k+1], ind + "  ", ctx)
            out += fwd(rest, ind, ctx)
            return out
        for c in reversed([s for s in rest if s.kind == 'call']):
            out.append(ind + "wp; " + ecall(c))
        out.append(ind + f"wp; while ({name}).")
        out.append(ind + "+ (* loop body *)")
        out += fwd(instrs(head.body), ind + "  ", ctx)
        out.append(ind + "(* before the loop *)")
        out.append(ind + "auto; " + CL)
        return out
    raise Exception("?")

class Gen:
    def __init__(self, path):
        self.P = model.procs(path)
        txt = open(path).read()
        self.sig = {}
        for m in re.finditer(r'\n  proc ([A-Za-z0-9_]+) \(([^)]*)\)', txt):
            a = m.group(2).strip()
            self.sig[m.group(1)] = 0 if not a else len(a.split(','))
        for n, ss in self.P.items():
            number(ss, [0, 0, 0, 0])

    def script(self, name, ann=None, qual=None):
        """-> (proof script, formula names it needs, names that would enable more merges)"""
        global BEFORE, QUAL, CL, KEYS, MERGE_MODE
        a = ann or {}
        BEFORE = set(k for k in a if k.startswith('BEFORE'))
        KEYS = set(k for k in a if k not in OPTIONS)
        # MERGE: 'auto' (merge the branches of a conditional when the join formula
        # exists), 'all' (merge everywhere, missing formulas are reported), 'off'
        MERGE_MODE = a.get('MERGE', 'auto')
        QUAL = dict(qual or {})
        # SPLIT: split depths tried by the closer, e.g. (1, 'all'); default (2, 'all')
        CL = closer(a.get('SPLIT', (2, 'all')))
        used = set()
        ss = expand(self.P[name], self.P, self.sig, used)
        step = a.get('STEPWP')
        if step and not used and all(s.kind == 'asgn' for s in instrs(ss)):
            # long straight-line body (a permutation round): reduce the projections of
            # the result tuple first, then wp a few instructions at a time, simplifying
            # in between, so that the dead word computations are dropped one by one
            # (a single wp + simplify substitutes the whole let chain and blows up)
            n = len(instrs(ss))
            ks = list(range((n - 1) // step * step, -1, -step))
            lines = ["simplify."]
            lines += [" ".join(f"wp {k}. simplify." for k in ks[i:i + 8]) for i in range(0, len(ks), 8)]
            lines.append("skip; " + CL)
            return "\n".join(lines), set(), set()
        ctx = {'need': set(), 'hint': set()}
        lines = fwd(ss, "", ctx)
        if used:
            lines = ["inline " + " ".join("M." + f for f in INLINE if f in used) + "."] + lines
        return "\n".join(lines), ctx['need'], ctx['hint']

OPTIONS = ('SMT', 'SMT2', 'STEPWP', 'SPLIT', 'MERGE')   # annotation keys that are not formulas

def subst(script, ann):
    smt = "smt(" + ann.get('SMT', '') + ")"
    sloppy, strict = smt, smt
    if ann.get('SMT2'):
        # SMT2: a short hint list for the shallow attempt, tried before the full one;
        # only for the few procedures where it is known to work (the 4-buffer absorb
        # loop): a failing call costs the whole timeout, and used as a default for a
        # layer it tripled its time. The atoms keep the full list.
        sloppy = "(smt(" + ann['SMT2'] + ") || " + smt + ")"
    script = script.replace("SMTCALL", sloppy).replace("SMTLAST", strict)
    for k in sorted(ann, key=len, reverse=True):
        if k in OPTIONS: continue
        script = re.sub(r'\b' + k + r'\b', '(' + ann[k] + ')', script)
    return script

if __name__ == '__main__':
    G = Gen(sys.argv[1])
    for n in sys.argv[2:]:
        s, need, hint = G.script(n)
        print(f"== {n} need={sorted(need)} merge-hints={sorted(hint)}"); print(s)
