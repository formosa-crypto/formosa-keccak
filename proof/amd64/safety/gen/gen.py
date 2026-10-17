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

CL = "rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt()."
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

def expand(ss, P, sig, used):
    """simulate EasyCrypt `inline` of INLINE procs: params + body + result."""
    out = []
    for s in instrs(ss):
        if s.kind == 'call' and s.f in INLINE:
            used.add(s.f)
            out += [model.Stmt('asgn', text='(inline param)') for _ in range(sig[s.f])]
            out += expand(copy.deepcopy(P[s.f]), P, sig, used)
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
        out.append(ind + "if.")
        out.append(ind + "+ (* then *)")
        out += fwd(head.then + ss[k+1:], ind + "  ", ctx)
        out.append(ind + "+ (* else *)")
        out += fwd(head.els + ss[k+1:], ind + "  ", ctx)
        return out
    if head.kind == 'call':
        h = next(i for i in range(k, len(ss)) if hard(ss[i]))
        if ss[h].kind == 'while':
            name = f"INV{ss[h].ord}"
        else:
            name = f"CUT{ss[h].ord}"
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
        global BEFORE, QUAL
        BEFORE = set(k for k in (ann or {}) if k.startswith('BEFORE'))
        QUAL = dict(qual or {})
        used = set()
        ss = expand(self.P[name], self.P, self.sig, used)
        ctx = {'need': set()}
        lines = fwd(ss, "", ctx)
        if used:
            lines = ["inline " + " ".join("M." + f for f in INLINE if f in used) + "."] + lines
        return "\n".join(lines), ctx['need']

def subst(script, ann):
    if 'SMT' in ann:
        script = script.replace("; smt().", "; smt(" + ann['SMT'] + ").")
    for k in sorted(ann, key=len, reverse=True):
        if k == 'SMT': continue
        script = re.sub(r'\b' + k + r'\b', '(' + ann[k] + ')', script)
    return script

if __name__ == '__main__':
    G = Gen(sys.argv[1])
    for n in sys.argv[2:]:
        s, need = G.script(n)
        print(f"== {n} need={sorted(need)}"); print(s)
