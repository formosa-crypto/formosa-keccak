"""Minimal parser for jasmin2ec -m safety models: procedures -> statement trees."""
import re

class Stmt:
    def __init__(self, kind, **kw):
        self.kind = kind  # 'asgn' | 'call' | 'if' | 'while' | 'comment'
        self.__dict__.update(kw)
    def __repr__(self):
        return f"<{self.kind} {getattr(self,'text','')[:40]!r}>"

def _match_paren(s, i, o='(', c=')'):
    d = 0
    while i < len(s):
        if s[i] == o: d += 1
        elif s[i] == c:
            d -= 1
            if d == 0: return i
        i += 1
    raise ValueError("unbalanced")

def parse_block(s):
    """parse statements in string s (contents between braces)"""
    out = []; i = 0; n = len(s)
    while i < n:
        while i < n and s[i] in ' \t\n': i += 1
        if i >= n: break
        if s.startswith('(*', i):
            j = s.index('*)', i) + 2; out.append(Stmt('comment', text=s[i:j])); i = j; continue
        if s.startswith('if ', i) or s.startswith('if(', i):
            j = s.index('(', i); k = _match_paren(s, j); cond = s[j+1:k]
            b1 = s.index('{', k); e1 = _match_paren(s, b1, '{', '}')
            then = parse_block(s[b1+1:e1]); i = e1 + 1
            while i < n and s[i] in ' \t\n': i += 1
            els = []
            if s.startswith('else', i):
                b2 = s.index('{', i); e2 = _match_paren(s, b2, '{', '}')
                els = parse_block(s[b2+1:e2]); i = e2 + 1
            out.append(Stmt('if', cond=cond, then=then, els=els)); continue
        if s.startswith('while ', i) or s.startswith('while(', i):
            j = s.index('(', i); k = _match_paren(s, j); cond = s[j+1:k]
            b1 = s.index('{', k); e1 = _match_paren(s, b1, '{', '}')
            body = parse_block(s[b1+1:e1]); i = e1 + 1
            out.append(Stmt('while', cond=cond, body=body)); continue
        # simple statement until ';' at depth 0
        j = i; d = 0
        while j < n:
            ch = s[j]
            if ch in '([{': d += 1
            elif ch in ')]}': d -= 1
            elif ch == ';' and d == 0: break
            j += 1
        text = s[i:j].strip(); i = j + 1
        if '<@' in text:
            m = re.match(r'(.*?)<@\s*([A-Za-z0-9_]+)\s*\((.*)\)\s*$', text, re.S)
            lhs, f, args = m.group(1), m.group(2), m.group(3)
            out.append(Stmt('call', text=text, f=f, args=split_args(args), lhs=lhs))
        else:
            out.append(Stmt('asgn', text=text))
    return out

def split_args(a):
    res = []; d = 0; cur = ''
    for ch in a:
        if ch in '([{': d += 1
        if ch in ')]}': d -= 1
        if ch == ',' and d == 0: res.append(cur.strip()); cur = ''
        else: cur += ch
    if cur.strip(): res.append(cur.strip())
    return [re.sub(r'\s+', ' ', x) for x in res]

def procs(path):
    txt = open(path).read()
    m0 = txt.index('module M = {')
    res = {}
    for m in re.finditer(r'\n  proc ([A-Za-z0-9_]+) \(', txt[m0:]):
        name = m.group(1); st = m0 + m.start()
        b = txt.index('{', txt.index(')', st))   # body start after signature
        # signature may contain ':' types; find the '= {' that opens body
        b = txt.index('= {', st) + 2
        e = _match_paren(txt, b, '{', '}')
        body = txt[b+1:e]
        body = re.sub(r'(?m)^\s*var [^;]*;\s*$', '', body)
        stmts = parse_block(body)
        res[name] = stmts
    return res

def stats(stmts):
    c = {'if':0,'while':0,'call':0,'asgn':0}
    def go(ss):
        for s in ss:
            if s.kind in c: c[s.kind]+=1
            if s.kind=='if': go(s.then); go(s.els)
            if s.kind=='while': go(s.body)
    go(stmts); return c

def has(ss, kinds):
    for s in ss:
        if s.kind in kinds: return True
        if s.kind=='if' and (has(s.then,kinds) or has(s.els,kinds)): return True
        if s.kind=='while' and has(s.body,kinds): return True
    return False
