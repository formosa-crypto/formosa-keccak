"""State formulas for the absorb (read) and squeeze (write) cascades."""
def B(t): return f"(if {t} <> 0 then 1 else 0)"

def jlen(c, a0, l0):
    e = f"({a0} + {l0})"
    return f"(if {c} <= {a0} then {l0} else if {c} <= {e} then {e} - {c} else 0)"

def J(c, a0="_aT", l0="__LEN", t0="__TRAILB", at="aT", ln="_LEN", tr="_TRAILB", ptr=None, p0=None, delta=None):
    """state after the blocks below byte position c have been processed"""
    e = f"({a0} + {l0})"
    pos = f"(if {c} <= {a0} then {a0} else if {c} <= {e} then {c} else {e} + {B(t0)})"
    trl = f"(if {c} <= {e} then {t0} else 0)"
    s = f"{at} = {pos}"
    if ln: s += f" /\\ {ln} = {jlen(c, a0, l0)}"
    if tr: s += f" /\\ {tr} = {trl}"
    if ptr: s += f" /\\ {ptr} = {p0} + ({l0} - {jlen(c, a0, l0)})"
    if delta: s += f" /\\ {delta} = {l0} - {jlen(c, a0, l0)}"
    return s

def W(k, l0="__LEN", ln="_LEN", ptr=None, p0=None, delta=None):
    """state after writing the blocks of cumulative capacity k"""
    m = f"(if {l0} < {k} then {l0} else {k})"
    s = f"{ln} = {l0} - {m}"
    if ptr: s += f" /\\ {ptr} = {p0} + {m}"
    if delta: s += f" /\\ {delta} = {m}"
    return s
