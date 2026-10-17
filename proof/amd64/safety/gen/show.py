import sys, gen, build
G=gen.Gen(build.MODEL)
def show(ss, ind=""):
    for s in gen.instrs(ss):
        if s.kind=='asgn':
            t=' '.join(s.text.split())
            if 'witness' in t: continue
            print(ind+f"[{s.id}] "+t[:160])
        elif s.kind=='call': print(ind+f"[{s.id}] CALL "+s.f+"("+", ".join(s.args)+")")
        elif s.kind=='if':
            print(ind+f"[{s.id}] IF#{s.ord} if ("+' '.join(s.cond.split())[:140]+")"); show(s.then, ind+"   "); print(ind+"   else"); show(s.els, ind+"   ")
        elif s.kind=='while':
            print(ind+f"[{s.id}] WHILE#{s.ord} while ("+' '.join(s.cond.split())+")"); show(s.body, ind+"   ")
for n in sys.argv[1:]:
    print("=====",n); show(G.P[n])
