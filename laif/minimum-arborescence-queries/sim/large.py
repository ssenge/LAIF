import sys, math
sys.dont_write_bytecode=True
import trees
for name in ("chain","hierarchy","binmerge"):
    f=trees.cases()[name]
    for n in (512,1024):
        W=f(n)
        for which in ("notes","fo"):
            m,T,G,extra,res=trees.measure(W,which)
            print(f"{name:10s} {n:5d} {which:6s} T/m={T/m:7.2f} G/n={G/n:7.2f} sqrt(TG)/n^1.5={math.sqrt(T*G)/n**1.5:7.2f} L={math.log2(n)+1:.0f} extra={extra}",flush=True)
