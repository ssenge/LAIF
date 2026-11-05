"""Does a richer label scheme beat the symmetric three-label one? Free array Theta(d,L), several
labels of each kind, free split t on each {0,1}x{0,1} label, no symmetry. Random restarts."""
import math, random, sys
from opt import H, seven_sum, inner, best, quantum

KINDS = "AABC"  # two labels of kind A allowed

def evaluate(p, v):
    n = len(KINDS)
    th = [[abs(x) for x in v[i*n:(i+1)*n]] for i in range(3)]
    rows = [(1-p)/2, p, (1-p)/2]            # d = -1, 0, +1
    for i in range(3):
        s = sum(th[i]) or 1
        th[i] = [x/s*rows[i] for x in th[i]]
    ts = [min(1, abs(x)) for x in v[3*n:]]
    cols = [sum(th[i][j] for i in range(3)) for j in range(n)]
    a = max(0.0, H(*cols) - sum(rows[i]*H(*th[i]) for i in range(3)))
    u = w = l = 0.0
    for j, k in enumerate(KINDS):
        m, z, q = th[0][j], th[1][j], th[2][j]
        if k == "A":
            t = ts[j]
            u += cols[j]*H(q + t*z, m + (1-t)*z)    # x=1 on d=+1 and on share t of zeros
            w += cols[j]*H(m + t*z, q + (1-t)*z)    # y=1 on d=-1 and on the same share
            l += z*H(t, 1-t)
        elif k == "B":
            u += cols[j]*H(m, z, q)
        else:
            w += cols[j]*H(m, z, q)
    return a/2 + inner((u+w)/2, l)

def search(p, restarts=40, iters=4000):
    bestv = math.inf
    n = len(KINDS)
    for _ in range(restarts):
        v = [random.random() for _ in range(3*n)] + [random.random() for _ in range(n)]
        c, step = evaluate(p, v), 0.3
        for it in range(iters):
            w = [x + random.gauss(0, step) if random.random() < .3 else x for x in v]
            d = evaluate(p, w)
            if d < c:
                v, c = w, d
            elif it % 200 == 199:
                step = max(step*.8, 1e-4)
        bestv = min(bestv, c)
    return bestv

random.seed(1)
for p in (.2, .225, .25, .275, .3, .35):
    print(p, "symmetric", round(best(p, quantum)[0], 5), "free", round(search(p), 5), flush=True)
