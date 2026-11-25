"""Local search over CNOT placements: mutate one CNOT of the placement, re-optimize the rotations from the current
angles (warm start, plus one random restart), accept by a annealing rule on log(loss).
usage: python anneal.py n k c steps seed [EDGES env as in search.py]"""
import itertools, math, os, sys
import numpy as np
from scipy.optimize import minimize
from search import dicke, gates, loss_grad

n, k, c, steps, seed = map(int, sys.argv[1:6]); rng = np.random.default_rng(seed); target = dicke(n, k)
pairs = list(itertools.permutations(range(n), 2))
if "EDGES" in os.environ:
    und = [tuple(map(int, e.split("-"))) for e in os.environ["EDGES"].split(",")]; pairs = und + [(b, a) for a, b in und]

def angle_slots(skel):          # number of rotations: n initial + 2 per CNOT
    return n + 2 * len(skel)

def opt(skel, x0):
    g = gates(n, skel); best = (9.0, None)
    for t, init in enumerate([x0, rng.uniform(0, 2 * math.pi, angle_slots(skel))]):
        r = minimize(loss_grad, init, args=(n, g, target), jac=True, method="L-BFGS-B",
                     options={"maxiter": 3000, "ftol": 1e-16, "gtol": 1e-12})
        if r.fun < best[0]: best = (r.fun, r.x)
        if best[0] < 1e-12: break
    return best

skel = [pairs[i] for i in rng.integers(len(pairs), size=c)]
L, x = opt(skel, rng.uniform(0, 2 * math.pi, angle_slots(skel)))
T = 1.0
for step in range(steps):
    j = rng.integers(c); new = list(skel); new[j] = pairs[rng.integers(len(pairs))]
    if new == skel: continue
    L2, x2 = opt(new, x)              # the rotations keep their slots, so x is a warm start
    if L2 < 1e-12:
        print("HIT", new, L2, "step", step, flush=True); np.save("hit_%d_%d_%d.npy" % (n, k, c), x2); break
    if math.log(L2 + 1e-16) < math.log(L + 1e-16) or rng.random() < math.exp(-(math.log(L2 + 1e-16) - math.log(L + 1e-16)) / T):
        skel, L, x = new, L2, x2
    T = max(0.05, T * 0.997)
    if step % 50 == 0: print("step", step, "loss %.3e" % L, flush=True)
print("done n=%d k=%d c=%d final loss %.3e" % (n, k, c, L))
