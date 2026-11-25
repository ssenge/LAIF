"""Remove the continuous freedom of a solution: compute the Jacobian of the output state with respect to the angles,
find its null space (directions that keep the state), and pin one angle per null direction to a nice value
(multiples of pi/4 first, then arccos(sqrt(p/q)) + m pi/4 with small q), re-solving the others from a warm start.
usage: X0=x.npy python nullgauge.py n k 'skeleton' out.npy"""
import ast, math, os, sys
import numpy as np
from scipy.optimize import minimize
from search import dicke, gates, loss_grad, ry, cnot

n, k = int(sys.argv[1]), int(sys.argv[2]); skel = ast.literal_eval(sys.argv[3]); out = sys.argv[4]
g = gates(n, skel); target = dicke(n, k); x = np.load(os.environ["X0"])

def state(th):
    psi = np.zeros(2 ** n); psi[0] = 1; j = 0
    for op in g:
        if op[0] == "cx": psi = cnot(psi, n, op[1], op[2])
        else: psi = ry(psi, n, op[1], th[j]); j += 1
    return psi

def nullspace(th, pinned):
    h = 1e-6; base = state(th); free = [i for i in range(len(th)) if i not in pinned]
    J = np.empty((len(base), len(free)))
    for c, i in enumerate(free):
        e = np.zeros(len(th)); e[i] = h; J[:, c] = (state(th + e) - state(th - e)) / (2 * h)
    u, s, vt = np.linalg.svd(J, full_matrices=True)
    rank = int((s > 1e-7 * s[0]).sum())
    return free, vt[rank:]          # rows span the null space in the free coordinates

def resolve(th, pinned):
    free = [i for i in range(len(th)) if i not in pinned]
    def fun(y):
        z = th.copy(); z[free] = y; l, gr = loss_grad(z, n, g, target); return l, gr[free]
    r = minimize(fun, th[free], jac=True, method="L-BFGS-B", options={"maxiter": 5000, "ftol": 1e-18, "gtol": 1e-15})
    z = th.copy(); z[free] = r.x; return r.fun, z

nice = [m * math.pi / 4 for m in range(-4, 5)]
for q in range(2, 13):
    for p in range(1, q):
        if math.gcd(p, q) == 1:
            b = math.acos(math.sqrt(p / q))
            nice += [s * b + m * math.pi / 2 for s in (1, -1) for m in range(-2, 3)]
pinned = set()
while True:
    free, N = nullspace(x, pinned)
    print("null dimension", len(N), flush=True)
    if len(N) == 0: break
    weight = (N ** 2).sum(axis=0)                     # how much each free angle moves along the null space
    done = False
    for c in np.argsort(-weight):
        if weight[c] < 1e-6: break
        i = free[c]
        for v in sorted(nice, key=lambda v: abs((x[i] - v + math.pi) % (2 * math.pi) - math.pi))[:40]:
            th = x.copy(); th[i] = v; l, z = resolve(th, pinned | {i})
            if l < 1e-14:
                x = z; pinned.add(i); print("pinned", i, round(v / math.pi, 6), "pi", flush=True); done = True; break
        if done: break
    if not done: print("no nice pin found"); break
print("loss", loss_grad(x, n, g, target)[0]); np.save(out, x)
