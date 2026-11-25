"""Polish a solution to full double precision with damped least squares on the state residual, keeping the given
angles fixed at their nearest nice values. usage: python polish.py n k 'skeleton' in.npy out.npy i1,i2,..."""
import ast, math, sys
import numpy as np
from scipy.optimize import least_squares
from search import dicke, gates, ry, cnot

n, k = int(sys.argv[1]), int(sys.argv[2]); skel = ast.literal_eval(sys.argv[3]); x = np.load(sys.argv[4]); out = sys.argv[5]
pin = [int(i) for i in sys.argv[6].split(",")] if len(sys.argv) > 6 and sys.argv[6] else []
g = gates(n, skel); target = dicke(n, k)
nice = [m * math.pi / 4 for m in range(-8, 9)]
for q in range(2, 13):
    for p in range(1, q):
        if math.gcd(p, q) == 1:
            b = math.acos(math.sqrt(p / q)); nice += [u * b + m * math.pi / 4 for u in (1, -1, 2, -2) for m in range(-8, 9)]
for i in pin:
    v = min(nice, key=lambda v: abs((x[i] - v + math.pi) % (2 * math.pi) - math.pi))
    print("pin", i, "moves by %.1e" % abs((x[i] - v + math.pi) % (2 * math.pi) - math.pi)); x[i] = v

def state(th):
    psi = np.zeros(2 ** n); psi[0] = 1; j = 0
    for op in g:
        if op[0] == "cx": psi = cnot(psi, n, op[1], op[2])
        else: psi = ry(psi, n, op[1], th[j]); j += 1
    return psi
sgn = 1.0 if state(x) @ target > 0 else -1.0
free = [i for i in range(len(x)) if i not in pin]
def res(y):
    z = x.copy(); z[free] = y; return state(z) - sgn * target
r = least_squares(res, x[free], method="lm", xtol=1e-15, ftol=1e-15, gtol=1e-15, max_nfev=20000)
x[free] = r.x; print("residual norm %.2e" % np.linalg.norm(res(r.x))); np.save(out, x)
