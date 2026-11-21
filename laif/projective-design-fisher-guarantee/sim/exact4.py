"""Solve the optimality system for t=4 on qubits in high precision: dual polynomial q touching f at 4 orbits,
primal weights matching the Haar moments."""
import mpmath as mp
import numpy as np
from dual2d import solve, basis
mp.mp.dps = 50
B = basis(4)
def hm(a, c):
    if c % 2: return mp.mpf(0)
    return 2 * mp.gamma(a + mp.mpf(1) / 2) * mp.gamma(mp.mpf(1) / 2) * mp.gamma(mp.mpf(c + 1) / 2) / mp.gamma(mp.mpf(2 * a + c + 3) / 2) / (4 * mp.pi)
def q(co, z, u): return sum(c * u ** a * z ** b for c, (a, b) in zip(co, B))
def g(co, z, u): return u - (1 + z) * q(co, z, u)
def F(*v):
    co = v[:9]; z1, z2, u2, z3, z4, w1, w2, w3 = v[9:]
    w4 = 1 - w1 - w2 - w3
    gz = lambda z, u: mp.diff(lambda s: g(co, s, u), z)
    gu = lambda z, u: mp.diff(lambda s: g(co, z, s), u)
    u4 = 1 - z4 ** 2
    eqs = [g(co, z1, 0), gz(z1, 0), g(co, z2, u2), gz(z2, u2), gu(z2, u2), g(co, z3, 0), gz(z3, 0), g(co, z4, u4),
           gz(z4, u4) - 2 * z4 * gu(z4, u4)]
    P = [(z1, 0, w1), (z2, u2, w2), (z3, 0, w3), (z4, u4, w4)]
    eqs += [sum(w * u ** a * z ** b for z, u, w in P) - hm(a, b) for a, b in B]
    return eqs
v0, Bn, coef, *_ = solve(4, 400)
x0 = list(coef) + [-0.858, -0.25, 0.677, 0.360, 0.802, 0.188, 0.38, 0.213]
sol = mp.findroot(F, x0, tol=1e-40, maxsteps=200)
co = sol[:9]; z1, z2, u2, z3, z4, w1, w2, w3 = sol[9:]; w4 = 1 - w1 - w2 - w3
val = sum(c * hm(a, b) for c, (a, b) in zip(co, B))
prim = w1 * 0 + w2 * u2 / (1 + z2) + w3 * 0 + w4 * (1 - z4 ** 2) / (1 + z4)
print("LP grid value", v0)
print("dual value  ", val); print("primal value", prim)
assert abs(val - prim) < mp.mpf(10) ** -40
print("points", z1, z2, u2, z3, z4); print("weights", w1, w2, w3, w4)

# global check of the dual inequality on a fine grid, and the polynomial at higher precision
import numpy as np
cf = [float(c) for c in co]
zz = np.cos(np.linspace(0, np.pi, 3001)); worst = 1
for z in zz:
    uu = np.linspace(0, 1 - z * z, 801)
    gv = uu - (1 + z) * sum(c * uu ** a * z ** b for c, (a, b) in zip(cf, B))
    worst = min(worst, gv.min())
print("min of g on grid:", worst)
assert worst >= -1e-12
mp.mp.dps = 90
sol2 = mp.findroot(F, list(sol), tol=1e-80, maxsteps=100)
val2 = sum(c * hm(a, b) for c, (a, b) in zip(sol2[:9], B))
print("value(90 digits)", mp.nstr(val2, 60))
import json
json.dump([mp.nstr(x, 85) for x in sol2], open("sol_t4.json", "w"))
