"""Exact certificates for eta_des(d,t), d >= 3, from the cutting-plane solution (exchange_qudit.py)."""
import sys, json, numpy as np
from fractions import Fraction as Fr
from scipy.optimize import linprog
from cert_qudit import basis, haar, h_poly, certify
from cert4 import solve_exact
d, t = int(sys.argv[1]), int(sys.argv[2])
D = json.load(open(f"exch_d{d}_t{t}.json")); P = np.load(f"exch_d{d}_t{t}_P.npy")
Bs = basis(t)
DEN = 10 ** 13
qc = [Fr(int(round(v * DEN)), DEN) for v in D["q"]]
# violation of the float dual on faces and edges of the cube (fine grids), plus the search value
from exchange_qudit import mono3, fval
qf = np.array(D["q"]); vmax = D["viol"]; g = np.linspace(0, 1, 801)
for fix in [(0, 0), (0, 1), (1, 0), (1, 1), (2, 0), (2, 1)]:
    X, Y = np.meshgrid(g, g); pts = [None] * 3; k = [i for i in range(3) if i != fix[0]]
    pts[fix[0]] = np.full(X.size, float(fix[1])); pts[k[0]] = X.ravel(); pts[k[1]] = Y.ravel()
    hv = fval(*pts, d) - qf @ mono3(*pts, Bs); vmax = max(vmax, -hv.min())
print("max violation incl. faces", vmax)
shift = Fr(int(2 * vmax * DEN) + 100, DEN)
qc[Bs.index((0, 0, 0))] -= shift
low = sum(c * haar(i, j, l, d) for c, (i, j, l) in zip(qc, Bs))
h0 = {}
for c, (i, j, l) in zip(qc, Bs):
    if i == 0 and l == 0: h0[(j,)] = h0.get((j,), Fr(0)) - c
ok0, n0, _ = certify({k: v for k, v in h0.items() if v != 0}, 1)
ok, n, bad = certify(h_poly(qc, Bs, d), 3, maxdepth=60)
print(f"d={d} t={t}: a=0 face {ok0} ({n0} boxes); h >= 0 {ok} ({n} boxes); lower {float(low):.10f}")
assert ok and ok0
# primal on rationalized points (a, s, c) -> (a, b = s(1-a), c)
R = [(Fr(int(round(a * 10 ** 8)), 10 ** 8), Fr(int(round(s * 10 ** 8)), 10 ** 8), Fr(int(round(c * 10 ** 8)), 10 ** 8)) for a, s, c in P]
R = [(a, s * (1 - a), c) for a, s, c in R if 0 <= a <= 1 and 0 <= s <= 1 and 0 <= c <= 1]
A = np.array([[float(a ** i * b ** j * (a * b * c) ** l) for (a, b, c) in R] for i, j, l in Bs])
rhs = [haar(i, j, l, d) for i, j, l in Bs]
f = np.array([float(d * b * c) if a > 0 else 0.0 for a, b, c in R])
res = linprog(f, A_eq=A, b_eq=[float(x) for x in rhs], bounds=(0, None), method="highs")
order = list(np.argsort(-res.x)); sup = [i for i in order if res.x[i] > 1e-13]
w = None
for _ in range(len(R)):
    M = [[R[k][0] ** i * R[k][1] ** j * (R[k][0] * R[k][1] * R[k][2]) ** l for k in sup] for i, j, l in Bs]
    w = solve_exact(M, rhs)
    if w is not None: break
    sup.append(order[len(sup)])
assert w is not None and all(x >= 0 for x in w)
high = sum(wi * (d * R[k][1] * R[k][2] if R[k][0] > 0 else 0) for wi, k in zip(w, sup))
print(f"  upper {float(high):.10f}  width {float(high - low):.2e}  support {len(sup)}")
assert low <= high
json.dump({"d": d, "t": t, "basis": Bs, "q": [str(c) for c in qc], "lower": str(low), "upper": str(high),
           "design": [[str(R[k][0]), str(R[k][1]), str(R[k][2]), str(wi)] for wi, k in zip(w, sup)]},
          open(f"cert_d{d}_t{t}.json", "w"), indent=1)
