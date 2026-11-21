"""Rational certificates for eta_des(2,t) from the high-precision KKT solution sol_t{t}.json (exact_t.py)."""
import sys, json
from fractions import Fraction as Fr
import mpmath as mp
import cert4
from exact_t import basis

t = int(sys.argv[1]); mp.mp.dps = 60
D = json.load(open(f"sol_t{t}.json"))
B = [tuple(b) for b in D["basis"]]; assert B == basis(t)
cert4.B = B
co = [mp.mpf(c) for c in D["sol_co"]]
DEN = 10 ** 14; EPS = Fr(1, 10 ** 8)
qc = [Fr(int(mp.nint(c * DEN)), DEN) for c in co]
qc[B.index((0, 0))] -= EPS
low = sum(c * cert4.haar(a, cc) for c, (a, cc) in zip(qc, B))
ok, boxes = cert4.certify_nonneg(cert4.poly_h(qc))
print(f"t={t}: dual certificate nonnegative: {ok}, boxes {boxes}")
assert ok
def rat(x, den=10 ** 6): return Fr(int(mp.nint(mp.mpf(x) * den)), den)
pts = []
for (zs, us), kind in zip(D["pts"], D["kinds"]):
    for k in range(-3, 4):
        z = rat(zs) + Fr(k, 10 ** 5)
        if kind == 'b0': pts.append((z, Fr(0)))
        elif kind == 'b1': pts.append((z, 1 - z * z))
        else:
            for l in range(-3, 4): pts.append((z, rat(us) + Fr(l, 10 ** 5)))
pts = [(z, u) for z, u in pts if -1 < z <= 1 and 0 <= u <= 1 - z * z]
high, support = cert4.primal(pts)
print(f"lower {float(low):.12f}  upper {float(high):.12f}  width {float(high - low):.2e}")
assert low <= high
json.dump({"t": t, "q": [str(c) for c in qc], "basis": B, "lower": str(low), "upper": str(high),
           "design": [[str(z), str(u), str(w)] for (z, u), w in support]}, open(f"cert_t{t}.json", "w"), indent=1)
