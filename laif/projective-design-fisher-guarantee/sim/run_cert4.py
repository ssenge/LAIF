"""Build and check the rational certificates for eta_des(2,4); prints the bracket."""
import json
from fractions import Fraction as Fr
import mpmath as mp
from cert4 import B, haar, poly_h, certify_nonneg, primal

mp.mp.dps = 85
sol = [mp.mpf(x) for x in json.load(open("sol_t4.json"))]
co = sol[:9]; z1, z2, u2, z3, z4 = sol[9:14]
DEN = 10 ** 14; EPS = Fr(1, 10 ** 8)
qc = [Fr(int(mp.nint(c * DEN)), DEN) for c in co]
qc[B.index((0, 0))] -= EPS                       # shift down so that h > 0 off the touching set
low = sum(c * haar(a, cc) for c, (a, cc) in zip(qc, B))
h = poly_h(qc)
ok, boxes = certify_nonneg(h)
print("dual certificate nonnegative:", ok, "boxes", boxes)
assert ok
# primal: rational points near the optimal support
def rat(x, den=10 ** 6): return Fr(int(mp.nint(x * den)), den)
pts = []
for k in range(-3, 4):
    d = Fr(k, 10 ** 5)
    pts += [(rat(z1) + d, Fr(0)), (rat(z3) + d, Fr(0))]
    zz = rat(z4) + d; pts.append((zz, 1 - zz * zz))
    for l in range(-3, 4):
        pts.append((rat(z2) + d, rat(u2) + Fr(l, 10 ** 5)))
pts = [(z, u) for z, u in pts if 0 <= u <= 1 - z * z]
high, support = primal(pts)
print("lower bound", low, "=", float(low))
print("upper bound", high, "=", float(high))
print("width", float(high - low))
assert low <= high and low > Fr(37793, 100000) and high < Fr(38889, 100000)
json.dump({"q": [str(c) for c in qc], "basis": B, "lower": str(low), "upper": str(high),
           "design": [[str(z), str(u), str(w)] for (z, u), w in support]}, open("cert_t4.json", "w"), indent=1)
print("support", [(float(z), float(u), float(w)) for (z, u), w in support])
