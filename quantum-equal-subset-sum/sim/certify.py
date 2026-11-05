"""Certify sup_p min(7-SUM(p), labels(p)) <= 0.4384 by interval arithmetic.
Parameters are piecewise linear in p, knots from exact.py. Upper bounds only need valid parameters."""
from mpmath import iv, mpf
import numpy as np
from exact import labels
from opt import scheme, inner

iv.dps = 30
BOUND = 0.4384
LO, HI = 0.20, 0.47
knots = np.linspace(LO, HI, 55)
vals = []
for p in knots:
    c, (a1, a0) = labels(float(p))
    a1, a0 = min(a1, (1-p)/2 - .02), min(a0, p - .02)      # keep every entry of the array positive
    a, u, l = scheme(float(p), a1, a0)
    vals.append((a1, a0, max(0.0, (4*u-10*l)/7)))
vals = np.array(vals)

def xlogx(x):                       # -x log2 x on an interval inside (0,1]; monotone pieces handled by iv
    return -x*iv.log(x)/iv.log(2)

def Hiv(parts):
    s = sum(parts)
    return sum(xlogx(q) for q in parts) - xlogx(s)      # s H(parts/s), the form the exponents use

def cost(pl, pr):
    p = iv.mpf([pl, pr])
    i = min(np.searchsorted(knots, (pl+pr)/2, side="right")-1, len(knots)-2)
    t = (p - float(knots[i])) / float(knots[i+1]-knots[i])
    a1, a0, s = [float(vals[i][j]) + t*float(vals[i+1][j]-vals[i][j]) for j in range(3)]
    b1, b0 = ((1-p) - 2*a1)/4, (p - a0)/2
    ca, cb = 2*a1 + a0, 2*b1 + b0
    x1 = a1 + a0/2
    # a = H(cols) - sum_d H(row d); all entries stay positive on this range
    a = xlogx(ca) + 2*xlogx(cb) - (2*(Hiv([a1, b1, b1])) + Hiv([a0, b0, b0]))
    u = Hiv([x1, x1]) + Hiv([b1, b0, b1])
    l = a0
    table = l + s
    walk = s/2 + 2*(u - l - s)/3
    tlen = u - l - s                # exponent of T
    return a/2 + iv.mpf([min(table.a, walk.a), max(table.b, walk.b)]), (min(float(a1.a), float(a0.a), float(b1.a), float(b0.a)), float(s.a), float(table.a), float(tlen.a))

def sup(pl, pr, depth=0):
    c, m = cost(pl, pr)
    if float(c.b) <= BOUND or depth > 24:
        return float(c.b), m, 1
    mid = (pl + pr)/2
    a, b = sup(pl, mid, depth+1), sup(mid, pr, depth+1)
    return max(a[0], b[0]), tuple(map(min, a[1], b[1])), a[2] + b[2]

worst, lo, boxes = 0.0, (1.0, 1.0, 1.0, 1.0), 0
for k in range(len(knots)-1):
    w, m, c = sup(float(knots[k]), float(knots[k+1]))
    worst, lo, boxes = max(worst, w), tuple(map(min, lo, m)), boxes + c
print(f"labels on [{LO},{HI}]: every box <= {worst:.6f}; {boxes} boxes")
print(f"smallest array entry {lo[0]:.5f}, sigma {lo[1]:.5f}, exponent of P0 {lo[2]:.5f}, exponent of T {lo[3]:.5f}")
assert worst <= BOUND and lo[0] > 0 and lo[1] >= 0 and lo[2] >= 0.38 and lo[3] >= 0.36

# The empty label covers the rest: S(p) increases on [0,1/3] and decreases on [1/3,1]
def seven(p):
    p = iv.mpf(p)
    return (xlogx(p) + xlogx(1-p) + 1 - p) * 2/7
print("S(p) at p=%g: %.5f, at p=%g: %.5f" % (LO, float(seven(LO).b), HI, float(seven(HI).b)))
assert float(seven(LO).b) <= BOUND and float(seven(HI).b) <= BOUND
print("certified: exponent <=", BOUND)
