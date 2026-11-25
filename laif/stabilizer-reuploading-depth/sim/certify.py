"""Interval-arithmetic certificate for the two-phase recursion (README, Lemma 2).
Phase A (expansion map, 10 copies) brings t0 = cos x, delta <= |x| <= 1, into J_A; phase B (10 copies, superattracting
at t* = 1/sqrt 2) then converges quadratically. All interval evaluations use outward rounding (mpmath.iv)."""
import sys, math, sympy as sp
from mpmath import iv, mp, mpf
from poly import Gpoly, WA, WB, t
iv.dps = 40; mp.dps = 40
GA = [int(c) for c in Gpoly(WA).all_coeffs()]; GB = [int(c) for c in Gpoly(WB).all_coeffs()]
q, r = sp.div(sp.Poly(1 - Gpoly(WA).as_expr(), t), sp.Poly(1 - t, t)); assert r.is_zero
PA = [int(c) for c in q.all_coeffs()]                      # 1 - G_A(t) = (1 - t) P_A(t)
dGB2 = [int(c) for c in sp.Poly(sp.diff(Gpoly(WB).as_expr(), t, 2), t).all_coeffs()]

def ev(c, X):                                             # Horner in interval arithmetic
    y = iv.mpf(0)
    for a in c: y = y * X + a
    return y
I = lambda a, b: iv.mpf([a, b])
sub = lambda X, Y: X.a >= Y.a and X.b <= Y.b
def deriv(c):
    d = len(c) - 1; return [a * (d - i) for i, a in enumerate(c[:-1])]
def mv(c, X):                                             # mean-value form G(m) + G'(X)(X - m), rigorous enclosure
    m = iv.mpf(X.mid); return ev(c, m) + ev(deriv(c), X) * (X - m)
def img(c, X, n=64):                                      # hull of enclosures over n pieces of X
    pts = [X.a + (X.b - X.a) * i / n for i in range(n + 1)]
    Ys = [mv(c, I(pts[i], pts[i + 1])) for i in range(n)]
    return I(min(y.a for y in Ys), max(y.b for y in Ys))

KAPPA = mpf(sys.argv[1]) if len(sys.argv) > 1 else mpf("1e-3")
# (1) near 1: c <= P_A <= C on [1 - kappa, 1]
cs, Cs = [], []
for i in range(200):
    X = I(1 - KAPPA + KAPPA * i / 200, 1 - KAPPA + KAPPA * (i + 1) / 200); Y = mv(PA, X); cs.append(Y.a); Cs.append(Y.b)
c, C = min(cs), max(Cs); assert c > 1 and 1 - C * KAPPA > math.cos(1)
# (2) the attracting fixed point of A and an invariant interval J_A
tA = mpf("0.7071"); 
for _ in range(200): tA = ev(GA, iv.mpf(tA)).mid
JA = I(tA - mpf("0.005"), tA + mpf("0.005")); assert sub(img(GA, JA), JA)
# (3) every t in R = [cos 1, 1 - kappa] reaches J_A within K_A steps of A
KMAX = 40; worst = [0]
def reach(a, b, depth=0):
    Y = I(a, b)
    for k in range(1, KMAX + 1):
        Y = img(GA, Y, 4)
        if sub(Y, JA): worst[0] = max(worst[0], k); return True
        if Y.delta > 0.5: break
    assert depth < 40, (a, b)
    m = (a + b) / 2; return reach(a, m, depth + 1) and reach(m, b, depth + 1)
N = 2000; lo = mpf(math.cos(1)) - mpf("1e-9")
for i in range(N):
    assert reach(lo + (1 - KAPPA - lo) * i / N, lo + (1 - KAPPA - lo) * (i + 1) / N)
KA = worst[0]
# (4) J_A reaches J_B = [t* - rho, t* + rho] within K_B steps of B, and |G_B(t) - t*| <= M (t - t*)^2 on J_B
ts = iv.sqrt(2) / 2; rho = mpf("0.01")
JB = I((ts - rho).a, (ts + rho).b)
M = max(abs(img(dGB2, JB).a), abs(img(dGB2, JB).b)) / 2; assert M * rho < 0.5
Y = JA; KB = 0
while not sub(Y, JB):
    Y = img(GB, Y); KB += 1; assert KB < 60 and Y.delta < 1
print(f"kappa={float(KAPPA)}: c={float(c):.4f} C={float(C):.4f}  t_A={float(tA):.6f}  K_A={KA}  K_B={KB}  M={float(M):.4f} rho={float(rho)}")
print(f"delta exponent 2 ln10/ln c = {2*math.log(10)/math.log(float(c)):.4f}")
