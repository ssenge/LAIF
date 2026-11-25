"""Interval-arithmetic certificate for the three-phase recursion (README, Lemma 1').
Phase F: the composite word F = Q o P (100 copies, G_F'(1) = 832) brings t0 = cos x, delta <= |x| <= 1, into an
invariant interval J_F around its attracting fixed point (about 0.4552). Phase A (10 copies) carries J_F into J_A,
and phase B (10 copies, superattracting at 1/sqrt 2) converges quadratically, as in certify.py.
All interval evaluations use outward rounding (mpmath.iv); compositions are evaluated as nested enclosures."""
import sys, math, sympy as sp
from mpmath import iv, mp, mpf
from poly import Gpoly, WA, WB, t
iv.dps = 40; mp.dps = 40
WP = [("n", 1), ("z", 2), ("n", 2), ("z", 2), ("n", 2), ("z", 2), ("n", 1), ("z", 1), ("n", 3)]
WQ = [("n", 2), ("z", 2), ("n", 1), ("z", 3), ("n", 3), ("z", 2), ("n", 2), ("z", 2), ("n", 2)]
co = lambda w: [int(c) for c in Gpoly(w).all_coeffs()]
GP, GQ, GA, GB = co(WP), co(WQ), co(WA), co(WB)
def quot(w):                                              # 1 - G(t) = (1 - t) P(t)
    q, r = sp.div(sp.Poly(1 - Gpoly(w).as_expr(), t), sp.Poly(1 - t, t)); assert r.is_zero; return [int(c) for c in q.all_coeffs()]
PP, PQ = quot(WP), quot(WQ)
gBx = Gpoly(WB).as_expr(); assert sp.simplify(gBx.subs(t, 1 / sp.sqrt(2)) - 1 / sp.sqrt(2)) == 0 and sp.simplify(sp.diff(gBx, t).subs(t, 1 / sp.sqrt(2))) == 0
dGB2 = [int(c) for c in sp.Poly(sp.diff(gBx, t, 2), t).all_coeffs()]
assert Gpoly(WP).as_expr().subs(t, 1) == 1 and Gpoly(WQ).as_expr().subs(t, 1) == 1
bP, bQ = sp.diff(Gpoly(WP).as_expr(), t).subs(t, 1), sp.diff(Gpoly(WQ).as_expr(), t).subs(t, 1); assert bP * bQ == 832, (bP, bQ)

def ev(c, X):
    y = iv.mpf(0)
    for a in c: y = y * X + a
    return y
I = lambda a, b: iv.mpf([a, b])
sub = lambda X, Y: X.a >= Y.a and X.b <= Y.b
def deriv(c):
    d = len(c) - 1; return [a * (d - i) for i, a in enumerate(c[:-1])]
def mv(c, X):
    m = iv.mpf(X.mid); return ev(c, m) + ev(deriv(c), X) * (X - m)
def img(c, X, n=64):
    pts = [X.a + (X.b - X.a) * i / n for i in range(n + 1)]
    Ys = [mv(c, I(pts[i], pts[i + 1])) for i in range(n)]
    return I(min(y.a for y in Ys), max(y.b for y in Ys))
def imgF(X, n=64):                                        # F = Q o P on pieces of X
    pts = [X.a + (X.b - X.a) * i / n for i in range(n + 1)]
    Ys = [mv(GQ, mv(GP, I(pts[i], pts[i + 1]))) for i in range(n)]
    return I(min(y.a for y in Ys), max(y.b for y in Ys))

KAPPA = mpf(sys.argv[1]) if len(sys.argv) > 1 else mpf("5e-4")
# (1) near 1: c <= (1 - F)/(1 - t) = P_P(t) P_Q(P(t)) <= C on [1 - kappa, 1]
cs, Cs = [], []
for i in range(400):
    X = I(1 - KAPPA + KAPPA * i / 400 - mpf('1e-30'), 1 + KAPPA * (i + 1 - 400) / 400 + mpf('1e-30'))
    Y = mv(PP, X) * mv(PQ, mv(GP, X)); cs.append(Y.a); Cs.append(Y.b)
c, C = min(cs), max(Cs); assert c > 1 and 1 - C * KAPPA > math.cos(1)
# (2) attracting fixed point of F and an invariant interval J_F
tF = mpf("0.4552")
for _ in range(400): tF = ev(GQ, ev(GP, iv.mpf(tF))).mid
dF = (ev(deriv(GQ), ev(GP, iv.mpf(tF))) * ev(deriv(GP), iv.mpf(tF))).mid
RF = mpf(sys.argv[2]) if len(sys.argv) > 2 else mpf("0.002")
JF = I(tF - RF, tF + RF); assert sub(imgF(JF), JF), "J_F not invariant"
# (3) every t in [cos 1, 1 - kappa] reaches J_F within K_F steps of F
KMAX = 60; worst = [0]
def reach(a, b, depth=0):
    Y = I(a, b)
    for k in range(1, KMAX + 1):
        Y = imgF(Y, 4)
        if sub(Y, JF): worst[0] = max(worst[0], k); return True
        if Y.delta > 0.5: break
    assert depth < 40, (a, b)
    m = (a + b) / 2; return reach(a, m, depth + 1) and reach(m, b, depth + 1)
N = int(sys.argv[3]) if len(sys.argv) > 3 else 4000; lo = mpf(math.cos(1)) - mpf("1e-9")
for i in range(N):
    assert reach(lo + (1 - KAPPA - lo) * i / N - mpf('1e-30'), lo + (1 - KAPPA - lo) * (i + 1) / N + mpf('1e-30'))
KF = worst[0]
# (4) J_F reaches J_A under A; J_A is invariant (as in certify.py)
tA = mpf("0.7071")
for _ in range(200): tA = ev(GA, iv.mpf(tA)).mid
JA = I(tA - mpf("0.005"), tA + mpf("0.005")); assert sub(img(GA, JA), JA)
Y = JF; KA = 0
while not sub(Y, JA):
    Y = img(GA, Y); KA += 1; assert KA < 60 and Y.delta < 1, "J_F does not reach J_A"
# (5) J_A reaches J_B under B, quadratic phase
ts = iv.sqrt(2) / 2; rho = mpf("0.01"); JB = I((ts - rho).a, (ts + rho).b)
M = max(abs(img(dGB2, JB).a), abs(img(dGB2, JB).b)) / 2; assert M * rho < 0.5 and M < mpf("3.3274")
Y = JA; KB = 0
while not sub(Y, JB):
    Y = img(GB, Y); KB += 1; assert KB < 60
print(f"kappa={float(KAPPA)}: c={float(c):.4f} C={float(C):.4f}  t_F={float(tF):.6f} F'(t_F)={float(dF):+.4f} r_F={float(RF)}  K_F={KF}  K_A={KA}  K_B={KB}  M={float(M):.4f}")
print(f"delta exponent 2 ln100/ln c = {2*math.log(100)/math.log(float(c)):.4f}")
