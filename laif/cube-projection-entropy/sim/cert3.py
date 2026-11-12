# Certificate for n = 3: K(c) = E[phi(3/2 + c.U)] < K(e) on the sector of |c|^2 = 3/4, c != e = (1/2, 1/2, 1/2).
# phi = -log f, f = density of the sum of three uniforms on [0, 1]; U uniform on [-1, 1]^3.
# All bounds use interval arithmetic (mpmath.iv); vertex directions are exact rationals.
import sys
from fractions import Fraction as Fr
from math import comb, factorial
from mpmath import iv, mp
iv.prec = 200
I = lambda x: iv.mpf(x) if not isinstance(x, Fr) else iv.mpf(x.numerator) / iv.mpf(x.denominator)
S3 = iv.sqrt(3)
R1, R2 = (3 - S3) / 2, (3 + S3) / 2
LOG2 = iv.log(2)

def int_ulog(A, sg, k, u0, u1):
    """int_{u0}^{u1} (A + sg*u)^k log(u) du, u0, u1 >= 0 (u = 0 contributes the limit 0)."""
    tot = iv.mpf(0)
    for j in range(k + 1):
        c = comb(k, j) * A ** (k - j) * (sg ** j)
        F = lambda u: iv.mpf(0) if u == 0 else u ** (j + 1) * (iv.log(u) / (j + 1) - iv.mpf(1) / (j + 1) ** 2)
        tot += c * (F(u1) - F(u0))
    return tot

def int_poly(b, k, lo, hi):
    return ((hi - b) ** (k + 1) - (lo - b) ** (k + 1)) / (k + 1)

def Psi(k, b):
    """int_b^3 (s - b)^k phi(s) ds for b in [0, 3]."""
    for brk in (1, 2):
        if b.a < brk < b.b:
            raise ValueError("breakpoint straddle")
    tot = iv.mpf(0)
    if b.b <= 1:  # piece [b, 1]: phi = log 2 - 2 log s
        tot += LOG2 * int_poly(b, k, b, iv.mpf(1)) - 2 * int_log_piece(b, k, b, iv.mpf(1), iv.mpf(0), 1)
    if b.b <= 2:  # piece [max(b,1), 2]: phi = -log(s - r1) - log(r2 - s)
        lo = b if b.a >= 1 else iv.mpf(1)
        tot += -int_log_piece(b, k, lo, iv.mpf(2), R1, 1) - int_log_piece(b, k, lo, iv.mpf(2), R2, -1)
    lo = b if b.a >= 2 else iv.mpf(2)  # piece [max(b,2), 3]: phi = log 2 - 2 log(3 - s)
    tot += LOG2 * int_poly(b, k, lo, iv.mpf(3)) - 2 * int_log_piece(b, k, lo, iv.mpf(3), iv.mpf(3), -1)
    return tot

def K(c):
    """K(c) for c given as a list of intervals (zero entries exactly zero allowed)."""
    nz = [x for x in c if not (x.a == 0 and x.b == 0)]
    m = len(nz)
    if sum(abs(x) for x in nz).b >= iv.mpf(3) / 2 and not all(x.a == x.b == iv.mpf(0.5).a for x in nz):
        return None  # support reaches the singularity
    tot = iv.mpf(0)
    for mask in range(2 ** m):
        eps = [1 - 2 * ((mask >> i) & 1) for i in range(m)]
        sgn = 1
        for e_ in eps: sgn *= e_
        b = iv.mpf(1.5) - sum(e_ * x for e_, x in zip(eps, nz))
        tot += sgn * Psi(m - 1, b)
    den = iv.mpf(factorial(m - 1) * 2 ** m)
    for x in nz: den *= x
    return tot / den

def int_log_piece(b, k, lo, hi, r, sg):
    """int_lo^hi (s - b)^k log(sg*(s - r)) ds, via u = sg*(s - r)."""
    A = r - b
    if sg > 0:
        return int_ulog(A, 1, k, lo - r, hi - r)
    return int_ulog(A, -1, k, r - hi, r - lo)

E = [iv.mpf(0.5)] * 3
KE = K(E)

def check_numeric():
    """Compare K with direct numerical quadrature at random points (sanity, not part of the proof)."""
    import random
    mp.dps = 30
    f = lambda s: s * s / 2 if s <= 1 else ((-2 * s * s + 6 * s - 3) / 2 if s <= 2 else (3 - s) ** 2 / 2)
    random.seed(1)
    for _ in range(4):
        c = sorted([random.random() for _ in range(3)], reverse=True)
        nrm = sum(x * x for x in c) ** 0.5
        c = [x / nrm * (0.75 ** 0.5) for x in c]
        val = K([iv.mpf(x) for x in c])
        # density of 3/2 + sum c_i U_i by truncated powers
        import itertools
        def p(s):
            t = 0
            for eps in itertools.product([1, -1], repeat=3):
                b = 1.5 - sum(e_ * x for e_, x in zip(eps, c))
                t += eps[0] * eps[1] * eps[2] * max(s - b, 0) ** 2
            return t / (16 * c[0] * c[1] * c[2])
        brk = sorted(set([1.5 - sum(e_ * x for e_, x in zip(eps, c)) for eps in itertools.product([1, -1], repeat=3)] + [1, 2]))
        brk = [x for x in brk if 1.5 - sum(c) <= x <= 1.5 + sum(c)]
        num = mp.quad(lambda s: p(float(s)) * -mp.log(f(float(s))) if p(float(s)) > 0 else 0, brk)
        assert abs(float(val.mid) - float(num)) < 1e-8, (c, val, num)
    print("numeric check of K: ok")
    # alpha = 2 int m(s) phi''(s) ds with m(s) ds = E[(W1 - W2)^2; W1 + W2 + W3 in ds]; m is a polynomial on each of [0, 1], [1, 2], [2, 3]
    m0 = lambda s: s ** 4 / 12
    m1 = lambda s: -s ** 4 / 6 + s ** 3 - 5 * s ** 2 / 2 + 3 * s - mp.mpf(5) / 4
    r1, r2 = (3 - mp.sqrt(3)) / 2, (3 + mp.sqrt(3)) / 2
    a_num = 2 * (mp.quad(lambda s: m0(s) * 2 / s ** 2, [0, 1]) * 2 + mp.quad(lambda s: m1(s) * (1 / (s - r1) ** 2 + 1 / (r2 - s) ** 2), [1, 2]))
    a_cf = 2 * mp.sqrt(3) * mp.log(2 + mp.sqrt(3)) - mp.mpf(10) / 3
    assert abs(a_num - a_cf) < 1e-20, (a_num, a_cf)
    print("numeric check of alpha: ok")

R2c = iv.mpf(3) / 4  # |c|^2
def normsq(v): return sum(x * x for x in v)

def dist2_to_e(v):
    """squared chordal distance from the sphere point in direction v to e."""
    V = [I(x) for x in v]
    return iv.mpf(3) / 2 * (1 - sum(V) / (iv.sqrt(normsq(V)) * S3))

def cross(a, b): return [a[1] * b[2] - a[2] * b[1], a[2] * b[0] - a[0] * b[2], a[0] * b[1] - a[1] * b[0]]

def cell_ok(tri):
    V = [[I(x) for x in v] for v in tri]
    R = iv.sqrt(R2c)
    lam_lo = (R / max((iv.sqrt(normsq(v)) for v in V), key=lambda x: x.b)).a  # lower bound of R / max |v_i|
    nrm = cross([V[1][i] - V[0][i] for i in range(3)], [V[2][i] - V[0][i] for i in range(3)])
    h = abs(sum(nrm[i] * V[0][i] for i in range(3))) / iv.sqrt(normsq(nrm))
    lam_hi = (R / h).b
    for lam in (lam_lo, lam_hi):
        for v in V:
            val = K([iv.mpf(lam) * x for x in v])
            if val is None or val.b >= KE.a:
                return False
    return True

RHO0 = Fr(3, 10000)

def onsphere(v):
    """same ray as v, rescaled by a positive rational to norm about sqrt(3)/2 (rays, not lengths, define the cells)."""
    n2 = float(sum(x * x for x in v))
    return tuple(x * Fr(round((0.75 / n2) ** 0.5 * 2 ** 50), 2 ** 50) for x in v)

def local_ok():
    alpha = 2 * S3 * iv.log(2 + S3) - iv.mpf(10) / 3
    J = 2 * S3 * iv.log(2 + S3)  # J = int f'^2 / f = E[phi''], bounds |beta|
    m = (iv.mpf(4) / 3 - alpha) / 2
    d = I(RHO0)
    xi_min = iv.mpf(0.5) - d
    pbar = 1 / (2 * xi_min)
    M1 = 2 / (R2 - 2) ** 3 - 2 / (2 - R1) ** 3  # max of |phi'''| on [1, 2]
    A = (M1 + 12 * pbar) / 6
    B = 1 / (2 * xi_min ** 3)
    assert (A + B * iv.log(1 / d) / 3 - B / 3).a > 0  # bracket increasing on (0, rho0]
    bracket = -m + J / 2 * d ** 2 + iv.mpf(3) ** 1.5 * d * (A + B * (iv.log(1 / d) / 3 + iv.mpf(11) / 36))
    print("alpha =", alpha.mid, " margin m =", m.mid, " local bracket at rho0 =", bracket.b)
    return bracket.b < 0

def run():
    check_numeric()
    print("K(e) =", KE.mid, "width", float(KE.delta))
    assert local_ok(), "local bound fails"
    stack = [(onsphere((Fr(1), Fr(0), Fr(0))), onsphere((Fr(1), Fr(1), Fr(0))), onsphere((Fr(1), Fr(1), Fr(1))), 0)]
    done = local = 0; maxdepth = 0
    while stack:
        a, b, c, dep = stack.pop()
        if all(dist2_to_e(v).b <= I(RHO0 ** 2).a for v in (a, b, c)):
            local += 1; continue
        try:
            ok = cell_ok((a, b, c))
        except ValueError:
            ok = False
        if ok:
            done += 1; maxdepth = max(maxdepth, dep); continue
        if dep > 40:
            raise SystemExit("depth limit at %s %s %s" % (a, b, c))
        mid = lambda x, y: onsphere(tuple(p + q for p, q in zip(x, y)))
        ab, bc, ca = mid(a, b), mid(b, c), mid(c, a)
        stack += [(a, ab, ca, dep + 1), (ab, b, bc, dep + 1), (ca, bc, c, dep + 1), (ab, bc, ca, dep + 1)]
    print("cells verified by convexity:", done, " cells inside the local ball:", local, " max depth:", maxdepth)
    print("n = 3: K(c) < K(e) for every c != e in the sector. Certificate complete.")

if __name__ == "__main__":
    run()
