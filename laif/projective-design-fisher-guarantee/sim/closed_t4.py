"""Exact value of the qubit design Fisher guarantee at t = 4.

All data lie in K = Q(sigma), sigma = sqrt(4 - sqrt 6), sigma^4 - 8 sigma^2 + 10 = 0.
Checks, in exact arithmetic in K plus rigorous interval enclosures of sigma:
  1. the 4-orbit measure has the Haar moments of u^a z^c, 2a + c <= 4, and positive weights;
  2. the dual polynomial q from the touching conditions has E_Haar[q] equal to the primal value V;
  3. h(z, s) = s(1 - z) - q(z, s(1 - z^2)) >= 0 on [-1, 1] x [0, 1].
"""
from fractions import Fraction as Fr
import mpmath as mp


class K:
    """Element c0 + c1 sigma + c2 sigma^2 + c3 sigma^3 of K."""
    __slots__ = ("c",)

    def __init__(s, c=0):
        if isinstance(c, K): c = c.c
        elif not isinstance(c, (list, tuple)): c = [Fr(c), 0, 0, 0]
        s.c = [Fr(x) for x in c]

    def __add__(s, o): o = K(o); return K([a + b for a, b in zip(s.c, o.c)])
    __radd__ = __add__
    def __neg__(s): return K([-a for a in s.c])
    def __sub__(s, o): return s + (-K(o))
    def __rsub__(s, o): return K(o) - s

    def __mul__(s, o):
        o = K(o); p = [Fr(0)] * 7
        for i, a in enumerate(s.c):
            if a:
                for j, b in enumerate(o.c): p[i + j] += a * b
        for k in (6, 5, 4):  # sigma^k = 8 sigma^(k-2) - 10 sigma^(k-4)
            p[k - 2] += 8 * p[k]; p[k - 4] -= 10 * p[k]; p[k] = 0
        return K(p[:4])
    __rmul__ = __mul__

    def inv(s):
        cols = [(s * K([1 if i == j else 0 for i in range(4)])).c for j in range(4)]
        M = [[cols[j][i] for j in range(4)] + [Fr(1 if i == 0 else 0)] for i in range(4)]
        for i in range(4):
            p = next(r for r in range(i, 4) if M[r][i]); M[i], M[p] = M[p], M[i]
            M[i] = [x / M[i][i] for x in M[i]]
            for r in range(4):
                if r != i and M[r][i]: M[r] = [a - M[r][i] * b for a, b in zip(M[r], M[i])]
        return K([M[i][4] for i in range(4)])

    def __truediv__(s, o): return s * K(o).inv()
    def __rtruediv__(s, o): return K(o) * s.inv()

    def __pow__(s, n):
        r = K(1)
        for _ in range(n): r = r * s
        return r

    def iszero(s): return all(x == 0 for x in s.c)
    def __eq__(s, o): return (s - K(o)).iszero()
    def mpf(s): return sum(mp.mpf(a.numerator) / a.denominator * SIG ** i for i, a in enumerate(s.c))
    def iv(s): return sum(mp.iv.mpf([a.numerator, a.numerator]) / a.denominator * SIGI ** i for i, a in enumerate(s.c))


mp.mp.dps = 60; mp.iv.dps = 60
SIG = mp.sqrt(4 - mp.sqrt(6))
lo, hi = Fr(1), Fr(3, 2)          # sigma is the only root of x^4 - 8x^2 + 10 in [1, 3/2]
f = lambda x: x ** 4 - 8 * x ** 2 + 10
for _ in range(200):
    m = (lo + hi) / 2
    if f(m) > 0: lo = m
    else: hi = m
assert f(lo) > 0 > f(hi)
SIGI = mp.iv.mpf([mp.mpf(lo.numerator) / lo.denominator, mp.mpf(hi.numerator) / hi.denominator])
S = K([0, 1, 0, 0]); R6 = 4 - S * S
assert R6 * R6 == 6 and R6.mpf() > 0


def sign(x):
    assert not x.iszero()
    v = x.iv()
    if v.a > 0: return 1
    if v.b < 0: return -1
    raise ValueError("enclosure too wide")


# 1. primal measure on (z, u), u = x^2
z1 = -(1 + R6) * S / 5; z2 = -S / 5; z3 = (R6 - 1) * S / 5; z4 = 1 / S
u2 = (12 + 2 * R6) / 25; u4 = 1 - z4 * z4
w1 = (16 - R6) / 72; w2 = (16 - R6) / 36; w3 = (8 + 3 * R6) / 72; w4 = K(Fr(2, 9))
assert w1 + w2 + w3 + w4 == 1
B = [(0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (1, 0), (1, 1), (1, 2), (2, 0)]
def df2(n): return 1 if n <= 0 else n * df2(n - 2)
def hm(a, c): return Fr(0) if c % 2 else Fr(df2(2 * a - 1) * df2(c - 1), df2(2 * a + c + 1))
P = [(z1, K(0), w1), (z2, u2, w2), (z3, K(0), w3), (z4, u4, w4)]
for a, b in B:
    assert sum((w * u ** a * z ** b for z, u, w in P), K(0)) == hm(a, b), (a, b)
assert all(sign(w) > 0 for _, _, w in P)
assert sign(u2) > 0 and sign(1 - z2 * z2 - u2) > 0 and sign(u4) > 0
assert all(sign(z + 1) > 0 and sign(1 - z) > 0 for z, _, _ in P)
V = w2 * u2 / (1 + z2) + w4 * u4 / (1 + z4)
closed = (119 + 4 * R6 - (11 + 5 * R6) * S) / 261
assert V == closed
x = mp.mpf(V.mpf())
assert abs(2349 * x ** 4 - 4284 * x ** 3 + 2894 * x ** 2 - 860 * x + 95) < mp.mpf(10) ** -50
print("primal: exact moments of a 4-design, weights > 0, value V =", mp.nstr(x, 40))

# 2. dual polynomial q from the touching conditions (linear in the coefficients), g = u - (1 + z) q
def row(kind, z, u):
    out = []
    for a, b in B:
        m = u ** a * z ** b
        mz = b * u ** a * z ** (b - 1) if b else K(0)
        mu = a * u ** (a - 1) * z ** b if a else K(0)
        out.append({"g": -(1 + z) * m, "gz": -(m + (1 + z) * mz), "gu": -(1 + z) * mu,
                    "gt": -(m + (1 + z) * mz) + 2 * z * (1 + z) * mu}[kind])
    return out, {"g": -u, "gz": K(0), "gu": K(-1), "gt": 2 * z}[kind]
rows = [row("g", z1, K(0)), row("gz", z1, K(0)), row("g", z2, u2), row("gz", z2, u2), row("gu", z2, u2),
        row("g", z3, K(0)), row("gz", z3, K(0)), row("g", z4, u4), row("gt", z4, u4)]
M = [r + [rhs] for r, rhs in rows]; n = 9
for i in range(n):
    p = next(r for r in range(i, n) if not M[r][i].iszero()); M[i], M[p] = M[p], M[i]
    iv = M[i][i].inv(); M[i] = [x * iv for x in M[i]]
    for r in range(n):
        if r != i and not M[r][i].iszero():
            fac = M[r][i]; M[r] = [a - fac * b for a, b in zip(M[r], M[i])]
q = [M[i][n] for i in range(n)]
assert sum((c * hm(a, b) for c, (a, b) in zip(q, B)), K(0)) == V
print("dual: E_Haar[q] = V exactly")

# 3. h = A + B s + C s^2 with A = -q0(z), B = (1 - z) - q1(z)(1 - z^2), C = -q2 (1 - z^2)^2
def padd(p, r):
    k = max(len(p), len(r)); return [(p[i] if i < len(p) else K(0)) + (r[i] if i < len(r) else K(0)) for i in range(k)]
def pmul(p, r):
    o = [K(0)] * (len(p) + len(r) - 1)
    for i, a in enumerate(p):
        for j, b in enumerate(r): o[i + j] = o[i + j] + a * b
    return o
def psc(p, c): return [a * c for a in p]
def trim(p):
    while len(p) > 1 and p[-1].iszero(): p = p[:-1]
    return p
def pdiv(p, r):
    p = list(trim(p)); r = trim(r); out = [K(0)] * (len(p) - len(r) + 1)
    for k in range(len(out) - 1, -1, -1):
        c = p[k + len(r) - 1] / r[-1]; out[k] = c
        for j, b in enumerate(r): p[k + j] = p[k + j] - c * b
    assert all(x.iszero() for x in p), "not divisible"
    return out
qa = {a: [K(0)] * 5 for a in range(3)}
for c, (a, b) in zip(q, B): qa[a][b] = c
one_m, one_p, omz2 = [K(1), K(-1)], [K(1), K(1)], [K(1), K(0), K(-1)]
A = psc(qa[0], -1)
Bp = padd(one_m, psc(pmul(qa[1], omz2), -1))
C = psc(pmul(omz2, omz2), -qa[2][0])
assert sign(-qa[2][0]) > 0                                   # C >= 0: h is convex in s
sq = lambda r: pmul([-r, K(1)], [-r, K(1)])
RA = trim(pdiv(A, pmul(sq(z1), sq(z3))))                     # A = c (z - z1)^2 (z - z3)^2, c > 0
assert len(RA) == 1 and sign(RA[0]) > 0
R1 = pdiv(padd(padd(A, Bp), C), sq(z4))                      # h(z, 1) = (z - z4)^2 R1(z)
Bq = pdiv(Bp, one_m)                                         # B = (1 - z) Bq
G = pdiv(padd(Bp, psc(C, 2)), one_m)                         # B + 2C = (1 - z) G
L = padd([K(1)], psc(pmul(qa[1][:3], one_p), -1))
E = padd(psc(pmul(A, pmul(one_p, one_p)), 4 * (-qa[2][0])), psc(pmul(L, L), -1))
assert all(x.iszero() for x in trim(padd(padd(psc(pmul(A, C), 4), psc(pmul(Bp, Bp), -1)), psc(pmul(pmul(one_m, one_m), E), -1))))
R2 = pdiv(E, sq(z2))                                         # 4AC - B^2 = (1 - z)^2 (z - z2)^2 R2(z)

def ivp(p): return [c.iv() for c in trim(p)]
def ev(cs, X):
    v = mp.iv.mpf(0)
    for c in reversed(cs): v = v * X + c
    return v
def positive(cs, lo, hi, depth=0):
    v = ev(cs, mp.iv.mpf([lo, hi]))
    if v.a > 0: return 1
    assert depth < 40 and v.b > 0, (lo, hi)
    m = (lo + hi) / 2
    return positive(cs, lo, m, depth + 1) + positive(cs, m, hi, depth + 1)
print("R1 > 0 on [-1, 1]:", positive(ivp(R1), mp.mpf(-1), mp.mpf(1)), "intervals")
# For each z: B >= 0 (minimum over s at s = 0, h >= A >= 0), or B + 2C <= 0 (minimum at s = 1, h >= h(z, 1) >= 0),
# or 4AC - B^2 >= 0 (h >= 0 for every real s).
cB, cG, cR = ivp(Bq), ivp(G), ivp(R2); cnt = [0, 0, 0]
def cover(lo, hi, depth=0):
    X = mp.iv.mpf([lo, hi])
    if ev(cB, X).a >= 0: cnt[0] += 1; return
    if ev(cG, X).b <= 0: cnt[1] += 1; return
    if ev(cR, X).a > 0: cnt[2] += 1; return
    assert depth < 40, (lo, hi)
    m = (lo + hi) / 2; cover(lo, m, depth + 1); cover(m, hi, depth + 1)
cover(mp.mpf(-1), mp.mpf(1))
print("case split of [-1, 1] (s = 0, s = 1, discriminant):", cnt)
print("h >= 0 on [-1, 1] x [0, 1]; eta_des(2, 4) = (119 + 4 sqrt6 - (11 + 5 sqrt6) sqrt(4 - sqrt6))/261 =", mp.nstr(x, 40))
