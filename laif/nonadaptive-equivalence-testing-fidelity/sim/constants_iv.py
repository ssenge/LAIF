# Rigorous check of the constants of Theorems 1 and 2: exact rationals (fractions) for rational steps,
# interval arithmetic (mpmath.iv, outward rounding) for exp, log and roots. Asserts compare rigorous bounds.
# Each P(E^c) term decreases in D_A, d_C, D, so the smallest admissible sizes are the worst case.
from fractions import Fraction as Q
from mpmath import iv
iv.dps = 50
V = lambda q: iv.mpf(q.numerator) / iv.mpf(q.denominator)         # exact rational -> enclosing interval
ln21 = iv.log(iv.mpf(21))

# net bounds (1/10-net, factor 1.25): radii 3.8 and 4.48
assert Q(125, 100) * Q(38, 10) == Q(475, 100) and Q(125, 100) * Q(448, 100) == Q(56, 10)
assert (V(Q(38, 10)) ** 2 / 2 - 2 * ln21).a > V(Q(113, 100)).b              # exponent > 1.13 per dimension
assert (V(Q(448, 100)) ** 2 / 2 - 2 * ln21).a > V(Q(394, 100)).b            # exponent > 3.94 per dimension

def tv(c0, x, PEc):
    return V(Q(1, 20)) + iv.sqrt(iv.exp(V(x)) / (1 - PEc) ** 2 - 1) / 2       # interval

# Theorem 1: c0 = 3/20, ||G|| <= 4.75 + 1/4 = 5, D >= 60, N = 3 D^{3/2}/eps^2
c0, D = Q(3, 20), 60
assert c0 * 5 <= Q(3, 4) and Q(475, 100) + Q(1, 4) == 5
gap = V(c0 ** 2 / 16) / iv.mpf(Q(7, 4).numerator / 4) ** iv.mpf(1.5)        # c0^2 / (16 (7/4)^{3/2})
assert (1 / gap).b <= 1647
PEc = 2 * iv.exp(-V(Q(113, 100)) * D) + 2 * iv.exp(-V(Q(D * D, 32))) + iv.exp(-V(Q(D * D - 1, 36)))
x = 49 * c0 ** 4 * 9
assert x / D <= Q(1, 2)                                                       # condition of Lemma 5
t1 = tv(c0, x, PEc); assert t1.b < V(Q(1, 3)).a
print(f"Theorem 1: 1 - F >= eps/{float((1/gap).b):.3f}, x = {float(x):.6f}, P(E^c) <= {float(PEc.b):.3e}, TV <= {float(t1.b):.6f} < 1/3")

# Theorem 2: c0 = 1/10, ||G|| <= 7.5, D_A >= 56, d_C >= 2, N = 13 D^{3/2}/eps^2
c0, DA, dC = Q(1, 10), 56, 2; D = DA * dC; k = (DA ** 2 - 1) * (dC ** 2 - 1)
assert Q(475, 100) + Q(475, 100) / dC + Q(56, 10) / DA + Q(1, 4) <= Q(15, 2) and c0 * Q(15, 2) <= Q(3, 4)
assert Q(3, 4) * Q(3, 4) * (1 - Q(1, DA * DA)) >= Q(1, 2)                   # ||G||_F^2 >= D/2 after the chi^2 tail at x = k/64
assert k >= Q(3, 4) * (1 - Q(1, DA * DA)) * D * D
gap = V(c0 ** 2 / 16) / iv.mpf(1.75) ** iv.mpf(1.5)
assert (1 / gap).b <= 3705
PEc = (2 * iv.exp(-V(Q(113, 100)) * D) + 2 * iv.exp(-V(Q(113, 100)) * DA) + 2 * iv.exp(-V(Q(394, 100)) * dC)
       + 2 * iv.exp(-V(Q(D * D, 32))) + iv.exp(-V(Q(k, 64))))
assert PEc.b <= 2e-3
x = 16 * c0 ** 4 * 169
assert x / D <= Q(1, 2)
t2 = tv(c0, x, PEc); assert t2.b < V(Q(1, 3)).a
# Markov step: D_A >= 1 + 4 ln(41 D_A d_C/eps) gives e^{-(D_A-1)/4} <= eps/(41 D_A d_C); need 40 sqrt(D_A/(D_A-1)) <= 41
assert Q(1600) * Q(DA, DA - 1) <= Q(1681)
print(f"Theorem 2: 1 - F >= eps/{float((1/gap).b):.3f}, x = {float(x):.6f}, P(E^c) <= {float(PEc.b):.3e}, TV <= {float(t2.b):.6f} < 1/3 (margin >= {float((V(Q(1,3)) - t2).a):.6f})")
print("all asserts passed")
