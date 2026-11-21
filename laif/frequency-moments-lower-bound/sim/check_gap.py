"""Checks for the F_k lower bound.
1. Explicit pairs Z_0 on {0..k-1}, Z_1 on {0..k}, both mean one, equal moments of order 0..k-1
   (Z_1 = Z_0 + t * k-th finite difference), and the moment gap E[Z_1^k] - E[Z_0^k] = t k! (exact).
2. The gap identity sum_a nu(a) a^k = nu(k) k! for random signed nu on {0..k} with vanishing moments < k.
3. Sampling the induced inputs (exactly, through the multinomial counts of the m draws) (Definition 2.1 of the moment-matching framework): F_k / N concentrates at
   (1 + E[Z_b^k]) / 2, and the two values are separated.
4. Exponent arithmetic: a_k = (1 - 2^{1-k}) / (2 - 2^{1-k}) = (2^{k-1}-1)/(2^k-1) > max(1/3, 1/2 - 1/(2k)), k >= 3."""
import random
from fractions import Fraction as Fr
from math import comb, factorial
import numpy as np

def pair(k):
    nu = [Fr((-1) ** (k - a) * comb(k, a)) for a in range(k + 1)]       # k-th finite difference
    z0 = [Fr(0)] * (k + 1)
    # full support on {0..k-1}, mean one: mass at 0 and 2 balanced around 1, small uniform part
    for a in range(k): z0[a] = Fr(1, 4 * k)
    rest = 1 - sum(z0); m = sum(a * z0[a] for a in range(k))
    # put remaining mass on {0, 1}... adjust so that the mean is one: solve p1 + 2 p2 term
    need = 1 - m                                                            # extra mean needed
    hi = k - 1
    p_hi = need / hi; assert 0 <= p_hi <= rest
    z0[hi] += p_hi; z0[0] += rest - p_hi
    assert sum(z0) == 1 and sum(a * z0[a] for a in range(k + 1)) == 1
    t = min(z0[a] / abs(nu[a]) for a in range(k) if nu[a] < 0) / 2
    z1 = [z0[a] + t * nu[a] for a in range(k + 1)]
    assert all(p >= 0 for p in z1) and z1[k] > 0 and z0[k] == 0
    for j in range(k):
        assert sum(z0[a] * a ** j for a in range(k + 1)) == sum(z1[a] * a ** j for a in range(k + 1))
    g = sum((z1[a] - z0[a]) * a ** k for a in range(k + 1))
    assert g == t * factorial(k) == z1[k] * factorial(k)
    return z0, z1

for k in range(3, 9):
    pair(k)
print("exact pairs and moment gap t k! checked for k = 3..8")

rng = random.Random(1)
for _ in range(500):
    k = rng.randint(1, 7)
    # random nu with vanishing moments < k: nu = c * finite difference (the only such measures)
    V = np.array([[a ** j for a in range(k + 1)] for j in range(k)], float)
    c = rng.uniform(-3, 3); nu = [Fr(c).limit_denominator(1000) * (-1) ** (k - a) * comb(k, a) for a in range(k + 1)]
    assert all(sum(nu[a] * a ** j for a in range(k + 1)) == 0 for j in range(k))
    assert sum(nu[a] * a ** k for a in range(k + 1)) == nu[k] * factorial(k)
    # null space of the moment matrix is one-dimensional
    assert np.linalg.matrix_rank(V) == k
print("gap identity and one-dimensional null space checked")

def sample_Fk(z, k, N, rs):
    m = N // 2                                                              # only the counts of each value matter
    cnt = rs.multinomial(m, [float(p) for p in z])
    s = sum(a * int(cnt[a]) for a in range(len(z)))
    if s > N: return 1.0                                                    # fallback: a bijection, F_k = N
    return (sum(int(cnt[a]) * a ** k for a in range(len(z))) + (N - s)) / N
rs = np.random.default_rng(2)
for k in (3, 4, 5):
    z0, z1 = pair(k)
    mom = lambda z, f: sum(z[a] * f(a) for a in range(k + 1))
    phi = [float((1 + mom(z, lambda a: a ** k)) / 2) for z in (z0, z1)]
    var = [float(mom(z, lambda a: (a ** k - a) ** 2) - mom(z, lambda a: a ** k - a) ** 2) for z in (z0, z1)]
    gap = phi[1] - phi[0]; assert gap > 0
    N = 2 * int(400 * max(var) / gap ** 2) + 2                              # gap = 10 standard deviations of F_k/N at least
    sd = [(N // 2 * v) ** 0.5 / N for v in var]
    v = [[sample_Fk(z, k, N, rs) for _ in range(30)] for z in (z0, z1)]
    for bb in (0, 1):
        assert max(abs(x - phi[bb]) for x in v[bb]) < 5 * sd[bb], (k, bb)
    assert max(v[0]) < min(v[1])
    print(f"k={k}, N={N}: F_k/N limits {phi[0]:.4f} vs {phi[1]:.4f} (sd {sd[0]:.4f}, {sd[1]:.4f}), "
          f"samples [{min(v[0]):.4f},{max(v[0]):.4f}] vs [{min(v[1]):.4f},{max(v[1]):.4f}]")

for k in range(3, 40):
    a = Fr(2 ** (k - 1) - 1, 2 ** k - 1)
    assert (1 - Fr(2) ** (1 - k)) / (2 - Fr(2) ** (1 - k)) == a
    assert a > Fr(1, 3) and a > Fr(1, 2) - Fr(1, 2 * k) and a < Fr(1, 2)
assert Fr(2 ** 1 - 1, 2 ** 2 - 1) == Fr(1, 3)
print("exponents checked for k = 3..39")
