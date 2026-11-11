# Recomputes every constant of the upper and lower bound in the README, with asserts.
from math import asin, sin, log, pi, ceil, sqrt, exp

eps0 = 1 / 16
# per-copy regret in an epoch: (s + delta)^2 <= kappa * eps, with s = sqrt(eps), sin(delta)^2 = D <= eps <= 1/16
slope = asin(0.25) / 0.25          # arcsin(y) <= slope * y on [0, 1/4] (arcsin is convex there)
kappa_exact = (1 + slope) ** 2
kappa = 4.05
assert kappa_exact <= kappa, kappa_exact
# a = 1 / (2 sin 2s), sin 2s >= 2s (1 - (2s)^2 / 6) >= 2s * 23/24 for s <= 1/4
a2_factor = (24 / 23) ** 2          # a^2 <= a2_factor / (16 eps)
for k in range(1, 2001):
    s = 0.25 * k / 2000
    assert 1 / (2 * sin(2 * s)) ** 2 <= a2_factor / (16 * s * s) + 1e-15
# |e|^2 <= 32 a^2 mu (M ln 5 + x) / N^2, mu = kappa eps N  ->  |e|^2 <= G (M ln 5 + x) / N
G = 32 * a2_factor / 16 * kappa
# need |e|^2 <= eps / 8, so N >= 8 G (M ln 5 + x) / eps with M = 4 (d - 1)
A_need, B_need = 8 * G * 4 * log(5), 8 * G
A, B = 458, 71
assert A_need <= A and B_need <= B, (A_need, B_need)
# net lemma condition mu >= M ln 5 + x: kappa (A (d-1) + B x) >= 4 (d-1) ln 5 + x
assert kappa * A >= 4 * log(5) and kappa * B >= 1
# contraction: 2 |e|^2 + 2 D^3 / (1 - D) <= eps / 4 + 2 eps^3 / (1 - eps) <= eps / 2 for eps <= 1/16
assert 2 * eps0 ** 2 / (1 - eps0) <= 1 / 4
# epoch regret <= kappa eps * 4 (d-1) * (N_real + 1) <= 4 kappa A (d-1)^2 + 4 kappa B (d-1) x + 4 kappa (d-1) eps
print("epoch regret <= %.0f (d-1)^2 + %.0f (d-1) x + %.3f (d-1)" % (4 * kappa * A, 4 * kappa * B, 4 * kappa * eps0))

# warm-up: one run fails (angle > r) with probability <= p_fail; r = arcsin(1/4) / 3 so 3 r gives D_0 <= 1/16
r = asin(0.25) / 3
assert abs(sin(3 * r) ** 2 - eps0) < 1e-15
C2 = 750
# E sin^2 <= (2d + 1) / (2 N2) with N2 = C2 d, worst at d = 2
mean_sin2 = max((2 * d + 1) / (2 * C2 * d) for d in range(2, 10000))
p_fail = mean_sin2 / sin(r) ** 2 + exp(-8)
print("warm-up run failure probability <=", p_fail)
assert p_fail < 0.25
# exponential bound for sums of independent indicators: P(#fail >= L/2) <= exp(-2 L (1/2 - p)^2) <= exp(-x) if L >= x / (2 (1/2 - p)^2)
Lfac = 1 / (2 * (0.5 - p_fail) ** 2)
assert Lfac <= 8.1, Lfac
# copies of one warm-up run: <= 8 d + N2 + 4 (d - 1) N2 <= W d^2 for d >= 2
W = 4 * C2
for d in range(2, 10000):
    assert 8 * d + C2 * d + 4 * (d - 1) * C2 * d <= W * d * d
# number of epochs: epoch m needs >= 4 (d-1) * 458 (d-1) / eps_m >= 4 * 458 * 16 * 2^m copies
# x = ln(T (log2 T + 2)) <= 3 ln T for T >= 2
for T in [2, 3, 10, 1e3, 1e6, 1e12, 1e30]:
    assert log(T * (log(T, 2) + 2)) <= 3 * log(T)
# total: warm (8.1 x + 1) W d^2 + (log2 T + 1) [epoch regret] + 1 (failure), with 1 <= ln T / ln 2
c_warm = (8.1 * 3 + 1 / log(2)) * W
c_ep2 = (1 / log(2) + 1 / log(2)) * 4 * kappa * A
c_ep1 = (1 / log(2) + 1 / log(2)) * 4 * kappa * B * 3
print("E Regret <= %.0f d^2 ln T + %.0f d ln^2 T  (+ lower order)" % (c_warm + c_ep2 + 1, c_ep1))
assert c_warm + c_ep2 + 1 + 2 * 4 * kappa * eps0 / log(2) + 1 / log(2) <= 1.0e5 and c_ep1 <= 1.0e4

# lower bound: prior on a cube of half-width h = 1/(2 sqrt m), so |theta| <= 1/2; J = m pi^2 / h^2 = 4 pi^2 m^2
# infidelity >= 0.4 |theta_hat - theta|^2 (Lemma 1); information trace <= 4 per copy (Lemma 2)
for u in [1 + k / 100 for k in range(0, 10000)]:
    assert (u - 0.5) ** 2 / (1.25 * (1 + u * u)) >= 0.4 * 0.25 - 1e-15
assert 1 / (1 + 0.25) >= 0.4 * 0.25 and 1 / ((1 + 0.25) * (1 + 1)) >= 0.4
# sum_t 0.4 m^2 / (4 t + 4 pi^2 m^2), t = 0..T-1, >= 0.1 m^2 ln(1 + T / (pi^2 m^2)) = 0.4 (d-1)^2 ln(1 + T / (4 pi^2 (d-1)^2))
for d in [2, 3, 5, 10]:
    m = 2 * (d - 1)
    for T in [1, 10, 1000, 100000]:
        s_ = sum(0.4 * m * m / (4 * t + 4 * pi ** 2 * m * m) for t in range(T))
        assert s_ >= 0.4 * (d - 1) ** 2 * log(1 + T / (4 * pi ** 2 * (d - 1) ** 2)) - 1e-12
# epoch regret constants: 4 kappa (d-1) eps N_m <= 4 kappa (d-1) (P + eps), P = 458 (d-1) + 71 x
assert 4 * kappa * A <= 7420 and 4 * kappa * B <= 1151 and 4 * kappa * eps0 <= 1.02
# warm-up length W <= (8.1 x + 1) * 3000 d^2 <= 1e5 d^2 ln T (x <= 3 ln T, 1 <= ln T / ln 2)
assert (8.1 * 3 + 1 / log(2)) * W <= 1e5
# online constant: eps_m * sum_{k <= m} N_k <= 2 P, hence eps_m <= 16 (d-1) P / t for t >= 2W
for d in [2, 3, 8, 100]:
    for T in [2, 1e3, 1e9, 1e30]:
        x = log(T * (log(T, 2) + 2)); P = A * (d - 1) + B * x
        for m in range(0, 120):
            em = eps0 * 2 ** -m
            assert em * sum(ceil(P / (eps0 * 2 ** -k)) for k in range(m + 1)) <= 2 * P
print("all constants: ok")
