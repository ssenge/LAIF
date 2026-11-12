# Constants of the phase algorithm (Theorem 2 of NOTES.md), with asserts.
# 1. Mean squared error of the median of 5 amplitude estimation runs with register size M, from the
#    tail bound P(|Y - mu| > pi k / M + pi^2 k^2 / M^2) <= 1 / (2 (k - 1)), k >= 2 (sqrt(mu(1-mu)) <= 1/2).
# 2. The phase-regret constant.
from math import pi, sqrt, comb, log, sin

H = 5            # runs in the median


def mse_bound(M):
    """upper bound on E (median - mu)^2 for register size M; error <= 1 always."""
    # P(err > gamma) <= P(Bin(5, p) >= 3), p = min(1, 1/(2(k - 1))) with k the largest k with g(k) <= gamma
    # E err^2 = int_0^1 2 gamma P(err > gamma) dgamma; integrate the step function exactly between breakpoints g(k)
    g = lambda k: pi * k / M + (pi * k / M) ** 2
    total = 0.0
    k = 1                                   # on [0, g(2)) use P <= 1
    lo = 0.0
    while lo < 1.0:
        hi = min(1.0, g(k + 1))
        if k < 2:
            P = 1.0
        else:
            p = min(1.0, 1 / (2 * (k - 1)))
            P = sum(comb(H, i) * p ** i * (1 - p) ** (H - i) for i in range(3, H + 1))   # binomial tail, increasing in p
        total += P * (hi * hi - lo * lo)
        lo = hi
        k += 1
    return total


CE2 = max(mse_bound(M) * M * M for M in list(range(2, 3000)) + [10 ** 4, 10 ** 5, 10 ** 6, 10 ** 7])
print(f"median of {H} runs: E err^2 <= {CE2:.2f} / M^2 (max over checked M); queries < {2 * H} M")
assert CE2 <= 160
CE2 = 160.0

# Phase with target error a, angle s <= 1, register M = ceil(K sqrt(d) / (s a)) for each of 2d - 1 means:
# E|theta^ - theta|^2 <= 4 CE2 / M^2 + (d - 1) 4 CE2 / (M^2 sin^2 s) <= 4 CE2 d / (M^2 sin^2 s) <= 4 CE2 a^2 / (K^2 sin(1)^2)
K = sqrt(4 * CE2) / sin(1)
K = 30.1
assert 4 * CE2 / (K ** 2 * sin(1) ** 2) <= 1
# Phase regret: (2d - 1) means, < 2 H M = 10 M queries each; pair regret r(x+) + r(x-) = |theta| - cos s <c, theta>
#   <= |theta| (s^2 + |c - n|^2) / 2, centre regret |theta| |c - n|^2 / 2, so phase regret <= 5 M d |theta| (s^2 + |c - n|^2).
# M <= K sqrt(d) / (s a) + 1. With e = previous error, E|e|^2 <= a_prev^2 = 4 a^2, s = min(1, a / |theta^|):
#   A = E[|theta| s / a] <= 2 + 2 E|e| / a <= 6
#   B = E[|theta| |c - n|^2 / (s a)] <= 4 E|e| / a + 8 E|e|^2 / a^2 <= 8 + 32 = 40
#   "+1" term: 5 d |theta| (s^2 + |c - n|^2) <= 25 d
A, B = 2 + 2 * 2, 4 * 2 + 8 * 4
lead = 5 * K * (A + B)
print(f"K = {K}, E phase regret <= {lead:.0f} d^1.5 + 25 d")
# phases: phase l has M >= K sqrt(d) 2^l >= 2^l, so at most log2 T + 1 phases start
print(f"E Regret <= ({lead:.0f} d^1.5 + 25 d) (log2 T + 1) <= {lead / log(2):.0f} d^1.5 ln T + {lead:.0f} d^1.5 + {25 / log(2):.0f} d ln T + 25 d")
assert lead <= 6925
print("upper bound constants: ok")
