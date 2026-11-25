"""Lower threshold: the number state |1> violates ln||W||_1 <= Delta_a for every order 0 < a < a1.
h(a) = lnGamma(a+1) - a ln a - (1-a) ln(4 e^{-1/2} - 1) is concave on (0, 1) (proof in README), h(0+) < 0,
so h < 0 on (0, a1) once h(a1) = 0 and h'(a1) > 0 (tangent line at a1 lies above h)."""
from mpmath import mp, mpf, loggamma, log, exp, digamma, findroot, quad, laguerre, inf
mp.dps = 40
L1 = 4 * exp(mpf(-1) / 2) - 1
assert abs(quad(lambda x: exp(-x / 2) * abs(1 - x), [0, 1, inf]) / 2 - L1) < mpf(10) ** -30   # ||W_1||_1
L = log(L1)
h = lambda a: loggamma(a + 1) - a * log(a) - (1 - a) * L
dh = lambda a: digamma(a + 1) - log(a) - 1 + L
a1 = findroot(h, mpf("0.2887"))
assert dh(a1) > mpf("0.4") and h(mpf(10) ** -30) < 0
for a in [mpf(k) / 1000 for k in range(1, 289)]:                 # sampled check of the concavity conclusion
    assert h(a) < 0
assert h(mpf("0.2888")) > 0
print("a1 =", mp.nstr(a1, 20), " h'(a1) =", mp.nstr(dh(a1), 10), " ln||W_1||_1 =", mp.nstr(L, 15))
