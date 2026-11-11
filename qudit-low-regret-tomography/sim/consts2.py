# Constants of Theorem 3 (budgeted phases): checks every inequality of the drift argument with asserts.
# python consts2.py          check the chosen parameters
# python consts2.py search   grid search for the smallest leading constant
import sys
from math import exp, log, log2, ceil

EPS0 = 1 / 128
LAM = 1 - 2 * EPS0          # pair average of the zero probability >= LAM (eps + D)
CE = 1 / (4 * (1 - 2 * EPS0 / 3) ** 2)   # E|e|^2 <= CE r eps / C
LIN = 1 / (exp(1) * log(2))  # log2(y)_+ <= LIN * y


def logpois_upper(mu, B):
    """log of the bound P(Z >= B) <= e^{-mu} (e mu / B)^B for a sum of independent indicators with mean <= mu < B."""
    return -mu + B * (1 + log(mu / B))


def tails(B):
    """S1 = sum_{k>=1} P(R >= k), S2 = sum_{k>=0} P(-1-R > k), both for the minimal budget B (they decrease in B)."""
    S1 = 0.0
    for k in range(1, 200):
        mu = B * 2.0 ** -k + 1
        S1 += exp(logpois_upper(mu, B))
    S2 = 0.0
    for k in range(0, 200):
        mu = LAM * (B * 2.0 ** (k + 1) - 2.01)
        S2 += exp(-(1 - B / mu) ** 2 * mu / 2)
    return S1, S2


def gamma(r):
    """bound on E[g' 1_complete] when the phase starts with eps + D <= r eps."""
    K = r - 1
    assert K * EPS0 < 1
    return LIN * (4 * CE * r / C_ + 4 * K ** 3 * EPS0 ** 2 / (1 - K * EPS0))


def analyse(theta, C, a, w, C2, d1=0.25, d2=0.25, verbose=False):
    global C_
    C_ = C
    Emin = 8 * C                       # eps n >= 4 C d (d - 1) >= 8 C
    Bmin = theta * Emin
    S1, S2 = tails(Bmin)
    # region I: r <= r1, abort only with probability pI
    r1 = theta / (1 + d1)
    mu_star = theta * Emin / (1 + d1)
    pI = exp(-d1 ** 2 * mu_star / (2 + d1))
    drift_I = (1 - pI) - a * gamma(r1) - (2 + w) * pI - (pI + S1) - a * S2
    # regions II and III: r > r1, so g >= g1
    g1 = log2(r1 - 1)
    r2 = (1 + d2) * (theta + 1 / Emin) / LAM
    dp = d2 / (1 + d2)
    pIII = exp(-dp ** 2 * LAM * r2 * Emin / 2)
    drift_II = min(1 + a * g1, (a - 1) * g1 - (2 + w) - 1) - a * gamma(r2) - S1 - a * S2
    eta = min(drift_I, drift_II - 0.25)  # region III spends at most 0.25 on a pIII (l + 8)
    Lstar = 0.25 / (a * pIII) - 8        # condition: log2 T <= Lstar
    # warm-up: Psi goes from -w to -a g0
    Eg0 = LIN * (1.25 / C2) / EPS0 + log2(1 / EPS0) * exp(-8)
    eta_w = (w - a * Eg0) / w
    eta = min(eta, eta_w)
    # cost: B <= theta (4 C d (d-1) + 4 (d-1) eps0) + 1 <= cB d^2 for d >= 2; warm-up W1 <= cW d^2
    cB = theta * (4 * C + 4 * EPS0 / 2) + 0.25
    cW = 4 * C2 + 3
    lead = max(cB, cW / w) / eta     # E Regret <= lead d^2 (log2 T + 1 + w) + max(cB, cW) d^2
    if verbose:
        print(f"theta={theta} C={C} a={a} w={w} C2={C2}: drift I {drift_I:.4f}, II {drift_II:.4f}, warm {eta_w:.4f}, "
              f"eta {eta:.4f}; g1 {g1:.3f}, r1 {r1:.3f}, r2 {r2:.3f}; pI {pI:.2e} pIII {pIII:.2e} S1 {S1:.2e} S2 {S2:.2e}; "
              f"log2 T <= {Lstar:.3e}; cB {cB:.1f} cW {cW:.0f}; lead {lead:.1f} d^2 log2 T = {lead / log(2):.1f} d^2 ln T")
    return eta, lead, Lstar, cB, cW


if __name__ == "__main__" and len(sys.argv) > 1 and sys.argv[1] == "search":
    best = None
    for theta in [3, 3.5, 4, 5]:
        for C in [20, 30, 40, 50, 70]:
            for a in [6, 8, 10, 12]:
                for w in [2, 3, 4, 6]:
                    for C2 in [300, 500, 800, 1200]:
                        for d1 in [0.15, 0.25, 0.4]:
                            for d2 in [0.25, 0.4, 0.6, 1.0]:
                                try:
                                    eta, lead, Ls, cB, cW = analyse(theta, C, a, w, C2, d1, d2)
                                except (AssertionError, ValueError, ZeroDivisionError):
                                    continue
                                if eta > 0.05 and Ls > 1e30 and (best is None or lead < best[0]):
                                    best = (lead, theta, C, a, w, C2, d1, d2)
    print("best", best)
    analyse(*best[1:], verbose=True)
    sys.exit()

# chosen parameters
THETA, C, A, W, C2, D1, D2 = 3.5, 40, 10, 4, 500, 0.15, 0.6
eta, lead, Lstar, cB, cW = analyse(THETA, C, A, W, C2, D1, D2, verbose=True)
assert eta >= 0.56 and Lstar >= 1e52
# E Regret <= d^2 [max(cB, cW/W) (l_max + 1 + W) / eta + max(cB, cW)], l_max + 1 <= log2 T - 14 (l_max = log2(T / (512 C d (d-1))))
assert lead / log(2) <= 1420 and max(cB, cW) <= 2010 and 512 * C * 2 >= 2 ** 15
# E Regret <= lead d^2 (max(0, log2 T - 14) + 4) + max(cB, cW) d^2 <= 1420 d^2 ln T + 6000 d^2
assert lead * 4 + max(cB, cW) <= 6000 and abs(lead - 983.8) < 0.1 and cB <= 560.4 and cW <= 2003
# the warm-up and phase copy counts behind cB and cW, d >= 2
for d in range(2, 2000):
    for eps in [EPS0 * 2.0 ** -k for k in range(0, 60, 7)]:
        n = 4 * (d - 1) * ceil(C * d / eps)
        assert ceil(THETA * eps * n) <= cB * d * d
    assert 8 * d + C2 * d * (1 + 4 * (d - 1)) <= cW * d * d
# monotonicity of the tail sums in B (used at B >= Bmin)
prev = None
for B in [THETA * 8 * C * m for m in (1, 1.5, 2, 4, 10, 100)]:
    s = sum(tails(B))
    assert prev is None or s <= prev
    prev = s
print("all constants of Theorem 3: ok")
