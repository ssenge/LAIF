"""Bases of the quantum approximate monotone local search corollaries.

For a list L of extension oracles (alpha, c) and a target ratio beta, approximate monotone local search
(Esmer, Kulik, Marx, Neuen, Sharma, ESA 2022 and SODA 2024) costs, for the guess k of OPT,
    min over (alpha, c) in L and t of  c^l / hyper(n, k, t, x),  x = max(0, ceil((1 - beta/alpha) k + t/alpha)),
with l = k - x, and best(L, beta) is the base of the maximum over k <= n/beta. The quantum base is
sqrt(best). The script computes best from the large-deviation exponent of the hypergeometric tail and
checks it against the exact discrete cost at finite n."""
import math
import numpy as np
from scipy.stats import hypergeom

# parameterized randomized alpha-approximations of Kulik and Shachnai (FOCS 2020), bases rounded up there
VC = {1.1: 1.1652, 1.2: 1.096, 1.3: 1.058, 1.4: 1.0332, 1.5: 1.0166, 1.666: 1.004, 1.75: 1.0016, 1.8: 1.00074,
      1.9: 1.000083}
HS3 = {1.2: 1.59, 1.4: 1.29, 1.6: 1.18, 1.8: 1.11, 2.0: 1.0659, 2.2: 1.039, 2.4: 1.021, 2.6: 1.0085, 2.8: 1.0026}
MCT = math.sqrt(math.sqrt(2) + 1)
# problem: list of oracles (alpha, c); alpha = 1 are the backtracking trees of quantum monotone local search,
# c = 1 are polynomial-time approximations
LISTS = {
    "Feedback Vertex Set": [(1, 3.460), (2, 1)],
    "Subset Feedback Vertex Set": [(1, 4.0), (8, 1)],
    "Cluster Vertex Deletion": [(1, 1.811), (2, 1)],
    "Proper Interval Vertex Deletion": [(1, 6.0), (6, 1)],
    "Multicut on Trees": [(1, MCT), (2, 1)],
    "3-Hitting Set": [(1, 2.168), (3, 1)] + list(HS3.items()),
    "4-Hitting Set": [(1, 4.0), (4, 1)],
    "Vertex Cover": [(2, 1)] + list(VC.items()),
}
BETAS = (1.1, 1.2, 1.3, 1.4, 1.5, 1.6, 1.8, 2.0)


def H(p):
    return 0.0 if p <= 0 or p >= 1 else -p * math.log(p) - (1 - p) * math.log(1 - p)


def rate(kap, tau, x):
    """lim -(1/n) ln Pr[|X cap K| >= x n], |X| = tau n, |K| = kap n; inf if impossible."""
    if x <= tau * kap:
        return 0.0
    if x > min(tau, kap) + 1e-15:
        return math.inf
    return H(tau) - kap * H(x / kap) - (1 - kap) * H((tau - x) / (1 - kap)) if kap < 1 else 0.0


def g(kap, tau, beta, a, c):
    x = max(0.0, (1 - beta / a) * kap + tau / a)
    return (kap - x) * math.log(c) + rate(kap, tau, x)


def inner(kap, beta, L, m=400):
    best = math.inf
    for a, c in L:
        lo, hi = 0.0, min(1.0, beta * kap)
        ts = np.linspace(lo, hi, m + 1)
        vals = [g(kap, t, beta, a, c) for t in ts]
        i = int(np.argmin(vals))
        a0, b0 = ts[max(i - 1, 0)], ts[min(i + 1, m)]
        for _ in range(60):                       # golden refinement; any tau gives an upper bound
            m1, m2 = a0 + (b0 - a0) * 0.382, a0 + (b0 - a0) * 0.618
            if g(kap, m1, beta, a, c) < g(kap, m2, beta, a, c):
                b0 = m2
            else:
                a0 = m1
        best = min(best, vals[i], g(kap, (a0 + b0) / 2, beta, a, c))
    return best


def best_base(L, beta, m=400):
    ks = np.linspace(0, 1 / beta, m + 1)[1:]
    vals = [inner(k, beta, L) for k in ks]
    i = int(np.argmax(vals))
    a0, b0 = ks[max(i - 1, 0)], ks[min(i + 1, m - 1)]
    for _ in range(60):
        m1, m2 = a0 + (b0 - a0) * 0.382, a0 + (b0 - a0) * 0.618
        if inner(m1, beta, L) > inner(m2, beta, L):
            b0 = m2
        else:
            a0 = m1
    return math.exp(max(max(vals), inner((a0 + b0) / 2, beta, L)))


def worst(n, beta, L):
    """log of the exact discrete cost max_k min_{(alpha,c),t} c^l / hyper(n, k, t, x)."""
    out = -math.inf
    for k in range(1, int(n / beta) + 1):
        t = np.arange(0, min(n, int(beta * k)) + 1)
        v = np.inf
        for a, c in L:
            x = np.maximum(0, np.ceil((1 - beta / a) * k + t / a - 1e-9))
            lh = hypergeom.logsf(x - 1, n, k, t)          # log Pr[Y >= x]
            v = min(v, np.min((k - x) * math.log(c) - lh))
        out = max(out, v)
    return out


def up(x, d=4):
    return math.ceil(x * 10**d - 1e-12) / 10**d


if __name__ == "__main__":
    # values of the SODA 2024 paper, Table 2 (Li-Nederlof base 2.69998 for Feedback Vertex Set)
    for L, beta, ref in (([(2, 1)], 1.5, 1.2072), ([(1, 2.69998)], 1.5, 1.2099), ([(1, 2.69998), (2, 1)], 1.5, 1.2068),
                         ([(1, 2.69998)], 1.1, 1.4156), ([(1.1, 1.1652)], 1.1, 1.114), ([(1, 3.0)], 1.0, 5 / 3)):
        b = best_base(L, beta)
        assert abs(b - ref) < 6e-4, (L, beta, b, ref)
    print("reference values reproduced")
    for name, L in LISTS.items():
        for beta in BETAS:
            if name == "Vertex Cover" and beta >= 2:
                continue
            Lb = L
            b = best_base(Lb, beta)
            n = 1000
            ex = worst(n, beta, Lb) - n * math.log(b)
            assert ex <= 2 * math.log(n + 1), (name, beta, ex)
            print(f"{name:32s} beta = {beta:.1f}  best = {b:.5f}  quantum = {math.sqrt(b):.5f} <= "
                  f"{up(math.sqrt(b))}  (n = {n}: excess {ex:+.2f})")
    print("all bounds hold")
