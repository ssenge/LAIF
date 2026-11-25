"""Optimal harvesting threshold by bisection on the sign rule.

Model: dX = X(mu - kappa X - h) dt + sigma X dB, h = M above the threshold eta, 0 below.
Dimensionless numbers: a = 2 mu / sigma^2 (> 1), beta = 2 M / sigma^2, alpha = a - beta, x = 2 kappa eta / sigma^2.

Yield (eq. 4.4 of arXiv:1710.01221 in closed form):
    H(eta) = (M sigma^2 / (2 kappa)) * x^beta Gamma(alpha, x) / (gamma(a - 1, x) + x^beta Gamma(alpha - 1, x)),
with gamma, Gamma the lower and upper incomplete gamma functions.
Sign rule: sign H'(eta) = sign S(x), where
    S(x) = (beta Gamma(alpha, x) - x^alpha e^-x) gamma(a - 1, x) - x^a e^-x Gamma(alpha - 1, x).
S > 0 on (0, xi) and S < 0 on (xi, inf) for a unique xi < a; the optimal threshold is eta* = sigma^2 xi / (2 kappa).
Bisection: hi = a (S(a) < 0); lo = a / 2^k for the first k with S > 0; then halve the bracket.

Run: python optimal_threshold.py   (a few seconds, 1 core). Writes the table to data/xi_table.csv.
"""
import csv
import os

import mpmath as mp

mp.mp.dps = 30


def Gup(s, x):
    return mp.gammainc(s, x, mp.inf)


def Glow(s, x):
    return mp.gammainc(s, 0, x)


def yield_scaled(x, a, beta):
    """H / (M sigma^2 / (2 kappa)) as a function of the scaled threshold x."""
    al = a - beta
    return x ** beta * Gup(al, x) / (Glow(a - 1, x) + x ** beta * Gup(al - 1, x))


def S(x, a, beta):
    al = a - beta
    return (beta * Gup(al, x) - x ** al * mp.e ** (-x)) * Glow(a - 1, x) - x ** a * mp.e ** (-x) * Gup(al - 1, x)


def xi_opt(a, beta, tol=mp.mpf(10) ** -12):
    """Unique root of S in (0, a), by bisection. Returns (xi, number of S evaluations)."""
    a, beta = mp.mpf(a), mp.mpf(beta)
    hi = a
    assert S(hi, a, beta) < 0
    lo, n = a / 2, 1
    while S(lo, a, beta) <= 0:
        lo /= 2; n += 1
        assert n < 2000
    while hi - lo > tol * hi:
        mid = (lo + hi) / 2; n += 1
        if S(mid, a, beta) > 0: lo = mid
        else: hi = mid
    return (lo + hi) / 2, n


def H_dim(eta, mu, M, kappa, s2):
    a, beta = 2 * mu / s2, 2 * M / s2
    return M * s2 / (2 * kappa) * yield_scaled(2 * kappa * mp.mpf(eta) / s2, a, beta)


def optimal(mu, M, kappa, s2):
    """Optimal threshold eta* and maximal long-run yield, in the units of the model."""
    a, beta = 2 * mp.mpf(mu) / s2, 2 * mp.mpf(M) / s2
    xi, _ = xi_opt(a, beta)
    return s2 * xi / (2 * kappa), H_dim(s2 * xi / (2 * kappa), mu, M, kappa, s2)


def main():
    # 1. bisection agrees with a grid argmax of H, and S has one sign change
    for (a, beta) in [(2, 2), (1.2, 0.3), (1.05, 3), (6, 1), (20, 4), (3, 0.05), (1.5, 1.5)]:
        xi, n = xi_opt(a, beta)
        grid = [a * mp.mpf(i) / 4000 for i in range(1, 4000)]
        vals = [yield_scaled(x, a, beta) for x in grid]
        i = max(range(len(vals)), key=lambda j: vals[j])
        assert abs(grid[i] - xi) <= 2 * a / 4000, (a, beta, xi, grid[i])
        signs = [mp.sign(S(x, a, beta)) for x in grid[::20]]
        assert sum(1 for k in range(len(signs) - 1) if signs[k] != signs[k + 1]) == 1, (a, beta)
        assert 0 < xi < a
    print("bisection = grid argmax, one sign change: ok")
    # 2. the closed form equals the expression of check.py (independent normalization)
    import sys
    sys.path.insert(0, os.path.dirname(__file__))
    from check import H_closed
    for p in [(1, 1, 1, 1), (0.7, 0.2, 0.3, 0.5), (2.5, 1.7, 1.2, 0.8)]:
        for eta in (0.2, 0.9):
            assert abs(H_dim(eta, *p) - H_closed(eta, *p)) < 1e-12 * H_closed(eta, *p)
    print("closed form = check.py H: ok")
    # 3. Figure 1 of arXiv:1710.01221 (mu = M = kappa = sigma^2 = 1): a = 2, beta = 2
    eta, Hs = optimal(1, 1, 1, 1)
    print("Fig. 1: eta* =", mp.nstr(eta, 10), " H* =", mp.nstr(Hs, 10))
    assert abs(eta - mp.mpf("0.46432969")) < 1e-7
    # 4. table of xi(a, beta) and h = H* / (M sigma^2 / (2 kappa))
    out = os.path.join(os.path.dirname(__file__), "data")
    os.makedirs(out, exist_ok=True)
    rows = []
    for a in (1.25, 1.5, 2, 3, 5, 10):
        for beta in (0.25, 0.5, 1, 2, 4):
            xi, n = xi_opt(a, beta)
            rows.append((a, beta, float(xi), float(yield_scaled(xi, a, beta)), "I" if a - beta > 1 else "II", n))
    with open(os.path.join(out, "xi_table.csv"), "w", newline="") as fh:
        w = csv.writer(fh); w.writerow(["a", "beta", "xi", "h", "case", "evals"]); w.writerows(rows)
    for r in rows:
        print("a=%-5s beta=%-5s xi=%.6f h=%.6f case %s evals %d" % r)


if __name__ == "__main__":
    main()
