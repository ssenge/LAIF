"""Exact checks of upper bounds on the gain alpha of the generalized short-path runtime (Theorems 4.2, 4.3 of
arXiv:2410.23270, used as Theorems 2, 3 in arXiv:2602.13494) for group relaxations: a coset x0 + K of a subgroup K of
Z_r^d, linear cost f(x) = c.x with representatives in [0, r), group walk on K (moves x -> x +- s, s in S) with holding
probability p0.

Quantities: L = ln(|K|/|K*|), Gamma = E_pi f - OPT, M = max f - OPT, Gamma_S = mean of f(x* +- s) - OPT over the moves s.
Claims checked:
  (a) every valid Delta_P(eta) obeys Delta_P >= E_{y ~ P(x*)} min(f(y) - OPT, eta |E*|)  (Def. 6 at an optimum x*);
  (b) condition (12)/(4) forces pi(E <= (1 - eta) E*) <= 1/16, hence eta |E*| <= (16/15) Gamma;
  (c) Poincare version: whenever pi(E <= (1 - eta) E*) < 1 (implied by gamma-spectral density with gamma > 0),
      alpha < (1/8)(1 - eta) (delta / (1 - p0)) M / (Gamma_S L), and delta / (1 - p0) <= 1 + 1/(|K| - 1);
  (d) the generator weight sum_{i: h_i != 0} |c_i| max(h_i, r - h_i) of a uniformly random element of K has mean >= M/4;
  (e) the family of Theorem 10 of 2602.13494 (K = t Z_{t^2}^m, unit costs) has M = m t (t - 1) = 2 Gamma.
"""
import itertools, math, sys
import numpy as np


def span(gens, r, d):
    K = {tuple([0] * d)}; frontier = list(K)
    while frontier:
        new = []
        for x in frontier:
            for g in gens:
                y = tuple((a + b) % r for a, b in zip(x, g))
                if y not in K: K.add(y); new.append(y)
        frontier = new
    return sorted(K)


instance_cost = [None]


def instance(rng, r, d, ngen, moves, p0):
    gens = [tuple(rng.integers(0, r, d)) for _ in range(ngen)]
    K = span(gens, r, d); x0 = tuple(rng.integers(0, r, d)); c = rng.integers(1, 6, d)
    X = [tuple((a + b) % r for a, b in zip(x0, k)) for k in K]; idx = {x: i for i, x in enumerate(X)}
    S = gens if moves == "gens" else [K[i] for i in rng.integers(1, len(K), max(2, int(2 * math.log(len(K)))))]
    S = [s for s in S if any(s)]
    P = np.zeros((len(X), len(X)))
    for x in X:
        P[idx[x], idx[x]] += p0
        for s in S:
            for sg in (1, -1):
                y = tuple((a + sg * b) % r for a, b in zip(x, s)); P[idx[x], idx[y]] += (1 - p0) / (2 * len(S))
    f = np.array([int(np.dot(c, x)) for x in X], float); instance_cost[0] = c
    return X, P, f, S


def theta(x, Eabs, eta):
    return np.minimum(0.0, (x / Eabs + 1 - eta) / eta)


def min_delta(P, H, Eabs, eta):
    """Smallest Delta with E_{y~P(x)} theta(H(y)) <= theta(H(x) + Delta) for all x (bisection; theta is monotone)."""
    lhs = P @ theta(H, Eabs, eta); lo, hi = 0.0, 4 * (H.max() - H.min()) + 4 * Eabs
    for _ in range(80):
        mid = (lo + hi) / 2
        if np.all(lhs <= theta(H + mid, Eabs, eta) + 1e-12): hi = mid
        else: lo = mid
    return hi


def check(rng, r, d, ngen, moves, p0, out):
    X, P, f, S = instance(rng, r, d, ngen, moves, p0)
    n = len(X); OPT = f.min(); star = np.flatnonzero(f == OPT); L = math.log(n / len(star))
    if L == 0 or len(S) == 0: return
    Gamma = f.mean() - OPT; M = f.max() - OPT
    ev = np.sort(np.linalg.eigvalsh((P + P.T) / 2)); assert np.allclose(P, P.T)
    delta = 1 - max(abs(ev[-2]), abs(ev[0]) if abs(ev[0] + 1) > 1e-12 else 0)
    assert delta / (1 - p0) <= 1 + 1 / (n - 1) + 1e-9
    xs = star[0]; nb = [j for j in np.flatnonzero(P[xs]) if j != xs or p0 == 0]
    Gamma_S = sum(P[xs, j] * (f[j] - OPT) for j in range(n) if j != xs) / (1 - p0)
    for eta in (0.1, 0.3, 0.5, 0.7, 0.9):
        for C in OPT + np.linspace(0.05, 3.0, 25) * max(M, 1):
            H = f - C; Eabs = C - OPT
            D = min_delta(P, H, Eabs, eta)
            lowb = sum(P[xs, j] * min(f[j] - OPT, eta * Eabs) for j in range(n))
            assert D >= lowb - 1e-6, (D, lowb)                                                    # (a)
            p = np.mean(H <= (1 - eta) * (-Eabs))
            ok12 = D > 0 and p > 0 and delta > 0 and 1 / (2 * math.sqrt(p)) - max(4 * math.log(n) / delta, 3 * Eabs ** 2 * (1 - eta) ** 2 / D ** 2) >= 2
            if ok12: assert p <= 1 / 16; out[1] += 1
            if p <= 1 / 16: assert eta * Eabs <= 16 / 15 * Gamma + 1e-9                         # (b)
            if p >= 1 or Gamma_S == 0: continue                        # the bound (c) only uses p < 1
            alpha = eta * (1 - eta) * Eabs * (delta / 4) / (2 * D * L)                             # sup over b < delta/4
            bound = 1 / 8 * (1 - eta) * delta / (1 - p0) * M / (Gamma_S * L)
            assert alpha <= bound + 1e-12, (alpha, bound)                                         # (c)
            out[0].append(alpha / bound)
    K = [tuple((a - b) % r for a, b in zip(x, X[0])) for x in X]; c = instance_cost[0]
    wt = [sum(ci * max(h, r - h) for ci, h in zip(c, k) if h) for k in K]
    assert np.mean(wt) >= M / 4 - 1e-9, (np.mean(wt), M)                                          # (d)


def theorem10_family(m, t):
    """Feasible coset {x* + t n : n in [t]^m} in Z_{t^2}^m with unit costs: exact M and Gamma by enumeration."""
    xs = [1] * m                                        # any minimizer with entries in [1, t)
    vals = [sum(xs[j] + t * nj[j] for j in range(m)) for nj in itertools.product(range(t), repeat=m)]
    return max(vals) - min(vals), np.mean(vals) - min(vals)


def test():
    for m, t in ((2, 2), (3, 3), (4, 2), (2, 5), (3, 4)):
        M, G = theorem10_family(m, t); assert M == m * t * (t - 1) and abs(M - 2 * G) < 1e-9             # (e)
    rng = np.random.default_rng(1); ratios = [[], 0]; cases = 0
    for r, d, ngen in ((2, 8, 3), (3, 6, 3), (4, 5, 2), (5, 4, 2), (3, 7, 4), (2, 10, 5), (6, 4, 3)):
        for moves in ("gens", "random"):
            for p0 in (0.0, 1 / 3, 0.5):
                for _ in range(3):
                    check(rng, r, d, ngen, moves, p0, ratios); cases += 1
    print(f"alpha_bounds self-checks passed: {cases} instances, {len(ratios[0])} (eta, shift) pairs with "
          f"pi(E <= (1-eta)E*) < 1, {ratios[1]} meeting condition (12), largest alpha/bound {max(ratios[0]):.3f}")


if __name__ == "__main__":
    test()
