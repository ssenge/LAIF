"""Checks for counting with Bernoulli oracles without the log factor.

1. The exact output law of amplitude estimation (phase estimation on the Grover iterate) against a direct simulation.
2. Inner decision: M = ceil(2 pi / Delta) gives the correct side of 1/2 with probability >= 8/pi^2 for every p with
   |p - 1/2| >= Delta (grid), and the error bound pi/M + pi^2/M^2 < Delta.
3. Outer decision: M = ceil(8 pi sqrt(a+e)/e) gives the correct side of a + e/2 with probability >= 8/pi^2 for every
   x <= a or x >= a + e (grid).
4. Geometric refinement with decisions that are wrong with probability delta_j and arbitrary in the gap: the final
   error is at most eps whenever no decision errs, and the cost sum_j r_j sqrt(a+e)/e stays below
   C (sqrt(rho)/eps + 1/sqrt(eps)).
Run: python -I check.py
"""
import math, random
import numpy as np

def ae_law(a, M):
    """Exact distribution of the outcome y in {0..M-1} of amplitude estimation with M points on amplitude a."""
    th = math.asin(math.sqrt(a)) / math.pi
    y = np.arange(M)
    def S(d):
        s = np.sin(np.pi * d / M)
        out = np.empty_like(d, dtype=float)
        small = np.abs(s) < 1e-12
        out[small] = 1.0
        out[~small] = np.sin(np.pi * d[~small]) ** 2 / (M ** 2 * s[~small] ** 2)
        return out
    return 0.5 * (S(y - M * th) + S(y + M * th))

def ae_direct(a, M):
    """Direct simulation: register sum_j |j> Q^j A|0>, inverse Fourier transform, outcome law."""
    phi = math.asin(math.sqrt(a))
    R = np.array([[math.cos(2 * phi), -math.sin(2 * phi)], [math.sin(2 * phi), math.cos(2 * phi)]])
    v = np.array([math.cos(phi), math.sin(phi)])           # (bad, good)
    states = np.zeros((M, 2))
    for j in range(M):
        states[j] = v; v = R @ v
    F = np.exp(-2j * np.pi * np.outer(np.arange(M), np.arange(M)) / M) / math.sqrt(M)
    amp = F @ (states / math.sqrt(M))
    return (np.abs(amp) ** 2).sum(axis=1)

def estimates(M):
    return np.sin(np.pi * np.arange(M) / M) ** 2

def check_law():
    for M in (2, 3, 5, 8, 13, 32):
        for a in (0.0, 0.03, 0.2, 0.5, 0.77, 1.0):
            p1, p2 = ae_law(a, M), ae_direct(a, M)
            assert abs(p1.sum() - 1) < 1e-9 and np.max(np.abs(p1 - p2)) < 1e-9, (M, a)

def check_inner():
    worst = 1.0
    for D in np.concatenate([np.linspace(0.01, 0.5, 50), [0.001, 0.003]]):
        M = math.ceil(2 * math.pi / D)
        assert math.pi / M + math.pi ** 2 / M ** 2 < D
        est = estimates(M)
        for p in np.concatenate([np.linspace(0, 0.5 - D, 40), np.linspace(0.5 + D, 1, 40)]):
            law = ae_law(p, M)
            ok = law[est >= 0.5].sum() if p > 0.5 else law[est < 0.5].sum()
            worst = min(worst, ok)
    assert worst >= 8 / math.pi ** 2, worst
    return worst

def check_outer():
    worst = 1.0
    for a in (0.0, 0.001, 0.01, 0.1, 0.3, 0.6):
        for e in (0.002, 0.01, 0.05, 0.2):
            if a + e > 1: continue
            M = math.ceil(8 * math.pi * math.sqrt(a + e) / e)
            est = estimates(M)
            for x in np.concatenate([np.linspace(0, a, 25), np.linspace(a + e, 1, 60)]):
                law = ae_law(x, M)
                ok = law[est < a + e / 2].sum() if x <= a else law[est >= a + e / 2].sum()
                worst = min(worst, ok)
    assert worst >= 8 / math.pi ** 2, worst
    return worst

def refine(rho, eps, rng, adversarial):
    """Geometric refinement; decision D(a, e) answers 1 if rho >= a + e and 0 if rho <= a, except with probability
    delta_j; in the gap the answer is random or adversarial. Returns (estimate, cost, any_error)."""
    J = max(1, math.ceil(math.log2(1 / eps)))
    l, cost, err = 0.0, 0.0, False
    for j in range(1, J + 1):
        e = 2.0 ** -j; dj = 2.0 ** -(J - j + 3); r = math.ceil(18 * math.log(4 / dj))
        ans = []
        for k in range(4):
            a = l + k * e
            cost += r * math.sqrt(min(1.0, a + e)) / e
            if rho >= a + e: t = 1
            elif rho <= a: t = 0
            else: t = (k % 2) if adversarial else rng.integers(2)
            if rng.random() < dj / 4: t = 1 - t; err = True
            ans.append(t)
        k1 = max([k for k in range(4) if ans[k] == 1], default=-1)
        l = l if k1 < 0 else l + k1 * e
    return l + 2.0 ** -J, cost, err   # interval [l, l + 2 e_J): midpoint

def check_refine():
    rng = np.random.default_rng(1)
    ratios = {}
    for eps in (0.1, 0.01, 1e-3, 1e-4, 1e-5):
        ratio = 0.0
        for rho in (0.0, eps / 3, eps, 0.01, 0.2, 0.5, 0.99, 1.0):
            fails = 0
            for t in range(200):
                est, cost, err = refine(rho, eps, rng, adversarial=(t % 2 == 0))
                if not err:
                    assert abs(est - rho) <= eps + 1e-12, (rho, eps, est)
                    eJ = 2.0 ** -max(1, math.ceil(math.log2(1 / eps)))   # the grid precision actually used, eps/2 < eJ <= eps
                    ratio = max(ratio, cost / (math.sqrt(rho) / eJ + 1 / math.sqrt(eJ)))
                fails += err
            assert fails / 200 <= 0.25 + 0.08, fails
        ratios[eps] = ratio
    return ratios

if __name__ == "__main__":
    check_law(); print("AE law ok")
    print("inner worst success", round(check_inner(), 4), ">= 8/pi^2 =", round(8 / math.pi ** 2, 4))
    print("outer worst success", round(check_outer(), 4))
    r = check_refine()
    # the constant must not grow as eps shrinks (no log(1/eps) factor)
    v = [r[k] for k in sorted(r, reverse=True)]
    inc = [v[i + 1] - v[i] for i in range(len(v) - 1)]
    assert all(inc[i + 1] <= 0.75 * inc[i] for i in range(1, len(inc) - 1)) and max(v) < 2100, r
    print("refinement ok, max cost / (sqrt(rho)/eps + 1/sqrt(eps)) per eps:", {k: round(v, 1) for k, v in r.items()})
