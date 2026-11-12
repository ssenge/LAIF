"""Checks for the note on measurement budgets (README.md).

1. Worst-case random-sign complexity of the measurement class: exact values on a
   repeated orthonormal basis, and random states never exceed sqrt(d/n)/2.
2. The rescaled hinge loss equals |p - y| on [0,1] x {0,1}.
3. Estimators from binomial-basis coefficients are unbiased for polynomial losses.
4. Constants of the lower bound on the excess risk, and a learner that respects it.
5. Certificate values: the bound of [1] at its best split versus the bounds here.
"""
import math
from fractions import Fraction as Fr

import numpy as np

rng = np.random.default_rng(1)


def mean_abs_walk(m):
    """E|sigma_1 + ... + sigma_m| exactly."""
    return Fr(sum(math.comb(m, k) * abs(2 * k - m) for k in range(m + 1)), 2 ** m)


def complexity_basis(d, m):
    """Random-sign complexity of the measurement class on n = m d basis states."""
    return d * mean_abs_walk(m) / (2 * m * d)


def complexity_mc(states, trials=400):
    """E_sigma ||sum_i sigma_i rho_i||_1 / (2n), by sampling sigma."""
    n = len(states)
    vals = []
    for _ in range(trials):
        s = rng.choice([-1.0, 1.0], n)
        a = np.tensordot(s, states, axes=1)
        vals.append(np.abs(np.linalg.eigvalsh(a)).sum() / (2 * n))
    return float(np.mean(vals)), float(np.std(vals) / math.sqrt(trials))


def random_states(n, d, rank):
    g = rng.normal(size=(n, d, rank)) + 1j * rng.normal(size=(n, d, rank))
    r = g @ g.conj().transpose(0, 2, 1)
    return r / np.trace(r, axis1=1, axis2=2).real[:, None, None]


def check_complexity():
    print("1. complexity / sqrt(d/n) on a repeated basis (n = m d):")
    for m in [1, 2, 3, 4, 10, 100, 1000]:
        ratio = float(complexity_basis(1, m)) * math.sqrt(m)
        assert 1 / (2 * math.sqrt(2)) - 1e-12 <= ratio <= 0.5 + 1e-12
        print(f"   m={m:5d}: {ratio:.4f}")
    print(f"   limit 1/sqrt(2 pi) = {1 / math.sqrt(2 * math.pi):.4f}")
    for m in range(1, 60):
        assert mean_abs_walk(m) ** 2 >= Fr(m, 2)
    print("   random states, complexity / (sqrt(d/n)/2):")
    for d, n, rank in [(4, 40, 1), (16, 64, 1), (16, 400, 1), (16, 400, 4), (8, 8, 1)]:
        v, e = complexity_mc(random_states(n, d, rank))
        bound = min(1.0, math.sqrt(d / n)) / 2
        assert v <= bound + 4 * e
        print(f"   d={d:3d} n={n:4d} rank={rank}: {v / bound:.3f} +- {e / bound:.3f}")


def check_hinge():
    p = np.linspace(0, 1, 1001)
    for y in (0, 1):
        hinge = 0.5 * np.maximum(0, 1 - (2 * y - 1) * (2 * p - 1))
        assert np.allclose(hinge, np.abs(p - y))
    print("2. rescaled hinge = |p - y| on [0,1] x {0,1}: ok")


def binomial_basis(coeffs):
    """Binomial-basis coefficients of the polynomial sum_k coeffs[k] p^k, degree r = len - 1."""
    r = len(coeffs) - 1
    return [sum(Fr(math.comb(j, k), math.comb(r, k)) * coeffs[k] for k in range(j + 1))
            for j in range(r + 1)]


def check_unbiased():
    # (p - y)^2 for y = 0, 1 and a degree-3 example
    losses = {"p^2": [0, 0, 1], "(1-p)^2": [1, -2, 1], "p^3 - p/2 + 1/2": [Fr(1, 2), Fr(-1, 2), 0, 1]}
    for name, c in losses.items():
        beta = binomial_basis(c)
        r = len(c) - 1
        for S in range(r, r + 4):
            for p in [Fr(0), Fr(1, 3), Fr(5, 7), Fr(1)]:
                # U-statistic over all r-subsets of S shots, averaged exactly over the shot law
                est = 0
                for K in range(S + 1):
                    law = math.comb(S, K) * p ** K * (1 - p) ** (S - K)
                    u = sum(Fr(math.comb(K, j) * math.comb(S - K, r - j), math.comb(S, r)) * beta[j]
                            for j in range(r + 1))
                    est += law * u
                assert est == sum(ck * p ** k for k, ck in enumerate(c))
        print(f"3. {name}: binomial-basis coefficients {[str(b) for b in beta]}, unbiased for S = r..r+3")


def check_lower_bound():
    # KL(Ber(1/2+e) || Ber(1/2-e)) per sample, times n/d samples per basis state
    worst = 0.0
    for nd in np.linspace(1, 1e4, 20001):
        eps = math.sqrt(1 / nd) / 8
        kl = nd * 2 * eps * math.log((1 + 2 * eps) / (1 - 2 * eps))
        worst = max(worst, kl)
    tv = math.sqrt(worst / 2)
    const = (1 - tv) / 8
    assert worst <= 0.25 and const >= 0.08
    print(f"4. max relative entropy = {worst:.4f}, TV <= {tv:.4f}, excess risk >= {const:.4f} sqrt(d/n)")
    # a plug-in learner (vote per basis state) on the hard family; its excess must exceed the bound
    for d, n in [(4, 400), (16, 1600), (16, 16000)]:
        eps = math.sqrt(d / n) / 8
        exc = []
        for _ in range(2000):
            tau = rng.choice([-1, 1], d)
            j = rng.integers(0, d, n)
            y = rng.random(n) < 0.5 + eps * tau[j]
            votes = np.bincount(j, weights=2 * y - 1.0, minlength=d)
            pred = np.where(votes > 0, 1.0, np.where(votes < 0, 0.0, 0.5))
            # excess risk of predicting p_j: (2 eps / d) * (1 - p_j if tau = 1 else p_j)
            exc.append(np.sum(2 * eps / d * np.where(tau > 0, 1 - pred, pred)))
        print(f"   vote learner d={d} n={n}: excess / sqrt(d/n) = {np.mean(exc) / math.sqrt(d / n):.4f}")
        assert np.mean(exc) >= const * math.sqrt(d / n)


def check_certificates():
    print("5. gap terms at d = 16, delta = 0.05, L = 1 (lower is better):")
    d, delta = 16, 0.05
    for B in [10 ** 4, 10 ** 6, 10 ** 8]:
        def theirs(n):
            S = B / n
            return (2 * math.sqrt(d / n) + math.sqrt(math.log(4 * n / delta) / (2 * S))
                    + math.sqrt(math.log(2 / delta) / (2 * n)))

        def lipschitz(n):
            S = B / n
            return (math.sqrt(d / n) + 1 / (2 * math.sqrt(S)) + math.sqrt(math.log(2 / delta) / (2 * B))
                    + math.sqrt(math.log(2 / delta) / (2 * n)))

        grid = np.unique(np.logspace(0, math.log10(B), 4000).astype(int))
        nt = min(grid, key=theirs)
        nl = min(grid, key=lipschitz)
        linear = math.sqrt(d / B) + 2 * math.sqrt(math.log(2 / delta) / (2 * B))  # n = B, S = 1
        print(f"   B=1e{int(math.log10(B))}: [1] {theirs(nt):.4f} (n={nt}), "
              f"slope-L loss here {lipschitz(nl):.4f} (n={nl}), linear loss here {linear:.4f} (n=B, S=1)")
        assert lipschitz(nl) < theirs(nt) and linear < lipschitz(nl)


if __name__ == "__main__":
    check_complexity()
    check_hinge()
    check_unbiased()
    check_lower_bound()
    check_certificates()
    print("all checks passed")
