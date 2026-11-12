"""Checks for the lower-bound instances (energy x = number of excited levels, Gibbs weight c_x e^{beta x}
in the convention of the classical construction; the Hamiltonian is E = n - x).
Base counts: coefficients of g(t) = prod_{k<n} (e^k + t); alternates c^±_x = e^{±nu x} c_x, nu = 10 eps / n.
Asserts, in log space:
  (1) ||sqrt(mu^±_beta) - sqrt(mu_beta)|| <= nu for beta on a grid in [0, 4n] and at beta = infinity;
  (2) |log Q^±(inf) - log Q(inf)| > 2.02 eps, Q(inf) = c_n / Z(0) (ground-state fraction);
  (3) q = log(Z(0)/c_n) lies in [n(n-1)/2, n(n-1)/2 + 2];
  (4) the integer realization (counts scaled by K = ceil(10 n / eps), rounded, totals equalized)
      moves each qsample by at most 0.07 nu and log Q by at most 0.07 nu;
  (5) ||R_a - R_b|| <= 2 ||a - b|| for reflections about unit vectors a, b (random tests)."""
import numpy as np
from scipy.special import logsumexp

rng = np.random.default_rng(5)


def log_counts(n):
    """log of the coefficients c_0..c_n of prod_{k<n} (e^k + t), by a log-space recursion."""
    lc = np.array([0.0])                       # polynomial 1
    for k in range(n):
        new = np.full(len(lc) + 1, -np.inf)
        new[:-1] = np.logaddexp(new[:-1], lc + k)   # e^k * c_j -> t^j
        new[1:] = np.logaddexp(new[1:], lc)          # t * c_j -> t^{j+1}
        lc = new
    return lc


def sqrt_mu(lc, beta):
    x = np.arange(len(lc))
    if np.isinf(beta):
        v = np.zeros(len(lc)); v[-1] = 1.0
        return v
    lw = lc + beta * x
    return np.exp(0.5 * (lw - logsumexp(lw)))


def logQinf(lc):
    return lc[-1] - logsumexp(lc)


def realize(lc, lZ0, K):
    """integer counts round(K * c_x * Z0 / Z), with the largest count adjusted so that all totals equal K * Z0.
    Returns the log of the relative perturbation bound max_x |c'_x / c_x - 1| (computed exactly for the small
    counts; the large counts change by at most 1/2 + n, relative to at least K e^{-1})."""
    l = lc - logsumexp(lc) + lZ0 + np.log(K)          # log of K * normalized count
    small = l < 40                                    # exact rounding where it matters numerically
    rel = np.zeros(len(l))
    vals = np.exp(l[small])
    rel[small] = np.abs(np.round(vals) - vals) / vals
    rel[~small] = (0.5 + len(l)) * np.exp(-l[~small])
    return rel.max()


def main():
    for n in [7, 12, 25, 50, 100, 200]:
        for eps in [1e-2, 1e-3, 1e-5]:
            nu = 10 * eps / n
            x = np.arange(n + 1)
            lc = log_counts(n)
            lZ0 = logsumexp(lc)
            q = lZ0 - lc[-1]
            assert n * (n - 1) / 2 <= q <= n * (n - 1) / 2 + 2, (n, q)
            dmax = 0
            for s in [+1, -1]:
                la = lc + s * nu * x
                for beta in list(np.linspace(0, 4 * n, 801)) + [np.inf]:
                    d = np.linalg.norm(sqrt_mu(la, beta) - sqrt_mu(lc, beta))
                    dmax = max(dmax, d / nu)
                diff = abs(logQinf(la) - logQinf(lc))
                assert diff > 2.02 * eps, (n, eps, diff / eps)
            assert dmax <= 1 + 1e-9, dmax
            K = int(np.ceil(10 * n / eps))
            rel = max(realize(lc + s * nu * x, lZ0, K) for s in [0, 1, -1])
            assert 3 * rel <= 0.07 * nu, (n, eps, rel / nu)
            print(f"n = {n:3d}, eps = {eps:.0e}: q = {q:9.1f}, max ||sqrt mu^± - sqrt mu|| / nu = {dmax:.4f}, "
                  f"|log Q^± - log Q| / eps >= {min(abs(logQinf(lc + s * nu * x) - logQinf(lc)) for s in [1, -1]) / eps:.3f}, "
                  f"rounding 3 eta / nu = {3 * rel / nu:.1e}")
    for _ in range(2000):
        d = rng.integers(2, 10)
        a = rng.normal(size=d); a /= np.linalg.norm(a)
        b = a + rng.normal(size=d) * rng.uniform(0, 1); b /= np.linalg.norm(b)
        Ra = np.eye(d) - 2 * np.outer(a, a); Rb = np.eye(d) - 2 * np.outer(b, b)
        assert np.linalg.norm(Ra - Rb, 2) <= 2 * np.linalg.norm(a - b) + 1e-12
    print("reflections: ||R_a - R_b|| <= 2||a - b|| on 2000 pairs")
    print("check: all asserts passed")


if __name__ == "__main__":
    main()
