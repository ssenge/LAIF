"""Order-a version of the bound: gap_a(psi) = ln int|W| - Delta_a(Q), with
Delta_a = (1/(1-a)) ln( a pi^{a-1} int Q^a ), the excess of the order-a entropy of Q over the vacuum value.
A positive gap is a violation. For number states Delta_a(n) = (lnGamma(an+1) - a ln n! - a n ln a)/(1-a)."""
import sys, numpy as np
from scipy.special import gammaln
from scipy.optimize import minimize, brentq
from search import tables, vec

def gap(c, T, a):
    Wmn, coh, h2 = T
    W = np.real(np.einsum("m,mnij,n->ij", np.conj(c), Wmn, c))
    Q = np.abs(np.einsum("nij,n->ij", coh, c)) ** 2 / np.pi
    return np.log(np.abs(W).sum() * h2) - np.log(a * np.pi ** (a - 1) * (Q ** a).sum() * h2) / (1 - a)

def delta_fock(a, n): return (gammaln(a * n + 1) - a * gammaln(n + 1) - a * n * np.log(a)) / (1 - a)

if __name__ == "__main__":
    D = int(sys.argv[1]); rng = np.random.default_rng(int(sys.argv[2])); starts = int(sys.argv[3])
    T = tables(D, 10.0, 301)
    for a in map(float, sys.argv[4:]):
        for n in range(D):                                   # grid check against the closed form
            e = np.zeros(D, complex); e[n] = 1
            Wn = np.log(np.abs(np.real(np.einsum("m,mnij,n->ij", e, T[0], e))).sum() * T[2])
            assert abs((Wn - gap(e, T, a)) - delta_fock(a, n)) < 2e-3, (a, n)
        best = -np.inf
        for s in range(starts):
            res = minimize(lambda p: -gap(vec(p, D), T, a), rng.normal(size=2 * D - 1), method="Nelder-Mead",
                           options={"maxiter": 3000, "xatol": 1e-6, "fatol": 1e-9})
            if -res.fun > best: best, bc = -res.fun, vec(res.x, D)
        print(f"a={a} D={D} max gap {best:.5f} state {np.round(np.abs(bc), 3)}", flush=True)
