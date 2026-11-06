"""Checks for greedy coordinate descent in quantum Boltzmann machine learning.

Model rho_theta = exp(sum_i theta_i H_i)/Z with Pauli terms H_i; target eta. One step on a coordinate
with s(g_i - h_i) >= eps' sets theta_i -= eps' s and must lower S(eta||rho_theta) by at least eps'^2/2.
"""
import itertools
import numpy as np
from scipy.linalg import logm
from scipy.optimize import minimize

P1 = {"I": np.eye(2), "X": np.array([[0, 1], [1, 0]]), "Y": np.array([[0, -1j], [1j, 0]]),
      "Z": np.diag([1.0, -1.0])}


def pauli(word):
    M = np.array([[1.0]])
    for c in word:
        M = np.kron(M, P1[c])
    return M


def local_terms(n, k, rng, m):
    words = set()
    while len(words) < m:
        w = ["I"] * n
        for q in rng.choice(n, size=int(rng.integers(1, k + 1)), replace=False):
            w[q] = "XYZ"[int(rng.integers(3))]
        words.add("".join(w))
    return [pauli(w) for w in sorted(words)]


def gibbs(H):
    w, V = np.linalg.eigh(H)
    p = np.exp(w - w.max())
    return (V * (p / p.sum())) @ V.conj().T


def rel_entropy(eta, rho):
    return float(np.real(np.trace(eta @ (logm(eta) - logm(rho)))))


def run(n, k, m, eps, rng, noise=True):
    Hs = local_terms(n, k, rng, m)
    # target: Gibbs state of a different Hamiltonian, with terms outside the ansatz
    extra = local_terms(n, k + 1, rng, 2 * m)
    Ht = sum(rng.normal() * h for h in Hs) + sum(0.5 * rng.normal() * h for h in extra)
    eta = gibbs(Ht)
    h = np.array([np.real(np.trace(eta @ H)) for H in Hs])
    kappa = xi = eps / 6
    hh = h + (rng.uniform(-xi, xi, size=m) if noise else 0)  # data estimates
    theta = np.zeros(m)
    rho = gibbs(np.zeros_like(Hs[0]))
    S0 = rel_entropy(eta, rho)
    steps, min_drop = 0, np.inf
    while True:
        g = np.array([np.real(np.trace(rho @ H)) for H in Hs])
        gh = g + (rng.uniform(-kappa, kappa, size=m) if noise else 0)  # shadow estimates
        gap = gh - hh
        i = int(np.argmax(np.abs(gap)))
        if abs(gap[i]) <= 2 * eps / 3:
            assert np.max(np.abs(g - h)) <= eps + 1e-12
            break
        s = np.sign(gap[i])
        assert s * (g[i] - h[i]) > eps / 3  # the step direction is correct
        S_old = rel_entropy(eta, rho)
        theta[i] -= (eps / 3) * s
        rho = gibbs(sum(t * H for t, H in zip(theta, Hs)))
        drop = S_old - rel_entropy(eta, rho)
        min_drop = min(min_drop, drop)
        assert drop >= (eps / 3) ** 2 / 2 - 1e-10
        steps += 1
    assert steps <= 18 * S0 / eps ** 2
    return steps, S0, min_drop


def log_z(theta, Hs):
    w = np.linalg.eigvalsh(sum(t * H for t, H in zip(theta, Hs)))
    return w.max() + np.log(np.exp(w - w.max()).sum())


def run_worst_case(n, k, m, eps, rng, pure=False):
    """Worst case for the lemma: step on the violated coordinate with the smallest true gap above eps/3
    (estimates off by eps/6 so that its estimated gap just exceeds 2eps/3). delta0 by convex minimisation."""
    Hs = local_terms(n, k, rng, m)
    if pure:  # rank one target: no minimiser, only an infimum
        v = rng.normal(size=2 ** n) + 1j * rng.normal(size=2 ** n)
        eta = np.outer(v, v.conj()) / np.vdot(v, v).real
    else:
        extra = local_terms(n, k + 1, rng, 2 * m)
        eta = gibbs(sum(rng.normal() * h for h in Hs) + sum(0.5 * rng.normal() * h for h in extra))
    h = np.array([np.real(np.trace(eta @ H)) for H in Hs])
    S = lambda t: log_z(t, Hs) - t @ h  # S(eta||rho_theta) + S(eta)
    grad = lambda t: np.array([np.real(np.trace(gibbs(sum(a * H for a, H in zip(t, Hs))) @ H)) for H in Hs]) - h
    S_inf = minimize(S, np.zeros(m), jac=grad, method="BFGS", options={"gtol": 1e-10, "maxiter": 5000}).fun
    delta0 = S(np.zeros(m)) - S_inf  # <= the true delta0, so the step bound below is checked at least as strictly
    theta, steps, ratio = np.zeros(m), 0, np.inf
    while True:
        gap = grad(theta)
        viol = [i for i in range(m) if abs(gap[i]) > eps / 3 + 1e-9]
        if not viol:
            break
        i = min(viol, key=lambda j: abs(gap[j]))
        old = S(theta)
        theta[i] -= (eps / 3) * np.sign(gap[i])
        ratio = min(ratio, (old - S(theta)) / ((eps / 3) ** 2 / 2))
        steps += 1
        assert ratio >= 1 - 1e-8
    assert steps <= 18 * delta0 / eps ** 2
    return steps, delta0, ratio


if __name__ == "__main__":
    rng = np.random.default_rng(13)
    for n, k, m, eps in [(3, 2, 8, 0.1), (4, 2, 12, 0.08), (5, 2, 20, 0.1), (5, 3, 30, 0.15)]:
        steps, S0, md = run(n, k, m, eps, rng)
        print(f"n = {n}, k = {k}, m = {m}, eps = {eps}: {steps} steps <= 18 S0/eps^2 = "
              f"{18 * S0 / eps ** 2:.0f}; every step lowered S by >= {md:.5f} >= (eps/3)^2/2 = "
              f"{(eps / 3) ** 2 / 2:.5f}; last iterate within eps on all {m} terms")
    for n, k, m, eps, pure in [(3, 2, 8, 0.1, False), (4, 2, 12, 0.08, False), (5, 2, 20, 0.1, False),
                               (5, 3, 30, 0.15, False), (4, 2, 12, 0.1, True)]:
        steps, d0, ratio = run_worst_case(n, k, m, eps, rng, pure)
        print(f"worst case, n = {n}, k = {k}, m = {m}, eps = {eps}{', pure target' if pure else ''}: {steps} steps "
              f"<= 18 delta0/eps^2 = {18 * d0 / eps ** 2:.0f}; smallest drop {ratio:.3f} (eps/3)^2/2")
    print("greedy coordinate descent checks pass")
