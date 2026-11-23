"""Checks for the net, the selection step and the lower bound of the closest determinant state README."""
import numpy as np, itertools
from math import log, sqrt, comb
from bvar import b_float
rng = np.random.default_rng(3)

def wedge_state(U):  # amplitudes of the determinant state of the columns of U on the basis of n-subsets
    m, n = U.shape
    return np.array([np.linalg.det(U[list(r), :]) for r in itertools.combinations(range(m), n)])

def haar_stiefel(m, n):
    Q, _ = np.linalg.qr(rng.normal(size=(m, n)) + 1j * rng.normal(size=(m, n)))
    return Q

# Lemma 1: <S_U|S_V> = det(U^dag V) and |F(U) - F(V)| <= ||U - V||_2 for every state rho
worst = 0
for _ in range(3000):
    m = rng.integers(2, 8); n = rng.integers(1, m + 1)
    U = haar_stiefel(m, n)
    V = U + (10 ** rng.uniform(-3, 0)) * (rng.normal(size=(m, n)) + 1j * rng.normal(size=(m, n)))
    V, _ = np.linalg.qr(V)
    su, sv = wedge_state(U), wedge_state(V)
    assert abs(np.linalg.norm(su) - 1) < 1e-9 and abs(np.vdot(su, sv) - np.linalg.det(U.conj().T @ V)) < 1e-9
    D = len(su)
    A = rng.normal(size=(D, D)) + 1j * rng.normal(size=(D, D)); rho = A @ A.conj().T; rho /= np.trace(rho).real
    dF = abs((su.conj() @ rho @ su - sv.conj() @ rho @ sv).real)
    sig = np.linalg.svd(U.conj().T @ V, compute_uv=False)
    lhs = 1 - abs(np.prod(sig)) ** 2
    assert lhs <= np.sum(1 - sig ** 2) + 1e-12 <= 2 * np.sum(1 - sig) + 2e-12
    assert 2 * np.sum(1 - sig) <= np.linalg.norm(U - V) ** 2 + 1e-9
    assert dF <= sqrt(max(lhs, 0)) + 1e-9 and dF <= np.linalg.norm(U - V) + 1e-9
    worst = max(worst, dF / np.linalg.norm(U - V))
print("Lemma 1 on 3000 random instances: max |F(U)-F(V)| / ||U-V||_2 =", round(worst, 4))

# Lower bound: two orthogonal determinant states with weights 1/2 +- 2 eps; a fidelity >= OPT - eps forces a - b >= 1/2
for _ in range(20000):
    eps = rng.uniform(1e-4, 1 / 8)
    a = rng.uniform(0, 1); b = rng.uniform(0, 1 - a)
    if (0.5 + 2 * eps) * a + (0.5 - 2 * eps) * b >= 0.5 + eps:
        assert a - b >= 0.5 - 1e-12
# KL(Bern(1/2+2e) || Bern(1/2-2e)) = 4e ln((1+4e)/(1-4e)) <= 64 e^2 for e <= 1/8
for eps in np.linspace(1e-6, 1 / 8, 2001):
    kl = 4 * eps * log((1 + 4 * eps) / (1 - 4 * eps))
    p, q = 0.5 + 2 * eps, 0.5 - 2 * eps
    assert abs(kl - (p * log(p / q) + q * log(q / p))) < 1e-12 and kl <= 64 * eps ** 2 + 1e-15
print("lower bound reduction and KL bound ok")

# copy counts: Theorem 1 (explicit constant) against the exponents of the previous bound
def ours(m, n, eps, delta):
    k = min(n, m - n) if m > n else 0
    return 612 * b_float(m) * (2 * m * k * log(1 + 6 * sqrt(max(k, 1)) / eps) + log(2 / delta)) / eps ** 2
print("m n eps  Theorem1 (explicit constant)   m^2 n^2 ln(m/delta)/eps^2 and n^6/eps^4 (constants of [1] not stated)")
for m, n, eps in [(20, 4, 0.1), (50, 10, 0.1), (100, 10, 0.05), (200, 20, 0.05), (400, 40, 0.02)]:
    delta = 0.01
    print(m, n, eps, f"{ours(m, n, eps, delta):.2e}", f"{m*m*n*n*log(m/delta)/eps**2:.2e}", f"{n**6/eps**4:.2e}")
# ours / (m^2 n^2 ln(m/delta) / eps^2) -> 0 like ln(n/eps) * sqrt(ln m) ... / (sqrt(m) n); check monotone decrease along m = 10 n
r = [ours(10 * n, n, 0.05, 0.01) / ((10 * n) ** 2 * n * n * log(10 * n / 0.01) / 0.05 ** 2) for n in (2, 4, 8, 16, 32)]
assert all(x > y for x, y in zip(r, r[1:])), r
print("ratio Theorem 1 / m^2 n^2 ln(m/delta)/eps^2 along m = 10n:", [f"{x:.3g}" for x in r])
print("ok")
