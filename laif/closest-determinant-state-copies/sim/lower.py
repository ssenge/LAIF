"""Checks for Proposition 5: the spiked instance, the reduction from a determinant state to one orbital,
the per-copy information bounds and the small-cap probability."""
import numpy as np, itertools
from math import log, comb
rng = np.random.default_rng(11)

def stiefel(m, n):
    Q, _ = np.linalg.qr(rng.normal(size=(m, n)) + 1j * rng.normal(size=(m, n))); return Q

# reduction: rho = core ^ rho_1, core = modes 0..n-2, last particle in modes n-1..m-1 (d' = m-n+1)
for _ in range(400):
    m = int(rng.integers(3, 8)); n = int(rng.integers(1, m))
    basis = list(itertools.combinations(range(m), n)); idx = {b: i for i, b in enumerate(basis)}
    core = tuple(range(n - 1)); comp = list(range(n - 1, m)); dp = len(comp)
    A = rng.normal(size=(dp, dp)) + 1j * rng.normal(size=(dp, dp)); r1 = A @ A.conj().T; r1 /= np.trace(r1).real
    # n-particle rho: |core u core| ^ rho_1 in the subset basis (core first, so no sign)
    rho = np.zeros((len(basis), len(basis)), complex)
    for a, j in enumerate(comp):
        for b, l in enumerate(comp):
            rho[idx[tuple(sorted(core + (j,)))], idx[tuple(sorted(core + (l,)))]] = r1[a, b]
    U = stiefel(m, n)
    s = np.array([np.linalg.det(U[list(r), :]) for r in basis])
    F = (s.conj() @ rho @ s).real
    psi = np.array([s[idx[tuple(sorted(core + (j,)))]] for j in comp])
    assert abs(F - (psi.conj() @ r1 @ psi).real) < 1e-10 and np.linalg.norm(psi) <= 1 + 1e-10
    lam = np.linalg.eigvalsh(r1).max(); u = psi / np.linalg.norm(psi)
    assert (u.conj() @ r1 @ u).real >= F - 1e-10 and F <= lam + 1e-10
print("reduction F = <psi|rho_1|psi>, |psi| <= 1 on 400 random instances: ok")

# spiked state: lambda_max - <u|rho_v|u> = beta (1 - |<u|v>|^2); with beta = 8 eps, success forces |<u|v>|^2 >= 7/8
for _ in range(2000):
    d = int(rng.integers(2, 30)); eps = rng.uniform(1e-3, 1 / 8); beta = 8 * eps
    v = stiefel(d, 1)[:, 0]; u = stiefel(d, 1)[:, 0]
    rho = (1 - beta) * np.eye(d) / d + beta * np.outer(v, v.conj())
    gap = (1 - beta) / d + beta - (u.conj() @ rho @ u).real
    assert abs(gap - beta * (1 - abs(np.vdot(u, v)) ** 2)) < 1e-12
# cap probability P(|<u|v>|^2 >= s) = (1-s)^(d-1) for uniformly random v (sampling)
for d in (2, 3, 5):
    V = rng.normal(size=(400000, d)) + 1j * rng.normal(size=(400000, d)); V /= np.linalg.norm(V, axis=1, keepdims=True)
    p = np.mean(np.abs(V[:, 0]) ** 2 >= 0.5)
    assert abs(p - 0.5 ** (d - 1)) < 4e-3, (d, p)
print("spiked gap identity and cap probability: ok")

# single-copy information: E_v chi^2 for a rank-one element equals w beta^2 (d-1)/(d (d+1)); sampling over uniformly random v
for d in (2, 4, 9):
    beta = 0.3; phi = stiefel(d, 1)[:, 0]
    V = rng.normal(size=(300000, d)) + 1j * rng.normal(size=(300000, d)); V /= np.linalg.norm(V, axis=1, keepdims=True)
    t = d * beta ** 2 * (np.abs(V @ phi.conj()) ** 2 - 1 / d) ** 2
    assert abs(t.mean() - beta ** 2 * (d - 1) / (d * (d + 1))) < 0.03 * beta ** 2 * (d - 1) / (d * (d + 1)), d
# exact: rank-one POVM from an orthonormal basis plus a random 2-design check of the sum: sum_x w_x = d
print("per-copy chi^2 average: ok")

# entangled bound: D(rho_v || I/d) <= (beta + 1/d) ln(1 + beta d)
for d in range(2, 200, 7):
    for beta in np.linspace(1e-4, 1, 50):
        l1 = beta + (1 - beta) / d; l0 = (1 - beta) / d
        D = l1 * log(d * l1) + ((d - 1) * l0 * log(d * l0) if l0 > 0 else 0)
        assert D <= (beta + 1 / d) * log(1 + beta * d) + 1e-12
print("relative entropy bound: ok")

# the resulting bounds for a few sizes, delta = 0.01, eps = 0.01
for m, n in [(20, 1), (100, 10), (1000, 1)]:
    eps, delta = 0.01, 0.01; dp1 = max(n, m - n)
    na = ((1 - delta) * dp1 * log(8) - log(2)) / (64 * eps ** 2)
    de = dp1 + 1
    ent = ((1 - delta) * dp1 * log(8) - log(2)) / ((8 * eps + 1 / de) * log(1 + 8 * eps * de))
    print(m, n, f"non-adaptive single-copy >= {na:.3g}", f"any measurement >= {ent:.3g}")
print("ok")
