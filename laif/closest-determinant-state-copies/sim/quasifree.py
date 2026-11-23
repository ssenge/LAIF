"""Checks for Corollary 3: pure free-fermion states, their overlap through the covariance matrices,
and the overlap bound 1 - |<psi1|psi2>|^2 <= ||M1 - M2||_2^2 / 8."""
import numpy as np
from scipy.linalg import expm
from math import sqrt
rng = np.random.default_rng(5)
X = np.array([[0, 1], [1, 0]]); Y = np.array([[0, -1j], [1j, 0]]); Z = np.diag([1, -1]); I2 = np.eye(2)
def kron(*a):
    r = np.eye(1)
    for x in a: r = np.kron(r, x)
    return r
def gens(m):
    g = []
    for j in range(m):
        g += [kron(*[Z] * j, X, *[I2] * (m - j - 1)), kron(*[Z] * j, Y, *[I2] * (m - j - 1))]
    return g
def cov(psi, g):  # M_ab = (i/2) <psi|[g_a, g_b]|psi>, real antisymmetric
    k = len(g)
    return np.array([[(0.5j * np.vdot(psi, (g[a] @ g[b] - g[b] @ g[a]) @ psi)).real for b in range(k)] for a in range(k)])
def rand_state(m, g, scale):
    H = rng.normal(size=(2 * m, 2 * m)) * scale; H = H - H.T
    U = expm(0.25 * sum(H[a, b] * g[a] @ g[b] for a in range(2 * m) for b in range(2 * m)))
    v = np.zeros(2 ** m, complex); v[0] = 1
    if rng.random() < 0.5: v = g[0] @ v  # odd parity as well
    return U @ v
worst = 0; cnt = 0
for m in (1, 2, 3, 4):
    g = gens(m)
    for _ in range(150):
        p1 = rand_state(m, g, rng.uniform(0, 2)); p2 = rand_state(m, g, rng.uniform(0, 2)) if rng.random() < 0.5 else expm(0.25 * sum(h * g[a] @ g[b] for (a, b), h in zip([(0, 1)], [rng.uniform(-0.3, 0.3)]))) @ p1
        M1, M2 = cov(p1, g), cov(p2, g)
        assert np.allclose(M1 @ M1, -np.eye(2 * m), atol=1e-9) and np.allclose(M1, -M1.T)
        ov = abs(np.vdot(p1, p2)) ** 2
        par1, par2 = round(np.linalg.det(M1)), 0
        pred = sqrt(max(np.linalg.det((M1 + M2) / 2), 0))
        assert abs(ov - pred) < 1e-8, (m, ov, pred)
        d = np.linalg.norm(M1 - M2) ** 2 / 8
        assert 1 - ov <= d + 1e-9
        D = 2 ** m; A = rng.normal(size=(D, D)) + 1j * rng.normal(size=(D, D)); rho = A @ A.conj().T; rho /= np.trace(rho).real
        dF = abs((p1.conj() @ rho @ p1 - p2.conj() @ rho @ p2).real)
        assert dF ** 2 <= (1 - ov) + 1e-9 and dF ** 2 <= d + 2e-9
        if d > 1e-12: worst = max(worst, (1 - ov) / d)
        cnt += 1
print(cnt, "pairs, m <= 4: overlap = sqrt(det((M1+M2)/2)); max (1-|<>|^2) / (||M1-M2||^2/8) =", round(worst, 4))
assert worst <= 1 + 1e-9
print("ok")
