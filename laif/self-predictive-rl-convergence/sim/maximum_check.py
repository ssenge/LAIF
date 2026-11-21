"""Checks of Theorem 3 of README.md: (i) f(Phi) <= F for every Phi whose predictor Q has p' positive and n' negative
eigenvalues, F = sum of squares of the p' largest positive and n' smallest negative eigenvalues of T (Cauchy
interlacing), with equality at the subspaces of the form (i), also with ties and zero eigenvalues;
(ii) turning u_i by the angle s towards v_j changes f by 2 mu_i (lambda_j - mu_i) s^2 + O(s^4)."""
import numpy as np
rng = np.random.default_rng(2)
def F(lam, pp, nn):
    return np.sum(np.sort(lam[lam > 0])[::-1][:pp] ** 2) + np.sum(np.sort(lam[lam < 0])[:nn] ** 2)
worst = -np.inf
for trial in range(400):
    n, k = rng.integers(3, 9), None; k = int(rng.integers(1, n))
    if trial % 2:                                            # ties and zero eigenvalues
        lam = rng.choice([-1.0, -0.4, 0.0, 0.4, 1.0], size=n)
    else:
        lam = rng.standard_normal(n)
    V, _ = np.linalg.qr(rng.standard_normal((n, n))); T = V @ np.diag(lam) @ V.T
    for _ in range(20):
        Phi, _ = np.linalg.qr(rng.standard_normal((n, k)))
        q = np.linalg.eigvalsh(Phi.T @ T @ Phi); pp, nn = int((q > 1e-12).sum()), int((q < -1e-12).sum())
        gap = np.sum(q ** 2) - F(lam, pp, nn); worst = max(worst, gap)
        assert gap <= 1e-10, (lam, q)
    # equality at a subspace of the form (i) with p = number of positive eigenvalues chosen at random
    npos, nneg = int((lam > 0).sum()), int((lam < 0).sum())
    lo, hi = max(0, k - nneg), min(k, npos)
    if lo <= hi:
        p = int(rng.integers(lo, hi + 1))
        idx = list(np.argsort(-lam)[:p]) + list(np.argsort(lam)[:k - p])
        S = V[:, idx]; assert abs(np.sum(np.linalg.eigvalsh(S.T @ T @ S) ** 2) - F(lam, p, k - p)) < 1e-10
# (ii): exact rotation, coefficient of s^2
lam = np.array([1.0, 0.5, -0.3, -0.9]); T = np.diag(lam); e = np.eye(4)
for i, j in [(1, 0), (0, 1), (2, 3), (3, 2), (1, 3)]:
    others = [m for m in [0, 1, 2, 3] if m not in (i, j)][:1]
    f = lambda s: np.sum(np.linalg.eigvalsh((lambda P: P.T @ T @ P)(np.column_stack([np.cos(s) * e[:, i] + np.sin(s) * e[:, j]] + [e[:, m] for m in others]))) ** 2)
    s = 1e-3; c = (f(s) - f(0)) / s ** 2
    assert abs(c - 2 * lam[i] * (lam[j] - lam[i])) < 1e-5, (i, j, c)
print("interlacing bound holds in 8000 random cases (largest f - F:", f"{worst:.2e})", "; s^2 coefficients match")
