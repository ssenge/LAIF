"""Linear-Gaussian controlled world and the population objective of a LeWM-type world model.

World: s' = A s + B a + w, a ~ N(0, I_m) white, w ~ N(0, Q), stationary covariance Sigma = A Sigma A^T + B B^T + Q.
Latent z = E s with E Sigma E^T = I_K (the zero set of the normality regularizer for normal data), linear predictor of
z' from (z, a). With E = U^T Sigma^{-1/2}, U^T U = I, and the whitened At = Sigma^{-1/2} A Sigma^{1/2},
Bt = Sigma^{-1/2} B, Qt = Sigma^{-1/2} Q Sigma^{-1/2} (At At^T + Bt Bt^T + Qt = I), the claim is
  loss(U) = K - J(U),  J(U) = ||U^T At U||_F^2 + tr(U^T Bt Bt^T U) = K - tr(U^T Qt U) - ||(I - U U^T) At^T U||_F^2.
Checks: (1) the formula against the residual of an explicit regression on simulated data; (2) gradient descent on the
sample loss with a whitening penalty reaches max_U J(U) found by a manifold optimizer over many starts.
"""
import numpy as np
from scipy.linalg import solve_discrete_lyapunov, sqrtm, expm


def world(d, m, rng, rho=0.9, qscale=0.3):
    A = rng.standard_normal((d, d)); A *= rho / max(abs(np.linalg.eigvals(A)))
    B = rng.standard_normal((d, m)); L = rng.standard_normal((d, d)) * qscale
    return A, B, L @ L.T


def whiten(A, B, Q):
    Sig = solve_discrete_lyapunov(A, B @ B.T + Q)
    S = np.real(sqrtm(Sig)); Si = np.linalg.inv(S)
    return Sig, Si @ A @ S, Si @ B, Si @ Q @ Si, Si


def J(U, At, Bt):
    return np.linalg.norm(U.T @ At @ U) ** 2 + np.trace(U.T @ Bt @ Bt.T @ U)


def maximize_J(At, Bt, K, rng, starts=30, iters=3000, lr=0.05):
    """Projected gradient ascent on the manifold of orthonormal K-frames (QR retraction), best of several starts."""
    d = At.shape[0]; best = (-1, None)
    for _ in range(starts):
        U = np.linalg.qr(rng.standard_normal((d, K)))[0]
        for _ in range(iters):
            M = U.T @ At @ U
            G = 2 * (At @ U @ M.T + At.T @ U @ M) + 2 * Bt @ Bt.T @ U
            G -= U @ (U.T @ G + G.T @ U) / 2
            U = np.linalg.qr(U + lr * G)[0]
        if J(U, At, Bt) > best[0]: best = (J(U, At, Bt), U)
    return best


def simulate(A, B, Q, T, rng):
    d, m = B.shape; Lq = np.linalg.cholesky(Q + 1e-12 * np.eye(d))
    s = np.zeros((T + 1, d)); a = rng.standard_normal((T, m))
    s[0] = np.linalg.cholesky(solve_discrete_lyapunov(A, B @ B.T + Q)) @ rng.standard_normal(d)
    for t in range(T): s[t + 1] = A @ s[t] + B @ a[t] + Lq @ rng.standard_normal(d)
    return s, a


def main():
    rng = np.random.default_rng(0)
    d, m, K = 8, 2, 3
    A, B, Q = world(d, m, rng)
    Sig, At, Bt, Qt, Si = whiten(A, B, Q)
    assert np.allclose(At @ At.T + Bt @ Bt.T + Qt, np.eye(d), atol=1e-9)
    # (1) formula against explicit regression
    s, a = simulate(A, B, Q, 400000, rng)
    for _ in range(3):
        U = np.linalg.qr(rng.standard_normal((d, K)))[0]; E = U.T @ Si
        z, z1 = s[:-1] @ E.T, s[1:] @ E.T
        X = np.hstack([z, a]); res = z1 - X @ np.linalg.lstsq(X, z1, rcond=None)[0]
        emp, th = (res**2).sum(1).mean(), K - J(U, At, Bt)
        alt = np.trace(U.T @ Qt @ U) + np.linalg.norm((np.eye(d) - U @ U.T) @ At.T @ U) ** 2
        print(f"loss: regression {emp:.4f}, K - J {th:.4f}, noise + leakage {alt:.4f}")
        assert abs(emp / th - 1) < 0.02 and abs(th - alt) < 1e-9
    # (2) gradient descent on E (not constrained) with a whitening penalty against max J
    Jmax, Ustar = maximize_J(At, Bt, K, rng)
    C = np.cov(s[:-1].T); C1 = s[1:].T @ s[:-1] / len(a); Ca = s[1:].T @ a / len(a)
    best = np.inf
    for trial in range(5):
        E = rng.standard_normal((K, d)) * 0.1; P = np.zeros((K, K)); R = np.zeros((K, m)); lam = 50.0
        import torch
        E, P, R = (torch.tensor(v, requires_grad=True) for v in (E, P, R))
        Ct, C1t, Cat, C0 = (torch.tensor(v) for v in (C, C1, Ca, np.cov(s[1:].T)))
        opt = torch.optim.Adam([E, P, R], lr=0.01)
        for it in range(6000):
            Szz = E @ Ct @ E.T
            pred = (torch.trace(E @ C0 @ E.T) - 2 * torch.trace(P @ E @ C1t.T @ E.T) - 2 * torch.trace(R @ Cat.T @ E.T)
                    + torch.trace(P @ Szz @ P.T) + torch.trace(R @ R.T))
            loss = pred + lam * ((Szz - torch.eye(K)) ** 2).sum()
            opt.zero_grad(); loss.backward(); opt.step()
        best = min(best, pred.item())
    print(f"gradient descent with whitening penalty: prediction loss {best:.4f}; K - max J = {K - Jmax:.4f}")
    assert abs(best - (K - Jmax)) < 0.03
    print("all checks passed")


if __name__ == "__main__":
    main()
