"""The action-covariance term: sum over h = 1..H of ||Cov(z_{t+h}, a_t)||_F^2 for a whitened latent z = U^T Sigma^{-1/2} s.

Claims checked:
  (1) the term equals tr(U^T Wt_H U) with Wt_H = sum_{h<H} At^h Bt Bt^T (At^h)^T = Sigma^{-1/2} W_H Sigma^{-1/2}, the
      H-step controllability matrix in whitened coordinates, 0 <= Wt_H <= I (simulated data);
  (2) its maximum over orthonormal U is the sum of the K largest eigenvalues of Wt_H;
  (3) static modes against noisy controllable scalar modes (the world of action_blind.py): the minimizer of
      L_pred - mu * term keeps mode i at full scale exactly when mu > q_i / w_i, w_i = b_i^2 (1 - alpha_i^(2H)) / (1 - alpha_i^2),
      and a latent that carries mode i with weight eps gains only eps^2 w_i.
"""
import numpy as np
import torch
from scipy.linalg import solve_discrete_lyapunov, sqrtm
from action_blind import build

torch.set_default_dtype(torch.float64)


def gram(At, Bt, H):
    W = np.zeros_like(At); X = Bt.copy()
    for _ in range(H): W += X @ X.T; X = At @ X
    return W


def minimize(At, Bt, Wt, K, mu, rng, starts=10, iters=1500):
    At, Bt, Wt = (torch.tensor(v) for v in (At, Bt, Wt)); best = None
    for _ in range(starts):
        Wp = torch.tensor(rng.standard_normal((At.shape[0], K)), requires_grad=True)
        opt = torch.optim.Adam([Wp], lr=0.03)
        for _ in range(iters):
            U = torch.linalg.qr(Wp)[0]; M = U.T @ At @ U; G = U.T @ Bt
            loss = K - (M**2).sum() - (G**2).sum() - mu * torch.trace(U.T @ Wt @ U)
            opt.zero_grad(); loss.backward(); opt.step()
        U = torch.linalg.qr(Wp)[0].detach()
        val = (K - ((U.T @ At @ U) ** 2).sum() - ((U.T @ Bt) ** 2).sum() - mu * torch.trace(U.T @ Wt @ U)).item()
        if best is None or val < best[0]: best = (val, ((U.T @ Bt) ** 2).sum().item())
    return best


def main():
    rng = np.random.default_rng(2)
    d, m, K, H = 6, 2, 3, 4
    A = rng.standard_normal((d, d)); A *= 0.85 / max(abs(np.linalg.eigvals(A)))
    B = rng.standard_normal((d, m)); L = 0.5 * rng.standard_normal((d, d)); Q = L @ L.T
    Sig = solve_discrete_lyapunov(A, B @ B.T + Q); S = np.real(sqrtm(Sig)); Si = np.linalg.inv(S)
    At, Bt = Si @ A @ S, Si @ B; Wt = gram(At, Bt, H)
    ev = np.linalg.eigvalsh(Wt); assert ev.min() > -1e-12 and ev.max() < 1 + 1e-12
    T = 400000; s = np.zeros((T + 1, d)); a = rng.standard_normal((T, m)); Lq = np.linalg.cholesky(Q)
    s[0] = np.linalg.cholesky(Sig) @ rng.standard_normal(d)
    for t in range(T): s[t + 1] = A @ s[t] + B @ a[t] + Lq @ rng.standard_normal(d)
    U = np.linalg.qr(rng.standard_normal((d, K)))[0]; z = s @ (U.T @ Si).T
    emp = sum(np.linalg.norm(z[h:T + 1].T @ a[: T + 1 - h] / (T + 1 - h)) ** 2 for h in range(1, H + 1))
    print(f"(1) term from data {emp:.4f}, tr(U^T Wt_H U) = {np.trace(U.T @ Wt @ U):.4f}")
    assert abs(emp / np.trace(U.T @ Wt @ U) - 1) < 0.03
    val, _ = minimize(0 * At, 0 * Bt, Wt, K, 1.0, rng, starts=4)     # only the term: K - 0 - 0 - tr
    print(f"(2) max of the term {K - val:.6f}, sum of the top {K} eigenvalues {ev[-K:].sum():.6f}")
    assert abs(K - val - ev[-K:].sum()) < 1e-5
    ks, K, sigma, H = 3, 3, 0.5, 4
    alphas, betas = np.array([0.9, 0.5]), [0.3, 1.0]
    At, Bt, Qt = build(ks, alphas, betas, sigma); Wt = gram(At, Bt, H)
    b2 = np.array([Bt[ks + i, i] ** 2 for i in range(2)]); q = np.array([Qt[ks + i, ks + i] for i in range(2)])
    w = b2 * (1 - alphas ** (2 * H)) / (1 - alphas**2); mu_th = q / w
    assert np.allclose(np.diag(Wt)[ks:], w)
    print(f"(3) w = {w.round(4)}, q = {q.round(4)}, thresholds mu_i = {mu_th.round(4)}")
    for mu in sorted(np.concatenate([mu_th * 0.8, mu_th * 1.25])):
        val, act = minimize(At, Bt, Wt, K, mu, rng)
        kept = mu > mu_th; exp = ((q - mu * w) * kept).sum()
        print(f"    mu = {mu:.4f}: value {val:.5f} (predicted {exp:.5f}), action response {act:.4f} "
              f"(predicted {(b2 * kept).sum():.4f})")
        assert abs(val - exp) < 1e-4 and abs(act - (b2 * kept).sum()) < 1e-2
    print("all checks passed")


if __name__ == "__main__":
    main()
