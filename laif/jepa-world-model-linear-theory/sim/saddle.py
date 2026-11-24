"""The squared action-covariance term has zero gradient at an action-blind latent; the unsquared term does not.

With C_h(U) = Cov(z_{t+h}, a_t) = U^T At^(h-1) Bt, a latent is action-blind when C_h(U) = 0 for h = 1..H.
Claims checked, in the world of action_blind.py (static modes plus scalar controllable modes):
  (1) at a static latent U0 (prediction loss 0, action-blind) the gradient of L_pred - mu * sum_h ||C_h||_F^2 on the
      manifold of orthonormal frames is zero for every mu, and the objective along a rotation of one column by eps
      towards mode i is eps^2 (q_i + (1 - alpha_i)^2 - mu w_i) + O(eps^4): the static latent is a strict saddle only when
      mu > (q_i + (1 - alpha_i)^2) / w_i, and for q_i / w_i < mu below that it is a local minimum that is not global;
  (2) with the unsquared term L_pred - mu * sum_h ||C_h||_F, one controllable mode (alpha, b^2, q), the objective along
      that rotation is f(s) = (q + c) s - c s^2 - mu S sqrt(s), s = sin^2 eps, c = (1 - alpha)^2, S = |b| sum_h |alpha|^(h-1),
      so for every mu > 0 the minimizer has s* > 0 (action response b^2 s* > 0); the minimum over orthonormal frames
      found by gradient descent equals min_s f(s).
"""
import numpy as np
import torch
from action_blind import build

torch.set_default_dtype(torch.float64)


def terms(U, At, Bt, H):
    M = U.T @ At @ U; G = U.T @ Bt; K = U.shape[1]
    pred = K - (M**2).sum() - (G**2).sum()
    C, X = [], Bt
    for _ in range(H): C.append(U.T @ X); X = At @ X
    return pred, sum((c**2).sum() for c in C), sum(((c**2).sum() + 1e-30).sqrt() for c in C)


def rotate(U0, e, eps):
    U = U0.clone(); U[:, -1] = np.cos(eps) * U0[:, -1] + np.sin(eps) * e; return U


def main():
    rng = np.random.default_rng(3)
    ks, K, sigma, H = 3, 3, 0.5, 4
    alphas, betas = np.array([0.9, 0.5]), [0.3, 1.0]
    At, Bt, Qt = (torch.tensor(v) for v in build(ks, alphas, betas, sigma))
    d = At.shape[0]
    b2 = np.array([Bt[ks + i, i].item() ** 2 for i in range(2)]); q = np.array([Qt[ks + i, ks + i].item() for i in range(2)])
    w = b2 * (1 - alphas ** (2 * H)) / (1 - alphas**2); mu_th = q / w
    U0 = torch.eye(d)[:, :K].clone()
    # (1) zero gradient for every mu, second variation 2 eps^2 (q_i - mu w_i)
    for mu in [0.1, 1.0, 10.0]:
        U = U0.clone().requires_grad_(True); p, sq, _ = terms(U, At, Bt, H); (p - mu * sq).backward()
        g = U.grad - U0 @ (U0.T @ U.grad + U.grad.T @ U0) / 2
        assert g.norm() < 1e-12, g.norm()
        for i in range(2):
            e = torch.eye(d)[:, ks + i]; eps = 1e-3
            p, sq, _ = terms(rotate(U0, e, eps), At, Bt, H)
            sec = (p - mu * sq).item() / eps**2
            exp = q[i] + (1 - alphas[i]) ** 2 - mu * w[i]; assert abs(sec - exp) < 1e-4, (sec, exp)
    mu = 0.5 * (mu_th[0] + (q[0] + (1 - alphas[0]) ** 2) / w[0])    # metastable range of mode 0, below mode 1's
    for _ in range(300):
        X = torch.tensor(rng.standard_normal((d, K))) * 1e-2; X[:ks] = 0
        p, sq, _ = terms(torch.linalg.qr(U0 + X)[0], At, Bt, H); assert (p - mu * sq).item() > 0
    Ufull = torch.eye(d)[:, [0, 1, ks]]; p, sq, _ = terms(Ufull, At, Bt, H); assert (p - mu * sq).item() < 0
    print(f"    mu = {mu:.4f}: 300 random perturbations of the static latent raise the objective, "
          f"while keeping mode 0 gives {(p - mu * sq).item():.4f} < 0")
    print(f"(1) gradient 0 at the static latent for mu in (0.1, 1, 10); curvature q_i + (1 - alpha_i)^2 - mu w_i; "
          f"global thresholds {mu_th.round(4)}, local thresholds {((q + (1 - alphas) ** 2) / w).round(4)}")
    # (2) unsquared term, one controllable mode
    al, be = 0.9, 0.3
    At, Bt, Qt = (torch.tensor(v) for v in build(ks, [al], [be], sigma)); d = At.shape[0]
    b2, qq = Bt[ks, 0].item() ** 2, Qt[ks, ks].item(); c = (1 - al) ** 2; S = np.sqrt(b2) * sum(al**h for h in range(H))
    U0 = torch.eye(d)[:, :K].clone(); e = torch.eye(d)[:, ks]
    for eps in [0.2, 0.7, 1.3]:
        p, _, un = terms(rotate(U0, e, eps), At, Bt, H); s = np.sin(eps) ** 2
        assert abs(p.item() - ((qq + c) * s - c * s * s)) < 1e-12 and abs(un.item() - np.sqrt(s) * S) < 1e-12
    ss = np.linspace(0, 1, 200001)
    for mu in [0.002, 0.01, 0.05, 0.5]:
        f = (qq + c) * ss - c * ss**2 - mu * S * np.sqrt(ss); fmin, sstar = f.min(), ss[f.argmin()]
        best = None
        for _ in range(8):
            Wp = torch.tensor(rng.standard_normal((d, K)), requires_grad=True); opt = torch.optim.Adam([Wp], lr=0.02)
            for _ in range(2500):
                U = torch.linalg.qr(Wp)[0]; p, _, un = terms(U, At, Bt, H); loss = p - mu * un
                opt.zero_grad(); loss.backward(); opt.step()
            U = torch.linalg.qr(Wp)[0].detach(); p, _, un = terms(U, At, Bt, H); val = (p - mu * un).item()
            if best is None or val < best[0]: best = (val, ((U.T @ Bt) ** 2).sum().item())
        print(f"(2) mu = {mu}: min f = {fmin:.6f} at s* = {sstar:.4f} (response {b2 * sstar:.5f}); "
              f"frames: {best[0]:.6f}, response {best[1]:.5f}")
        assert sstar > 0 and abs(best[0] - fmin) < 2e-5 and abs(best[1] - b2 * sstar) < 2e-3
    print("all checks passed")


if __name__ == "__main__":
    main()
