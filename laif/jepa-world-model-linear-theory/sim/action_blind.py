"""Action-blind optima of the prediction objective, and the weight of an inverse-dynamics term that removes them.

World in whitened coordinates: k_s static modes (At = 1, Bt = 0, Qt = 0, for example the content of a background that
is fixed within an episode) and a controllable block s' = A s + B (a + sigma e), e ~ N(0, I): actuator noise, so
Q = sigma^2 B B^T and range(B) lies in range(Q).
Claims checked:
  (1) with K <= k_s every minimizer of the prediction loss K - J(U) has loss 0 and action response G = U^T Bt = 0;
  (2) the inverse-dynamics loss is L_inv(U) = m - tr(G^T (I - M M^T)^{-1} G), M = U^T At U, checked against a regression;
  (3) for scalar controllable modes with (alpha_i, b_i^2, q_i), alpha_i^2 + b_i^2 + q_i = 1, a latent equal to a static
      mode plus eps times mode i has prediction loss O(eps^2) and explains the share b_i^2 / (b_i^2 + q_i + (1 - alpha_i)^2)
      of the action for every eps > 0, so the inverse-dynamics term is met with action response -> 0. The infimum of
      L_pred + lam L_inv keeps mode i at full scale exactly when
      lam > lam_i = q_i / (b_i^2 / (b_i^2 + q_i) - b_i^2 / (b_i^2 + q_i + (1 - alpha_i)^2)).
"""
import numpy as np
import torch
from scipy.linalg import solve_discrete_lyapunov, sqrtm

torch.set_default_dtype(torch.float64)


def build(ks, alphas, betas, sigma):
    """ks static modes, then scalar controllable modes s_i' = alpha_i s_i + beta_i (a_i + sigma e_i)."""
    kc = len(alphas); d = ks + kc
    At = np.eye(d); Bt = np.zeros((d, kc)); Qt = np.zeros((d, d))
    for i, (al, be) in enumerate(zip(alphas, betas)):
        var = be**2 * (1 + sigma**2) / (1 - al**2)
        At[ks + i, ks + i] = al; Bt[ks + i, i] = be / np.sqrt(var); Qt[ks + i, ks + i] = sigma**2 * be**2 / var
    assert np.allclose(At @ At.T + Bt @ Bt.T + Qt, np.eye(d))
    return At, Bt, Qt


def losses(U, At, Bt):
    M = U.T @ At @ U; G = U.T @ Bt; K = U.shape[1]
    pred = K - (M**2).sum() - (G**2).sum()
    inv = Bt.shape[1] - torch.trace(G.T @ torch.linalg.solve(torch.eye(K) - M @ M.T + 1e-9 * torch.eye(K), G))
    return pred, inv


def minimize(At, Bt, K, lam, rng, starts=12, iters=1500):
    At, Bt = torch.tensor(At), torch.tensor(Bt); best = None
    for _ in range(starts):
        W = torch.tensor(rng.standard_normal((At.shape[0], K)), requires_grad=True)
        opt = torch.optim.Adam([W], lr=0.03)
        for _ in range(iters):
            U = torch.linalg.qr(W)[0]; p, i = losses(U, At, Bt); loss = p + lam * i
            opt.zero_grad(); loss.backward(); opt.step()
        U = torch.linalg.qr(W)[0].detach(); p, i = losses(U, At, Bt)
        if best is None or (p + lam * i).item() < best[0]:
            best = ((p + lam * i).item(), p.item(), i.item(), ((U.T @ Bt) ** 2).sum().item())
    return best


def main():
    rng = np.random.default_rng(1)
    # (2) inverse-dynamics formula against a regression, generic world
    d, m, K = 6, 2, 3
    A = rng.standard_normal((d, d)); A *= 0.8 / max(abs(np.linalg.eigvals(A)))
    B = rng.standard_normal((d, m)); L = 0.4 * rng.standard_normal((d, d)); Q = L @ L.T
    Sig = solve_discrete_lyapunov(A, B @ B.T + Q); S = np.real(sqrtm(Sig)); Si = np.linalg.inv(S)
    T = 300000; s = np.zeros((T + 1, d)); a = rng.standard_normal((T, m)); Lq = np.linalg.cholesky(Q)
    s[0] = np.linalg.cholesky(Sig) @ rng.standard_normal(d)
    for t in range(T): s[t + 1] = A @ s[t] + B @ a[t] + Lq @ rng.standard_normal(d)
    U = np.linalg.qr(rng.standard_normal((d, K)))[0]; E = U.T @ Si
    X = np.hstack([s[:-1] @ E.T, s[1:] @ E.T]); res = a - X @ np.linalg.lstsq(X, a, rcond=None)[0]
    _, inv = losses(torch.tensor(U), torch.tensor(Si @ A @ S), torch.tensor(Si @ B))
    print(f"inverse-dynamics loss: regression {(res**2).sum(1).mean():.4f}, formula {inv.item():.4f}")
    assert abs((res**2).sum(1).mean() / inv.item() - 1) < 0.02
    # (1) and (3): static modes against noisy controllable modes
    ks, K, sigma = 3, 3, 0.5
    alphas, betas = [0.9, 0.5], [0.3, 1.0]
    At, Bt, Qt = build(ks, alphas, betas, sigma)
    b2 = np.array([Bt[ks + i, i] ** 2 for i in range(2)]); q = np.array([Qt[ks + i, ks + i] for i in range(2)])
    al = np.array(alphas)
    ride = b2 / (b2 + q + (1 - al) ** 2)      # action variance explained by an infinitesimal component on a static mode
    swap = b2 / (b2 + q)                      # explained when the mode is kept at full scale
    lam_th = q / (swap - ride)
    print(f"modes: b^2 = {b2.round(4)}, q = {q.round(4)}, explained riding {ride.round(4)} / kept {swap.round(4)}, "
          f"thresholds lam_i = {lam_th.round(4)}")
    tot, pred, inv, act = minimize(At, Bt, K, 0.0, rng)
    print(f"lam = 0: prediction loss {pred:.2e}, action response |G|^2 = {act:.2e}")
    assert pred < 1e-6 and act < 1e-6
    for lam in sorted(np.concatenate([[0.01], lam_th * 0.8, lam_th * 1.25])):
        tot, pred, inv, act = minimize(At, Bt, K, lam, rng)
        kept = (lam > lam_th); exp_tot = (q * kept).sum() + lam * (2 - np.where(kept, swap, ride).sum())
        print(f"lam = {lam:.4f}: total {tot:.5f} (predicted infimum {exp_tot:.5f}), prediction loss {pred:.5f}, "
              f"action response {act:.4f} (predicted {(b2 * kept).sum():.4f})")
        assert abs(tot - exp_tot) < 3e-4 and abs(act - (b2 * kept).sum()) < 2e-2
    print("all checks passed")


if __name__ == "__main__":
    main()
