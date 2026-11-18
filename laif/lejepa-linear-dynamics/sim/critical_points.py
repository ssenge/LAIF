"""Critical points of linear LeJEPA in the commuting case (Theorem 8 and Corollary 9).

At a critical point, (delta_i sigma_j - delta_j sigma_i) <v_i, v_j> = 0 for v_i = W e_i, so features with distinct
costs c_i = delta_i / sigma_i map to orthogonal directions, M = W Sigma W^T has the eigenpairs (n_j, v_j) with
n_j = sigma_j |v_j|^2, tr(W Delta W^T) = sum c_j n_j, and every active feature is stationary for the reduced objective.
Also: the learned features are the cheapest ones, and for the uniform law their variances are ordered by the costs.
Checked at critical points found by a quasi-Newton method, for many directions (uniform law) and for 16 fixed slices.
"""
import numpy as np
from scipy.optimize import minimize
from slice_function import D, D1

if __name__ == "__main__":
    sigma = np.array([9.0, 1, 1, 1, 0.5, 0.5, 2.0])
    rho = np.array([0.6, 0.95, 0.9, 0.85, 0.97, 0.5, 0.7])
    K, d = 3, 7
    mu = 1.6 * K / abs(D1(0.0))
    c = 2 * (1 - rho)
    S, Dl = np.diag(sigma), np.diag(2 * sigma * (1 - rho))
    for n_dir, seed in [(20000, 0), (20000, 1), (16, 2), (16, 3)]:
        rng = np.random.default_rng(seed)
        A = rng.standard_normal((n_dir, K)); A /= np.linalg.norm(A, axis=1, keepdims=True)   # unit directions

        def fg(w):
            W = w.reshape(K, d); M = W @ S @ W.T
            s = np.einsum("nk,kl,nl->n", A, M, A)
            G = (A * D1(s)[:, None]).T @ A / n_dir
            return np.trace(W @ Dl @ W.T) + mu * D(s).mean(), (2 * W @ Dl + 2 * mu * G @ W @ S).ravel()
        r = minimize(fg, 0.3 * rng.standard_normal(K * d), jac=True, method="BFGS", options={"gtol": 1e-11, "maxiter": 20000})
        W = r.x.reshape(K, d)
        M = W @ S @ W.T
        s = np.einsum("nk,kl,nl->n", A, M, A)
        gn = np.abs(fg(r.x)[1]).max()
        V = W                                                    # columns v_i = W e_i (e_i the standard basis)
        n = sigma * (V ** 2).sum(0)
        act = n > 1e-6 * n.max()
        cos = [abs(V[:, i] @ V[:, j]) / np.sqrt(V[:, i] @ V[:, i] * (V[:, j] @ V[:, j]))
               for i in range(d) for j in range(i + 1, d) if act[i] and act[j]]
        eig = max(np.linalg.norm(M @ V[:, j] - n[j] * V[:, j]) / np.linalg.norm(V[:, j]) / n[j] for j in range(d) if act[j])
        stat = max(abs(c[j] + mu * np.mean(D1(s) * (A @ V[:, j]) ** 2) / (V[:, j] @ V[:, j])) for j in range(d) if act[j])
        inv = abs(np.trace(W @ Dl @ W.T) - (c * n).sum())
        print(f"{n_dir:5d} directions: |grad| {gn:.1e}, active {np.flatnonzero(act)}, n {n[act].round(4)}, "
              f"max cos {max(cos):.1e}, eigen residual {eig:.1e}, stationarity {stat:.1e}, trace identity {inv:.1e}")
        assert gn < 1e-6 and act.sum() <= K and max(cos) < 1e-5 and eig < 1e-5 and stat < 1e-5 and inv < 1e-10
        assert c[act].max() < c[~act].min()                       # the learned features are the cheapest ones
        if n_dir > 1000:                                           # uniform law: ordered by the costs
            o = np.argsort(c[act]); assert np.all(np.diff(n[act][o]) <= 1e-9)
    print("all checks passed")
