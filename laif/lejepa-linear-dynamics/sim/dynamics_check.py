"""Gradient descent on linear LeJEPA, L(W) = tr(W Delta W^T) + mu E_a D(a^T W Sigma W^T a), W in R^{K x d}.

Features i = 0..d-1 with variance sigma_i and regression coefficient rho_i between the two views, so that
Delta = E (x - x')(x - x')^T = diag(2 sigma (1 - rho)) and the whitened invariance cost is c_i = 2 (1 - rho_i).
kappa = mu |D'(0)| / K. Early phase: rate of feature i is 4 sigma_i (kappa - c_i) (variance weighted).
Minimizer: ordered by c_i alone (Theorem 2 of the stiffness note).
"""
import numpy as np
from slice_function import D1

def run(sigma, rho, K, mu, steps, lr, seed=0, n_dir=20000, init=1e-4, S=None, Dl=None, every=50):
    rng = np.random.default_rng(seed)
    d = len(sigma)
    Q = np.eye(d)
    if S is None:
        S, Dl = np.diag(sigma), np.diag(2 * sigma * (1 - rho))
    A = rng.standard_normal((n_dir, K)); A /= np.linalg.norm(A, axis=1, keepdims=True)
    ev, U = np.linalg.eigh(A.T @ A / n_dir)                               # whiten: E a a^T = I/K exactly
    A = A @ (U / np.sqrt(ev)) @ U.T / np.sqrt(K)
    W = init * rng.standard_normal((K, d))
    hist = []
    for t in range(steps):
        M = W @ S @ W.T
        s = np.einsum("nk,kl,nl->n", A, M, A)
        G = (A * D1(s)[:, None]).T @ A / n_dir
        W -= lr * (2 * W @ Dl + 2 * mu * G @ W @ S)
        if t % every == 0:
            hist.append((t, (W ** 2).sum(0) * sigma, W.copy()))            # learned variance of each feature
    return (np.array([h[0] for h in hist]), np.array([h[1] for h in hist]), [h[2] for h in hist])

def subspace_overlap(W, U):
    """Squared cosines between the row space of W and the span of the orthonormal columns U, averaged."""
    Qw = np.linalg.qr(W.T)[0]
    return np.linalg.norm(U.T @ Qw) ** 2 / Qw.shape[1]

if __name__ == "__main__":
    sigma = np.array([9.0, 1, 1, 1, 0.5, 0.5])
    rho = np.array([0.6, 0.95, 0.9, 0.85, 0.97, 0.5])
    K = 3
    mu = K / abs(D1(0.0))                                                 # kappa = 1
    kappa = mu * abs(D1(0.0)) / K
    c = 2 * (1 - rho)
    rate = 4 * sigma * (kappa - c)
    lr = 2e-3
    print("c =", c.round(3), " early rates 4 sigma (kappa - c) =", rate.round(3))
    t, m, Ws = run(sigma, rho, K, mu, steps=40000, lr=lr, every=10)
    for k in [0, 100, 200, 300, 500, 1000, 2000, len(t) - 1]:
        print(f"step {t[k]:6d}", m[k].round(4))
    peak = m[:, 0].argmax()
    print("feature 0 peaks at step", t[peak], "with", m[peak, 0].round(4), "final", m[-1, 0].round(5))
    # Theorem 1: log n_i(t) - log n_i(0) <= rate_i * time, for all t (exact for whitened directions)
    T = lr * t
    with np.errstate(divide="ignore"):
        lg = np.log(m / m[0])
    assert np.all(lg <= rate * T[:, None] + 1e-9), "Theorem 1"
    # Theorem 2: while tr M <= eps, growth at least rate_i - 4 sigma_i eta, eta = 3 mu L2 eps / (K (K+2));
    # 1 % slack for the fourth moments of the sampled directions and the time step
    from slice_function import L as L2
    early = m.sum(1) <= 0.05
    eps = m[early].sum(1).max()
    eta = 3 * mu * L2 * eps / (K * (K + 2))
    low = (rate - 4 * sigma * eta)[None, :] * T[early, None]
    assert np.all(lg[early] >= low - 0.01 * np.abs(rate) * T[early, None] - 1e-9), "Theorem 2"
    print(f"Theorems 1 and 2 hold along the trajectory (early phase: tr M <= {eps:.3f}, eta = {eta:.4f})")
    # Corollary 3: the noisy feature leads early, the predictable feature 4 dominates at the end
    k_early = np.argmax(m.sum(1) > 0.01)
    assert lg[k_early, 0] > lg[k_early, 4] and m[-1, 4] > m[-1, 0] and m[-1, 0] < 1e-3 * m[peak, 0]
    # final spectrum ordered by c among the active features
    act = np.where(m[-1] > 1e-3)[0]
    assert list(act[np.argsort(c[act])]) == list(act[np.argsort(-m[-1, act])])
    print("variance first, predictability last: confirmed")

    # Non-commuting Sigma and Delta: the early row space follows the top eigenvectors of kappa Sigma - Delta,
    # the final one the bottom generalized eigenvectors of (Delta, Sigma).
    rng = np.random.default_rng(3)
    d, K = 8, 2
    Q1 = np.linalg.qr(rng.standard_normal((d, d)))[0]; Q2 = np.linalg.qr(rng.standard_normal((d, d)))[0]
    S = Q1 @ np.diag([6, 3, 1, 1, 1, 0.5, 0.5, 0.3]) @ Q1.T
    Dl = Q2 @ np.diag([0.1, 0.2, 0.4, 0.8, 1.5, 2, 3, 4]) @ Q2.T
    mu = K / abs(D1(0.0)) * 0.6
    kappa = mu * abs(D1(0.0)) / K
    ev, U = np.linalg.eigh(kappa * S - Dl)
    U_early = U[:, -K:]
    from scipy.linalg import eigh as geigh
    gv, Ug = geigh(Dl, S)                                                 # Delta u = gamma Sigma u, ascending
    U_final = np.linalg.qr(Ug[:, :K])[0]                                  # minimizer rows span the u_j
    t2, m2, Ws2 = run(np.ones(d), np.zeros(d), K, mu, steps=60000, lr=1e-3, S=S, Dl=Dl, every=100, seed=1)
    tr = np.array([np.trace(W @ S @ W.T) for W in Ws2])
    k1 = np.argmax(tr > 1e-3)
    o_early_A, o_early_G = subspace_overlap(Ws2[k1], U_early), subspace_overlap(Ws2[k1], U_final)
    o_end_A, o_end_G = subspace_overlap(Ws2[-1], U_early), subspace_overlap(Ws2[-1], U_final)
    print(f"non-commuting: early overlap with top eig(kappa S - Delta) {o_early_A:.3f}, with final basis {o_early_G:.3f}")
    print(f"               final overlap with top eig(kappa S - Delta) {o_end_A:.3f}, with final basis {o_end_G:.3f}")
    assert o_early_A > 0.95 and o_end_G > 0.95 and o_early_G < o_early_A and o_end_A < o_end_G
    # condition (a) of Lemma 2 for D and for the minibatch slice function N D + B, N >= 2
    from slice_function import D1, B
    xs = np.concatenate([np.linspace(0, 10, 100001), np.geomspace(10, 1e6, 10001)])
    B1 = lambda s: np.sqrt(2 * np.pi) * (2 * s + 1) ** -1.5
    assert np.all(D1(xs) >= D1(0.0) - 1e-15)
    for N in [2, 4, 64, 256]:
        g = N * D1(xs) + B1(xs)
        assert np.all(g >= g[0] - 1e-12), N
    print("all checks passed")
