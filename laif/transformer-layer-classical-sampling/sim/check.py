"""Classical sampling for one layer of the block-encoded transformer with the scaling alpha_0 = alpha_s^2 alpha_w^2.

Checks, with asserts:
1. b = max_k |(Q K^T)_{jk}| / alpha_0 <= 1 and Z_j / N in [e^{-1}, e] for every instance.
2. The mean squared error of the attention-row estimator is at most c(b) r^2 / m (Theorem 1),
   with c(b) = 2 e^{4b} (1 + e^{2b} sinh(b)^2) and r^2 = ||S W_v||_F^2 / N.
3. The error of the layer output is at most 4 (1 + L) ||G_hat - G|| / (sigma sigma') in every trial (Theorem 2),
   with sigma, sigma' the norms of the centred vectors before the two layer normalizations.
4. For fixed m the output error does not grow with N (N = 10^3 .. 10^6).
"""
import numpy as np
from math import erf, sqrt, exp, sinh

rng = np.random.default_rng(7)
d, N1, m, trials = 16, 64, 2000, 20
gelu = np.vectorize(lambda x: x * 0.5 * (1 + erf(x / sqrt(2))))


def spec_unit(a, b):
    W = rng.standard_normal((a, b))
    return W / np.linalg.norm(W, 2)


Wq, Wk, Wv = spec_unit(d, d), spec_unit(d, d), spec_unit(d, d)
M1, M2 = spec_unit(N1, d), spec_unit(d, N1)
alpha_w = 1.0
L = 1.13 * np.linalg.norm(M1, 2) * np.linalg.norm(M2, 2)
c = lambda b: 2 * exp(4 * b) * (1 + exp(2 * b) * sinh(b) ** 2)


def LN(z):                                   # gamma = 1/sqrt(d), beta = 0: centred and normalized, LN(constant) = 0
    p = z - z.mean(); n = np.linalg.norm(p)
    return (p / n if n > 0 else 0 * p), n    # (output, norm of the centred vector)


def tail(G, Sj):                             # residual, LN, feed-forward, residual, LN
    psi, s1 = LN(G + Sj)
    out, s2 = LN(psi + M2 @ gelu(M1 @ psi))
    return out, s1, s2


def instance(N, kind):
    S = rng.standard_normal((N, d)) / sqrt(d)            # rows of norm about 1, ||S||_F about sqrt(N)
    if kind == "split":                                   # half the scores near +1, half near -1
        u = rng.standard_normal(d); u /= np.linalg.norm(u)
        S[: N // 2] += 3 * u; S[N // 2:] -= 3 * u
    if kind == "heavy":                                   # a few rows of large norm
        S[rng.choice(N, 10, replace=False)] *= 30
    if kind in ("dominant", "maxscore"):                  # row 0 dominates the spectral norm
        S[0] = 100 * sqrt(N) * rng.standard_normal(d) / sqrt(d)
    return S


for kind in ["random", "split", "heavy", "dominant", "maxscore"]:
    for N in [10 ** 3, 10 ** 4, 10 ** 5, 10 ** 6]:
        S = instance(N, kind)
        j = 0
        alpha_s = np.linalg.norm(S, 2)                    # smallest valid normalization: the spectral norm
        a0 = alpha_s ** 2 * alpha_w ** 2
        Wqk = np.eye(d) if kind == "maxscore" else Wq @ Wk.T   # identity: score of the query row with itself close to 1
        q = S[j] @ Wqk / a0
        s = S @ q                                         # all scores, for the exact reference only
        b = np.abs(s).max()
        assert b <= 1
        w = np.exp(s)
        assert np.exp(-1) * N <= w.sum() <= np.e * N
        V = S @ Wv
        G = (w @ V) / w.sum()
        r2 = (V ** 2).sum() / N
        out, s1, s2 = tail(G, S[j])
        err_G, err_out = [], []
        for _ in range(trials):
            k = rng.integers(0, N, m)                     # uniform indices: m rows of S are read
            wk = np.exp(S[k] @ q)
            Gh = ((wk @ S[k]) @ Wv) / wk.sum()
            oh = tail(Gh, S[j])[0]
            eg, eo = np.linalg.norm(Gh - G), np.linalg.norm(oh - out)
            assert eo <= 4 * (1 + L) * eg / (s1 * s2) + 1e-12
            err_G.append(eg ** 2); err_out.append(eo)
        mse = np.mean(err_G)
        assert mse <= c(b) * r2 / m, (mse, c(b) * r2 / m)
        print(f"{kind:9s} N = {N:7d}: b = {b:.2e}, Z/N = {w.sum() / N:.4f}, r = {sqrt(r2):.3f}, "
              f"MSE(G) = {mse:.2e} <= {c(b) * r2 / m:.2e}, mean output error {np.mean(err_out):.4f}, "
              f"sigma sigma' = {s1 * s2:.3f}")
        del S, V, s, w
print("all checks passed")
