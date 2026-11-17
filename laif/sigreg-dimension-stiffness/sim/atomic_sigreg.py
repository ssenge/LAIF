"""Population SIGReg of laws on the sphere of radius sqrt(K): the uniform law, the cross-polytope (2K atoms
+-sqrt(K) e_i) and unions of r random orthonormal bases (2rK atoms).

For x, x' on the sphere with rho = <x, x'>/K, a slice difference a^T(x - x') has the law of |x - x'| a_1, so
  SIGReg(P) = sqrt(2 pi) E_{x,x'} h(K (1 - rho)) - 2 sqrt(pi) h(K/4) + sqrt(2 pi / 3),
with h(s) = E exp(-s a_1^2) = 1F1(1/2; K/2; -s) (a_1^2 ~ Beta(1/2, (K-1)/2)), weight e^{-t^2/2}, integral over R.
"""
import numpy as np, mpmath as mp
from scipy.integrate import quad

def h(K, s):
    return float(mp.hyp1f1(0.5, K / 2, -s))

def const(K):
    return -2 * np.sqrt(np.pi) * h(K, K / 4) + np.sqrt(2 * np.pi / 3)

def sigreg_pairs(K, rhos, weights):
    """SIGReg for a law on the sphere, given the law of rho over independent pairs (atoms and weights)."""
    return np.sqrt(2 * np.pi) * sum(w * h(K, K * (1 - r)) for r, w in zip(rhos, weights)) + const(K)

def sigreg_uniform(K):
    """rho of two independent uniform points has density prop. to (1 - r^2)^((K-3)/2)."""
    if K == 2:
        dens = lambda r: 1 / (np.pi * np.sqrt(1 - r * r))
    else:
        c = float(mp.gamma(K / 2) / (mp.sqrt(mp.pi) * mp.gamma((K - 1) / 2)))
        dens = lambda r: c * (1 - r * r) ** ((K - 3) / 2)
    f = lambda r: h(K, K * (1 - r)) * dens(r)
    val = sum(quad(f, a, b, limit=200)[0] for a, b in [(-1, -0.5), (-0.5, 0), (0, 0.5), (0.5, 1)])
    return np.sqrt(2 * np.pi) * val + const(K)

def sigreg_crosspolytope(K):
    return sigreg_pairs(K, [1.0, -1.0, 0.0], [1 / (2 * K), 1 / (2 * K), 1 - 1 / K])

def sigreg_bases(K, r, rng):
    """Uniform law on +-sqrt(K) b over the vectors b of r random orthonormal bases (2rK atoms)."""
    B = np.concatenate([np.linalg.qr(rng.standard_normal((K, K)))[0] for _ in range(r)], axis=1)
    G = B.T @ B                                           # inner products of unit atoms, both signs give +-G
    vals = np.concatenate([G.ravel(), -G.ravel()])
    hist, edges = np.histogram(vals, bins=4001, range=(-1 - 1e-9, 1 + 1e-9))
    centres = (edges[:-1] + edges[1:]) / 2
    keep = hist > 0
    return sigreg_pairs(K, centres[keep], hist[keep] / hist.sum())

def mc_check(K, atoms, M=200000, seed=0):
    """Monte Carlo over directions with the closed form of the t-integral, for a small atomic law."""
    rng = np.random.default_rng(seed)
    a = rng.standard_normal((M, K)); a /= np.linalg.norm(a, axis=1, keepdims=True)
    s = a @ atoms.T                                       # slices of the atoms, equal weights
    d = s[:, :, None] - s[:, None, :]
    pp = np.sqrt(2 * np.pi) * np.exp(-d ** 2 / 2).mean(axis=(1, 2))
    pg = np.sqrt(np.pi) * np.exp(-s ** 2 / 4).mean(axis=1)
    v = pp - 2 * pg
    return v.mean() + np.sqrt(2 * np.pi / 3), v.std() / np.sqrt(M)

if __name__ == "__main__":
    K = 4
    cp = np.concatenate([np.sqrt(K) * np.eye(K), -np.sqrt(K) * np.eye(K)])
    (mc, se), ex = mc_check(K, cp), sigreg_crosspolytope(K)
    print(f"K = 4 cross-polytope: Monte Carlo {mc:.5f} +- {se:.5f}, closed form {ex:.5f}")
    assert abs(mc - ex) < 4 * se
    rng = np.random.default_rng(1)
    print(f"{'K':>5} {'uniform':>11} {'K^2 unif':>9} {'cross-pol.':>11} {'K cross':>8} {'2 bases':>10} {'K 2bases':>9}")
    for K in [8, 16, 32, 64, 128, 256, 512, 1024]:
        u, c, b = sigreg_uniform(K), sigreg_crosspolytope(K), sigreg_bases(K, 2, rng)
        print(f"{K:>5} {u:11.3e} {K * K * u:9.4f} {c:11.3e} {K * c:8.4f} {b:10.3e} {K * b:9.4f}")
        assert 0 <= u < c and c < 3 / K
