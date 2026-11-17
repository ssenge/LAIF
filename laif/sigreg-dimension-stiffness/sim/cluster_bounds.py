"""Checks of the cluster theorems for finite laws on the sphere of radius sqrt(K), rho = <x, x'>/K.

1. Isotropy of the cross-polytope and of unions of random orthonormal bases (signed): sum p_j p_k rho = 0 and
   sum p_j p_k rho^2 = 1/K.
2. SIGReg profile H(rho) = E exp(-K (1 - rho) u), u ~ Beta(1/2, (K-1)/2): |energy - (b0 + b2/K)| <= 1/K.
3. Uniformity profile exp(-2t (1 - rho)): log energy of an isotropic law exceeds log e^{-2t}(1 + 2t^2/K) by at most
   (e^{2t} - 1 - 2t - 2t^2)/K, while a law with m atoms has log energy >= -log m and the uniform law has
   log energy <= -2t + 2t^2/K (moment generating function of a sphere coordinate, checked here).
"""
import numpy as np, mpmath as mp
import math
from scipy.special import roots_jacobi

def iso_laws(K, rng):
    E = np.eye(K)
    cross = np.sqrt(K) * np.concatenate([E, -E])
    B = np.concatenate([np.linalg.qr(rng.standard_normal((K, K)))[0] for _ in range(2)], axis=1).T
    bases = np.sqrt(K) * np.concatenate([B, -B])
    return {"cross-polytope": cross, "2 signed bases": bases}

def rho_matrix(X):
    return X @ X.T / X.shape[1]

def sig_profile(K, nodes=120):
    """H(rho) = E exp(-K (1 - rho) u) and b_n = E e^{-Ku} (Ku)^n / n! for u ~ Beta(1/2, (K-1)/2), by
    Gauss-Jacobi quadrature in u = (1 + x)/2; H is checked against the confluent hypergeometric form."""
    x, w = roots_jacobi(nodes, (K - 3) / 2, -0.5)
    u, w = (1 + x) / 2, w / w.sum()
    H = lambda r: np.exp(-K * (1 - np.asarray(r))[..., None] * u) @ w
    for r in [-1, -0.3, 0, 0.5, 1]:
        assert abs(H(r) - float(mp.hyp1f1(0.5, K / 2, -K * (1 - r)))) < 1e-10
    b = [float((np.exp(-K * u) * (K * u) ** n / math.factorial(n)) @ w) for n in range(3)]
    return H, b

def mgf_sphere(K, lam):
    """E exp(lam a_1) for a uniform on the unit sphere of R^K: 0F1(; K/2; lam^2/4)."""
    return float(mp.hyp0f1(K / 2, lam * lam / 4))

if __name__ == "__main__":
    rng = np.random.default_rng(0)
    for K in [8, 32, 128, 256]:
        H, b = sig_profile(K)
        assert sum(b) <= 1 and min(b) >= 0
        for name, X in iso_laws(K, rng).items():
            R = rho_matrix(X); w = 1 / len(X)
            assert abs(R.sum() * w * w) < 1e-9 and abs((R ** 2).sum() * w * w - 1 / K) < 1e-9, name
            Hv = H(R)
            e = Hv.sum() * w * w
            dev = abs(e - (b[0] + b[2] / K))
            print(f"K={K:4d} {name:15s} SIGReg energy {e:.6f}, |e - (b0 + b2/K)| * K = {dev * K:.4f} (<= 1)")
            assert dev <= 1 / K
            for t in [1, 2, 4]:
                eu = np.exp(-2 * t * (1 - R)).sum() * w * w
                gap = np.log(eu) - np.log(np.exp(-2 * t) * (1 + 2 * t * t / K))
                bound = (np.exp(2 * t) - 1 - 2 * t - 2 * t * t) / K
                assert -1e-12 <= gap <= bound + 1e-12 and np.log(eu) >= -np.log(len(X)) - 1e-12
        for t in [1, 2, 4, 8, K / 4]:
            assert mgf_sphere(K, 2 * t) <= np.exp(2 * t * t / K) * (1 + 1e-12)
    print("separation margin 2t - 2t^2/K - log m of the uniformity term, K = 1024:")
    K = 1024
    for t in [2, 4, 16, K / 4]:
        row = "  ".join(f"m={m}: {2 * t - 2 * t * t / K - np.log(m):7.2f}" for m in [10, 2 * K, 10 ** 5])
        print(f"  t={t:6.1f}  blind bound {(np.exp(2 * t) - 1 - 2 * t - 2 * t * t) / K:9.3g}  {row}")
    print("all checks passed")
