"""CVA of the single-asset instance of arXiv:2105.12087 (Table I): a European call on geometric Brownian motion,
S0 = 5, K = 5.5, sigma = 0.25, drift mu = 0.02, maturity T = 184/360, recovery 0.415, M = 2^m exposure dates t_i = i T / M.
CVA = (1 - R) sum_i p(t_i) q(t_i) E(t_i) with E(t) = E[max(S_t - K exp(-r (T - t)), 0)], which is a Black-type formula:
E(t) = F N(d1) - K' N(d2), F = S0 exp(mu t), K' = K exp(-r (T - t)), d1,2 = (ln(F / K') +- sigma^2 t / 2) / (sigma sqrt t).
Not tabulated in the source: the EONIA curve (flat r here) and the bootstrapped hazards (flat lambda from the 1y CDS
quote by the credit triangle lambda = s / (1 - R_CDS)). Both enter only through p and q, never through E(t)."""
import numpy as np
from scipy.stats import norm

S0, K, SIG, MU, T, R = 5.0, 5.5, 0.25, 0.02, 184 / 360, 0.415
LAM = 0.00093772 / (1 - 0.4125)

def exposure(t, r):
    F, Kp = S0 * np.exp(MU * t), K * np.exp(-r * (T - t)); s = SIG * np.sqrt(t)
    d1 = (np.log(F / Kp) + s * s / 2) / s
    return F * norm.cdf(d1) - Kp * norm.cdf(d1 - s)

def cva(m=2, r=-0.0045, lam=LAM, E=exposure):
    M = 2 ** m; t = np.arange(1, M + 1) * T / M; tp = t - T / M
    q = np.exp(-lam * tp) - np.exp(-lam * t); p = np.exp(-r * t)
    return (1 - R) * np.sum(p * q * E(t, r))

def mc_exposure(t, r, n=4_000_000, seed=0):
    z = np.random.default_rng(seed).standard_normal(n)
    out = []
    for ti in np.atleast_1d(t):
        S = S0 * np.exp((MU - SIG ** 2 / 2) * ti + SIG * np.sqrt(ti) * z)
        out.append(np.maximum(S - K * np.exp(-r * (T - ti)), 0).mean())
    return np.array(out)

if __name__ == "__main__":
    c = cva(); cm = cva(E=mc_exposure)
    print(f"closed form CVA = {c:.6e}; Monte Carlo (4e6 paths per date) {cm:.6e}; relative difference {abs(cm / c - 1):.1e}")
    assert abs(cm / c - 1) < 3e-3
    for r in (-0.006, -0.0045, -0.003):
        for lam in (0.9 * LAM, LAM, 1.1 * LAM):
            print(f"  r = {r:+.4f}, lambda = {lam:.6f}: CVA = {cva(r=r, lam=lam):.6e}")
    print("reference value of the source (Monte Carlo, 1e5 paths): 5.599e-5 +- 0.002e-5")
    assert abs(c / 5.599e-5 - 1) < 0.05
