"""End-to-end run of the bounded-variance mean estimator of me_design.py on explicit distributions, with exactly
sampled measurement outcomes in every amplitude estimation (AE). Checks |mu_hat - mu| <= eps, the failure rate
against delta, and the number of calls to the code of y against the certified bound.

usage: me_sim.py eps delta alpha_last runs [seed]   (alpha_last: the AE parameter certified by ae_bound.py)"""
import sys, os
import numpy as np
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "ae"))
from ae_core import cp, HALF
from ae_bound import wtable, qround, NGRID
import me_design

def ae_interval(theta, eps, alpha_last, rng, r=2.0, kappa=1.0, gamma=1.0, rho=1.02):
    """The AE algorithm of ae_alg.py (amplitude-estimation-constants), returning the final angle interval and the
    number of calls to A or its inverse (2k + 1 per shot of Q^k A)."""
    stop = np.arcsin(2 * eps)
    g = [stop]
    while g[-1] < HALF: g.append(min(HALF, g[-1] * rho))
    l, u, calls = 0.0, HALF, 0
    while u - l > stop:
        w = u - l
        c = int(np.searchsorted(g, w)) - 1
        lo, hi = g[c], g[c + 1]
        a_c = qround(alpha_last * (stop / hi) ** gamma)
        tab = wtable(a_c)
        cap = max(1, int(kappa * HALF / w))
        K = next(K for K in range(cap if cap % 2 else cap - 1, 0, -2)
                 if np.floor(K * l / HALF) == np.floor(K * u / HALF) or K * u / HALF == np.floor(K * u / HALF))
        target = max(lo / r, stop * 0.999)
        N = NGRID[next(j for j, v in enumerate(tab) if v <= target * K)]
        h = rng.binomial(N, np.sin(K * theta) ** 2)
        calls += N * K
        plo, phi = cp(h, N, a_c)
        j = int(np.floor(K * l / HALF))
        f0, f1 = np.arcsin(np.sqrt(plo)), np.arcsin(np.sqrt(phi))
        a, b = ((j + 1) * HALF - f1, (j + 1) * HALF - f0) if j % 2 else (j * HALF + f0, j * HALF + f1)
        nl, nu = max(l, a / K), min(u, b / K)
        if nl > nu: nl, nu = max(0.0, a / K), min(HALF, b / K)
        l, u = nl, nu
    return l, u, calls

def run(vals, probs, D, k, g, alpha_last, rng):
    """Distribution of y: finite support vals with probs, variance <= 1. Returns (mu_hat, calls)."""
    r, rho, b, L, eta = D["r"], D["rho"], D["b"], D["L"], D["eta"]
    ys = rng.choice(vals, size=(k, g), p=probs)
    m0 = np.median(ys.mean(1)); calls = k * g
    x = vals - m0
    e_ae = np.sin(eta) / 2
    # band 1: W = (1 + x 1{|x| <= b} / b) / 2
    a = float(probs @ np.where(np.abs(x) <= b, (1 + x / b) / 2, 0.5))
    l, u, c = ae_interval(np.arcsin(np.sqrt(a)), e_ae, alpha_last, rng); calls += c
    est = 2 * b * ((np.sin(l) ** 2 + np.sin(u) ** 2) / 2 - 0.5)
    t = [b * rho ** (j - 1) for j in range(1, L + 1)]
    for j in range(1, L):
        for s in (1, -1):
            band = (s * x > t[j - 1]) & (s * x <= t[j])
            a = float(probs @ np.where(band, s * x / t[j], 0.0))
            l, u, c = ae_interval(np.arcsin(np.sqrt(a)), e_ae, alpha_last, rng); calls += c
            est += s * t[j] * (np.sin(l) ** 2 + np.sin(u) ** 2) / 2
    return m0 + est, calls

if __name__ == "__main__":
    eps, delta, alpha_last, runs = float(sys.argv[1]), float(sys.argv[2]), float(sys.argv[3]), int(sys.argv[4])
    rng = np.random.default_rng(int(sys.argv[5]) if len(sys.argv) > 5 else 1)
    c, D = me_design.design(eps, delta)
    _, k, g = me_design.centering(D["r"], delta / 10)
    b = D["b"]
    dists = {  # name: (vals, probs), each with variance 1
        "two-point": (np.array([-1.0, 1.0]), np.array([0.5, 0.5])),
        "spike just above b": (np.array([-1.01 * b, 0.0, 1.01 * b]), np.array([0.5, 0, 0.5]) / (1.01 * b) ** 2 + np.array([0, 1 - 1 / (1.01 * b) ** 2, 0])),
        "spike at 3T": None,
        "gaussian grid": None}
    T = b * D["rho"] ** (D["L"] - 1)
    z = 3 * T; dists["spike at 3T"] = (np.array([0.0, z]), np.array([1 - 1 / z ** 2, 1 / z ** 2]))
    gx = np.linspace(-8, 8, 4001); gp = np.exp(-gx ** 2 / 2); gp /= gp.sum(); dists["gaussian grid"] = (gx, gp)
    for name, (v, p) in dists.items():
        p = p / p.sum(); mu = float(p @ v); var = float(p @ (v - mu) ** 2); assert var <= 1 + 1e-9, (name, var)
        v = v + 3.7                                         # unknown offset
        errs, calls = [], []
        for _ in range(runs):
            m, q = run(v, p, D, k, g, alpha_last, rng); errs.append(abs(m - (mu + 3.7))); calls.append(q)
        errs = np.array(errs)
        print(f"{name}: var {var:.3f}, fail {np.mean(errs > eps):.4f}, max err/eps {errs.max() / eps:.3f}, "
              f"calls max {max(calls) * eps:.1f}/eps mean {np.mean(calls) * eps:.1f}/eps (design bound {c * eps:.1f}/eps with table cA)", flush=True)
