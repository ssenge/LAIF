"""Asymptotic exponent per input qubit of the compressing memory: max over kappa of theta(kappa)/kappa.
theta = min cost (per copy, nats) of a path of error fractions from the typical state to a fraction >= 1/2."""
import sys
import numpy as np
from scipy.optimize import brentq


def D(a, p):
    a = np.clip(a, 1e-300, 1 - 1e-16)
    return a * np.log(a / p) + (1 - a) * np.log((1 - a) / (1 - p))


def h2(t):
    t = np.clip(t, 1e-300, 1 - 1e-16)
    return -(t * np.log2(t) + (1 - t) * np.log2(1 - t))


def h2inv(v):
    return 0.0 if v <= 0 else brentq(lambda t: h2(t) - v, 1e-300, 0.5)


def I(s, t, p, nx=400):
    """rate of reaching fraction t after noise from fraction s: remove x of the s errors, add y on the 1 - s correct copies."""
    x = np.linspace(0, s, nx) if s > 0 else np.zeros(1)
    y = t - s + x
    ok = (y >= 0) & (y <= 1 - s)
    if not ok.any(): return np.inf
    x, y = x[ok], y[ok]
    c = (s * D(x / s, p) if s > 0 else 0) + (1 - s) * D(y / (1 - s), p)
    return float(np.min(c))


def theta(kappa, p, N=161):
    S = np.linspace(0, 0.5, N)
    f = np.array([h2inv(h2(t) - kappa) for t in S])
    C = np.array([[I(s, t, p) for t in S] for s in S])  # C[i, j] = cost from S[i] to S[j]
    fi = np.searchsorted(S, f)  # round the compressed fraction up to the grid: conservative
    fi = np.minimum(fi, N - 1)
    fail = C[:, -1]  # reaching 1/2
    V = fail.copy()
    for _ in range(400):
        Vn = np.minimum(fail, np.min(C[:, :-1] + V[fi[:-1]][None, :], axis=1))
        if np.allclose(Vn, V, rtol=0, atol=1e-12): break
        V = Vn
    s = 0.0  # typical state: iterate the noiseless-mean map
    for _ in range(2000):
        s = h2inv(h2(s + p * (1 - 2 * s)) - kappa)
    i0 = min(np.searchsorted(S, s), N - 1)
    return V[i0], s


if __name__ == "__main__":
    q = float(sys.argv[1]); p = (1 - q) / 2
    alpha = 0.5 * np.log(1 / (1 - q * q))
    print(f"q={q} p={p:.3f} alpha_q={alpha:.4f} h2(p)={h2(p):.4f}", flush=True)
    best = (0, None)
    for kappa in [1.0, 0.3, 0.1, 0.03, 0.01]:
        th, s = theta(kappa, p, N=321)
        print(f"  kappa={kappa}: typical fraction {s:.4f}, theta={th:.4f}, per input qubit {th / kappa:.4f}", flush=True)
        best = max(best, (th / kappa, kappa))
    print("best", best)
