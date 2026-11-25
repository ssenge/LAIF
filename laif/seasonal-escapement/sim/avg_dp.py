"""Long-run average yield in Y_{t+1} = F(S_t, xi_{t+1}), escapement S_t in [max(0, Y_t - Q), Y_t].
Relative value iteration on a grid; checks whether the optimal policy is (capped) constant escapement.
"""
import numpy as np

def gh_lognormal(sig, k=31):
    z, w = np.polynomial.hermite_e.hermegauss(k)
    return np.exp(sig * z - sig**2 / 2), w / w.sum()

def bh(R):   return lambda S, xi: xi * R * S / (1 + (R - 1) * S)
def ricker(r): return lambda S, xi: xi * S * np.exp(r * (1 - S))

def grid(B=4.0, N=1601, lo=1e-5):
    """0 plus a log-spaced grid: resolves small populations, where tiny thresholds live."""
    return np.concatenate([[0.0], np.geomspace(lo, B, N - 1)])

def first_feasible(y, Q):
    """Index of the smallest grid escapement >= y - Q (the cap as the grid sees it)."""
    return np.zeros(len(y), int) if not np.isfinite(Q) else np.searchsorted(y, np.maximum(y - Q, 0) - 1e-12)

def range_argmax(phi, lo):
    """argmax of phi over [lo[i], i] for every i (sparse table)."""
    N = len(phi); idx = [np.arange(N)]; k = 1
    while 2 * k <= N:
        a = idx[-1]; b = np.concatenate([a[k:], a[-k:]])[:N]
        idx.append(np.where(phi[b] > phi[a], b, a)); k *= 2
    n = np.arange(N) - lo + 1; lev = np.floor(np.log2(n)).astype(int)
    c1 = np.array([idx[l][s] for l, s in zip(lev, lo)])
    c2 = np.array([idx[l][s] for l, s in zip(lev, np.arange(N) - (1 << lev) + 1)])
    return np.where(phi[c2] > phi[c1], c2, c1)

def solve(F, sig, Q=np.inf, B=4.0, N=1601, iters=2000):
    y = grid(B, N); xi, wq = gh_lognormal(sig)
    Fy = np.minimum(F(y[:, None], xi[None, :]), B)          # next state for escapement S = y[i]
    lo = first_feasible(y, Q); v = y.copy(); ref = np.searchsorted(y, 0.5)
    capped = np.isfinite(Q)
    if capped:                                               # escapement exactly y - Q (off the grid)
        Sq = np.maximum(y - Q, 0); Fq = np.minimum(F(Sq[:, None], xi[None, :]), B)
    for _ in range(iters):
        phi = -y + (np.interp(Fy, y, v) * wq).sum(1)        # phi(S) = -S + E v(F(S, xi))
        arg = range_argmax(phi, lo); best = phi[arg]; S = y[arg]
        if capped:
            pq = -Sq + (np.interp(Fq, y, v) * wq).sum(1)
            use = pq >= best; best = np.where(use, pq, best); S = np.where(use, Sq, S)
        vn = y + best; g = vn[ref] - v[ref]; v = vn - vn[ref]
    return y, S, g

def check(y, S, Q, tol=None):
    """Is S(y) the grid version of clamp(w, y - Q, y) for one w?  Returns w and the max deviation
    (in population units) on y > 0.01."""
    m = y > 0.01
    free = m & (y - S < Q - 1e-9) if np.isfinite(Q) else m
    w = S[free].max() if free.any() else 0.0
    pred = np.clip(w, np.maximum(y - Q, 0), y) if np.isfinite(Q) else np.minimum(y, w)
    return w, np.abs(S - pred)[m].max()

if __name__ == "__main__":
    for name, F, x1 in [("BH R=2", bh(2.0), 1 / (np.sqrt(2) + 1)), ("BH R=4", bh(4.0), 1 / 3),
                        ("Ricker r=1", ricker(1.0), None), ("Ricker r=2", ricker(2.0), None)]:
        for sig in (0.1, 0.3, 0.6):
            for Q in (np.inf, 0.15):
                y, S, g = solve(F, sig, Q)
                w, dev = check(y, S, Q)
                print(f"{name:11s} sig={sig:.1f} Q={Q:5.2f}  g={g:.5f}  w*={w:.4f}  x1={x1 if x1 else float('nan'):.4f}  maxdev={dev:.4f}", flush=True)
