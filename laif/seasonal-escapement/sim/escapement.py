"""Optimal escapement threshold w* for an annual season with quota cap Q (long-run average yield).

Policy: before the season the population is y; shoot q = min(Q, max(y - w, 0)).
w* comes from the DP over all policies (avg_dp.py); J(w), the yield of one threshold rule from the\nstationary law of a separate grid chain, cross-checks it.
Usage: python escapement.py bh 2.0 0.3 0.15 0.8   (model, R or r, sigma, cap Q or inf, current count)
"""
import sys
import numpy as np
import scipy.sparse as sp
from avg_dp import gh_lognormal, bh, ricker, solve, check

def J(F, sig, w, Q=np.inf, B=4.0, N=801, iters=3000):
    y = np.linspace(0, B, N); h = y[1] - y[0]; xi, wq = gh_lognormal(sig)
    S = np.clip(w, y - Q, y)
    Y = np.minimum(F(S[:, None], xi[None, :]), B) / h        # next state in grid units
    lo = np.minimum(np.floor(Y).astype(int), N - 2); fr = Y - lo
    rows = np.repeat(np.arange(N), len(xi) * 2)
    cols = np.stack([lo, lo + 1], -1).reshape(N, -1).ravel()
    vals = np.stack([(1 - fr) * wq, fr * wq], -1).reshape(N, -1).ravel()
    P = sp.csr_matrix((vals, (rows, cols)), shape=(N, N)).T.tocsr()
    pi = np.zeros(N); pi[np.searchsorted(y, max(w, 0.5))] = 1
    for _ in range(iters):
        pi = P @ pi
    return float(pi @ (y - S))

def w_star(F, sig, Q=np.inf):
    """Optimal threshold from the DP over all policies (log grid); returns (w*, long-run yield)."""
    y, S, g = solve(F, sig, Q)
    return check(y, S, Q)[0], g

if __name__ == "__main__":
    if len(sys.argv) == 6:
        m, p, sig, Q, y0 = sys.argv[1], float(sys.argv[2]), float(sys.argv[3]), float(sys.argv[4]), float(sys.argv[5])
        F = bh(p) if m == "bh" else ricker(p)
        w, g = w_star(F, sig, Q)
        print(f"w* = {w:.4f}  long-run yield = {g:.4f}  quota now = {min(Q, max(y0 - w, 0)):.4f}")
    else:   # self-check against the full DP over all policies
        for F, sig, Q in [(bh(2.0), 0.3, np.inf), (bh(2.0), 0.3, 0.15), (ricker(1.0), 0.6, np.inf), (ricker(1.0), 0.6, 0.15)]:
            w, gdp = w_star(F, sig, Q)
            g = J(F, sig, w, Q)                     # yield of the threshold rule alone, independent grid
            print(f"sig={sig} Q={Q}: w*={w:.4f} J(w*)={g:.5f}   DP over all policies g={gdp:.5f}")
            assert abs(g - gdp) < 3e-3
        print("ok")
