"""Search with a sound criterion: T = [l, 1] with l <= cos 1, G(T) in T, G < 1 on T minus {1}, and on T minus {1}
exactly one fixed point t* of G and of G o G, attracting. Then every orbit in T minus {1} tends to t*
(continuous interval map without 2-cycles; certified per map by certify.py)."""
import math, numpy as np
from maps import G, words
ts = np.linspace(-1, 1, 20001)
def roots(h, x):
    i = np.where(np.sign(h[:-1]) * np.sign(h[1:]) <= 0)[0]; return x[i]
for r in range(1, 6):
    for w in words(r):
        g = G(w, ts); l = math.cos(1)
        for _ in range(50):
            m = g[ts >= l].min()
            if m >= l - 1e-12: break
            l = m
        if l <= -0.999: continue
        sel = (ts >= l) & (ts < 1 - 1e-6); x = ts[sel]; gx = g[sel]
        if gx.max() >= 1 - 1e-9: continue
        f1 = roots(gx - x, x); f1 = f1[np.r_[True, np.diff(f1) > 1e-3]] if len(f1) else f1
        if len(f1) != 1: continue
        g2 = G(w, gx); f2 = roots(g2 - x, x); f2 = f2[np.r_[True, np.diff(f2) > 1e-3]] if len(f2) else f2
        if len(f2) != 1: continue
        t0 = f1[0]; d0 = (G(w, t0 + 1e-6)[0] - G(w, t0 - 1e-6)[0]) / 2e-6
        if abs(d0) >= 1: continue
        d1 = (1 - G(w, 1 - 1e-7)[0]) / 1e-7
        print(f"a={2*r} l={l:.4f} t*={t0:.5f} G'(t*)={d0:+.4f} G'(1)={d1:.3f} word={w}", flush=True)
