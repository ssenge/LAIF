"""One-bit flip algorithms on the 3-regular tree: tau0 iid (+1 w.p. p), vertex flips with probability q[s][l],
s = own initial bit, l = number of agreeing neighbours. Exact satisfied probability by enumerating the 2^10 initial
bits of the radius-2 tree; maximized from random starts. The case q[0] = q[1] is the family of Section 3.1 of [1]."""
import itertools, numpy as np
from scipy.optimize import minimize
CONF = np.array(list(itertools.product([0, 1], repeat=10)))   # v, w1..w3, children (w_i: 4+2(i-1), 5+2(i-1))
def value(p, q):                                           # q: (2, 4) flip probabilities
    v, w, ch = CONF[:, 0], CONF[:, 1:4], CONF[:, 4:].reshape(-1, 3, 2)
    pr = np.prod(np.where(CONF == 1, p, 1 - p), 1)
    lv = (w == v[:, None]).sum(1); fv = q[v, lv]
    lw = (ch == w[..., None]).sum(2) + (w == v[:, None]); fw = q[w, lw]
    tot = 0
    for flipv in (0, 1):
        zv = v ^ flipv; P1 = np.where(flipv, fv, 1 - fv)
        dis = np.where(w != zv[:, None], 1 - fw, fw)          # P(w ends on the other side of v)
        a, b, c = dis.T
        tot = tot + P1 * (a*b + a*c + b*c - 2*a*b*c)
    return float(pr @ tot)
assert abs(value(0.5, np.zeros((2, 4))) - 0.5) < 1e-12
rng = np.random.default_rng(0)
for sym in (True, False):
    best = 0
    for _ in range(300):
        x0 = rng.uniform(-3, 3, 5 if sym else 9)
        def f(x):
            s = 1 / (1 + np.exp(-x)); q = np.vstack([s[1:5], s[1:5] if sym else s[5:9]])
            return -value(s[0], q)
        r = minimize(f, x0, method="Nelder-Mead", options=dict(maxiter=4000, xatol=1e-8, fatol=1e-12))
        best = max(best, -r.fun)
    print("family of [1]" if sym else "flip prob depending on own bit", round(best, 6))
