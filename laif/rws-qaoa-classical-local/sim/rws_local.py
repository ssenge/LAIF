"""Max-Cut on random 3-regular graphs: the regularized warm start (RWS) of arXiv:2603.10191 and a classical local rule.
RWS: maximize F(m) = sum_E (1 - m_i m_j)/2 + lam sum_i (1 - m_i^2) over m in [-1, 1]^N (m_i = 1 - 2 p_i, so F is
E[cut] + 4 lam sum p_i (1 - p_i), Eq. (11) there), lam = 0.6, by coordinate ascent to a fixed point, best F of M starts.
Rounding: s_i = +1 if m_i > 0, else -1.
Flip rule, one round: every vertex whose flip strictly increases the cut (a majority of its neighbours on its own side) and
whose random priority is the largest among such vertices at distance <= 1 flips; the flips are pairwise non-adjacent, so the
cut grows by the sum of their gains. One round reads the radius-2 ball, so R rounds have radius 2R."""
import numpy as np, networkx as nx
from numba import njit

def graph(N, seed):
    G = nx.random_regular_graph(3, N, seed=seed); nb = np.array([sorted(G[v]) for v in range(N)], np.int64)
    return G, nb

@njit(cache=True)
def rws_ca(nb, lam, M, seed, tol=1e-13, maxsweeps=100000):
    """RWS warm start by exact coordinate ascent: F is concave in each m_i, maximized at clip(-sum_j m_j / (4 lam)).
    Each start runs to a fixed point (largest change below tol); returns the start with the largest F."""
    np.random.seed(seed); N = nb.shape[0]; best = np.zeros(N); fb = -1e18
    for _ in range(M):
        m = np.random.uniform(-1, 1, N)
        for _ in range(maxsweeps):
            d = 0.0
            for i in range(N):
                x = min(1.0, max(-1.0, -(m[nb[i, 0]] + m[nb[i, 1]] + m[nb[i, 2]]) / (4 * lam)))
                d = max(d, abs(x - m[i])); m[i] = x
            if d < tol: break
        f = 0.0
        for i in range(N):
            f += lam * (1 - m[i] * m[i])
            for k in range(3):
                j = nb[i, k]
                if j > i: f += 0.5 * (1 - m[i] * m[j])
        if f > fb: fb = f; best[:] = m
    return best, fb

@njit(cache=True)
def cut(nb, s):
    c = 0
    for i in range(nb.shape[0]):
        for k in range(3):
            if nb[i, k] > i and s[i] != s[nb[i, k]]: c += 1
    return c

@njit(cache=True)
def rounds(nb, s, R, seed):
    np.random.seed(seed); N = nb.shape[0]; s = s.copy(); hist = np.zeros(R + 1, np.int64); hist[0] = cut(nb, s); done = R
    for r in range(R):
        pr = np.random.random(N); imp = np.zeros(N, np.bool_)
        for i in range(N):
            same = 0
            for k in range(3): same += s[nb[i, k]] == s[i]
            imp[i] = same >= 2
        fl = np.zeros(N, np.bool_); nf = 0
        for i in range(N):
            if imp[i]:
                ok = True
                for k in range(3):
                    j = nb[i, k]
                    if imp[j] and pr[j] > pr[i]: ok = False
                fl[i] = ok
        for i in range(N):
            if fl[i]: s[i] = -s[i]; nf += 1
        hist[r + 1] = cut(nb, s)
        if nf == 0: done = r; hist[r + 1:] = hist[r]; break
    return s, hist, done
