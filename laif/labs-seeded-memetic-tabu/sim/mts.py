"""Memetic tabu search for LABS as in arXiv:2511.04553 (Algorithms 1-3: K = 100, p_comb = 0.9, p_mut = 1/N, tournament 2,
tabu budget M uniform in [N/2, 3N/2), tenure M/10 + uniform{0..M/50}, aspiration on a new best), with time-to-solution
counted as objective evaluations (every one-flip neighbour inspected and every new child counts one) until the known
optimum first appears; also
returned: the number of tabu steps and of children (generations), for other readings of the counting unit. Initial populations:
  rand   K uniformly random sequences (the MTS baseline)
  bestR  the lowest of S uniformly random sequences, copied K times (seed cost S evaluations)
  sa     the lowest state of a simulated-annealing run of S evaluations, copied K times (seed cost S evaluations)"""
import numpy as np
from numba import njit

E_OPT = {20: 26, 21: 26, 22: 39, 23: 47, 24: 36, 25: 36, 26: 45, 27: 37, 28: 50, 29: 62, 30: 59, 31: 67, 32: 64,
         33: 64, 34: 65, 35: 73, 36: 82, 37: 86, 38: 87, 39: 99, 40: 108}

@njit(cache=True)
def energy(s):
    N = s.shape[0]; e = 0
    for k in range(1, N):
        c = 0
        for i in range(N - k): c += s[i] * s[i + k]
        e += c * c
    return e

@njit(cache=True)
def corr(s, C):
    N = s.shape[0]
    for k in range(1, N):
        c = 0
        for i in range(N - k): c += s[i] * s[i + k]
        C[k] = c

@njit(cache=True)
def flip_energy(s, C, j):
    """Energy after flipping s[j], from the correlations C of s, in O(N)."""
    N = s.shape[0]; e = 0
    for k in range(1, N):
        d = 0
        if j + k < N: d += s[j] * s[j + k]
        if j - k >= 0: d += s[j - k] * s[j]
        c = C[k] - 2 * d; e += c * c
    return e

@njit(cache=True)
def tabu(s, cnt):
    N = s.shape[0]; p = s.copy(); best = s.copy(); C = np.zeros(N, np.int64); corr(p, C)
    eb = energy(best); M = np.random.randint(0, N) + N // 2; tl = np.zeros(N, np.int64)
    tmin = max(1, M // 10); textra = max(1, M // 50)
    for t in range(1, M + 1):
        bi = -1; be = 1 << 60
        for i in range(N):
            e = flip_energy(p, C, i); cnt[0] += 1
            if (tl[i] < t or e < eb) and e < be: be = e; bi = i
        if bi < 0: break
        cnt[1] += 1
        p[bi] = -p[bi]; corr(p, C)
        tl[bi] = t + tmin + np.random.randint(0, textra + 1)
        if be < eb: eb = be; best[:] = p
    return best, eb

@njit(cache=True)
def mts(pop, target, gmax, seed, cnt0):
    np.random.seed(seed); K, N = pop.shape; P = pop.copy(); cnt = np.zeros(3, np.int64); cnt[0] = cnt0
    Ep = np.zeros(K, np.int64)
    for k in range(K): Ep[k] = energy(P[k]); cnt[0] += 1
    b = np.argmin(Ep); eb = Ep[b]
    if eb <= target: return cnt, eb
    for g in range(gmax):
        if np.random.random() < 0.9:
            a1, a2 = np.random.randint(K), np.random.randint(K); p1 = a1 if Ep[a1] <= Ep[a2] else a2
            a1, a2 = np.random.randint(K), np.random.randint(K); p2 = a1 if Ep[a1] <= Ep[a2] else a2
            k = np.random.randint(1, N); c = np.empty(N, np.int64); c[:k] = P[p1, :k]; c[k:] = P[p2, k:]
        else:
            c = P[np.random.randint(K)].copy()
        for i in range(N):
            if np.random.random() < 1.0 / N: c[i] = -c[i]
        c, ec = tabu(c, cnt); cnt[2] += 1
        r = np.random.randint(K); P[r] = c; Ep[r] = ec
        if ec < eb: eb = ec
        if eb <= target: return cnt, eb
    cnt[0] = -1; return cnt, eb

@njit(cache=True)
def best_random(N, S, seed):
    np.random.seed(seed); best = np.ones(N, np.int64); eb = 1 << 60
    for _ in range(S):
        s = 2 * np.random.randint(0, 2, N) - 1; e = energy(s)
        if e < eb: eb = e; best = s.copy()
    return best, eb

@njit(cache=True)
def sa(N, S, seed, T0=20.0, T1=0.5):
    """Single-flip simulated annealing with S objective evaluations on a geometric schedule; returns the lowest state."""
    np.random.seed(seed); s = 2 * np.random.randint(0, 2, N) - 1; C = np.zeros(N, np.int64); corr(s, C)
    e = energy(s); best = s.copy(); eb = e
    for t in range(S):
        T = T0 * (T1 / T0) ** (t / S); j = np.random.randint(N); en = flip_energy(s, C, j)
        if en <= e or np.random.random() < np.exp((e - en) / T):
            s[j] = -s[j]; corr(s, C); e = en
            if e < eb: eb = e; best[:] = s
    return best, eb
