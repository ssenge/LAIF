"""Monte Carlo of the algorithm: per round k is sampled, success with probability sin^2((2k+1) theta)."""
import numpy as np
from cert import rounds

def run(p, t, N, rng):
    lam, al, c, h0, k0, M = p
    th = np.arcsin(np.sqrt(t / N)); q = 0
    for _ in range(k0):
        q += 1
        if rng.random() < t / N: return q
    for a, h, m in rounds(p, int(rng.integers(M))):
        k = a + int(rng.integers(h)); q += k + 1
        if rng.random() < np.sin((2 * k + 1) * th) ** 2: return q

def exact(p, t, N):
    """E from the closed form, for comparison."""
    lam, al, c, h0, k0, M = p
    th = np.arcsin(np.sqrt(t / N)); tot = 0
    for u in range(M):
        s, e = 1.0, 0.0
        for _ in range(k0): e += s; s *= 1 - t / N
        for a, h, m in rounds(p, u):
            e += s * (a + (h - 1) / 2 + 1)
            s *= np.mean(np.cos((2 * (a + np.arange(h)) + 1) * th) ** 2) if h < 4000 else \
                0.5 + (np.sin(4 * (a + h) * th) - np.sin(4 * a * th)) / (4 * h * np.sin(2 * th))
            if s < 1e-18: break
        tot += e
    return tot / M

if __name__ == "__main__":
    rng = np.random.default_rng(5)
    for name, p in [("S", (1.59, 0.95, 1.0, 1, 0, 64)), ("U", (1.59, 0.95, 0.2, 2, 2, 64))]:
        for N, t in [(2 ** 20, 1), (2 ** 20, 37), (10 ** 6, 2 * 10 ** 4), (1000, 480)]:
            xs = np.array([run(p, t, N, rng) for _ in range(20000)])
            ex = exact(p, t, N); sc = np.sqrt(N / t)
            print("%s N=%d t=%d: MC %.4f +- %.4f, exact %.4f (per sqrt(N/t))" % (name, N, t, xs.mean() / sc, xs.std() / sc / np.sqrt(len(xs)), ex / sc))
