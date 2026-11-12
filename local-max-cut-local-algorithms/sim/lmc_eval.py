"""Hard rule z_u = sign(g_u - T), T = m + c m^2 (a + b) with a <= m <= b the sorted seeds of the three neighbours.
Value on the 3-regular tree: fraction of vertices with at least 2 of 3 neighbours on the other side, sampled on
independent radius-2 trees (numpy, chunks of 10^7), with a two-sided Hoeffding bound at failure probability 1e-9."""
import sys, numpy as np
def T(s, c):
    s = np.sort(s, -1); m = s[..., 1]
    return m + c * m * m * (s[..., 0] + s[..., 2])
def chunk(rng, n, c):
    gv = rng.standard_normal(n); gn = rng.standard_normal((n, 3)); gc = rng.standard_normal((n, 3, 2))
    zv = gv > T(gn, c)
    zw = gn > T(np.concatenate([np.repeat(gv[:, None, None], 3, 1), gc], -1), c)
    return np.count_nonzero((zw != zv[:, None]).sum(1) >= 2)
if __name__ == "__main__":
    c, chunks, seed = float(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
    rng = np.random.default_rng(seed); n = 10**7
    assert abs(chunk(np.random.default_rng(0), 10**6, 0.0) / 10**6 - 0.8160) < 0.003   # c = 0: median rule
    k = sum(chunk(rng, n, c) for _ in range(chunks)); N = n * chunks; f = k / N
    t = np.sqrt(np.log(2 / 1e-9) / (2 * N))
    print(f"c={c} N={N} value={f:.6f} se={np.sqrt(f*(1-f)/N):.6f} hoeffding_lower={f - t:.6f}", flush=True)
