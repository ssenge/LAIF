"""Value of the radius-1 rule z_u = [g_u > sum_i w_i s_(i)] (sorted neighbour seeds, Gaussian seeds) for LocalMaxCut
on the d-regular tree, sampled on independent radius-2 trees, with a two-sided Hoeffding bound at failure 1e-9.
Usage: lmc_eval_d.py d chunks seed (chunks of 10^6 trees)."""
import sys, json, numpy as np
from rd import val
W = {4: [0.14, 0.64, 0.64, 0.14], 5: [0.04, 0.39, 0.81, 0.39, 0.04], 6: [0.08, 0.25, 0.61, 0.61, 0.25, 0.08],
     7: [0.04, 0.24, 0.45, 0.65, 0.45, 0.24, 0.04], 8: [0.06, 0.22, 0.42, 0.41, 0.41, 0.42, 0.22, 0.06]}
if __name__ == "__main__":
    d, chunks, seed = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
    w = np.array(W[d]); assert np.allclose(w, w[::-1]) and len(w) == d
    rng = np.random.default_rng(seed); n = 10**6; k = 0
    for _ in range(chunks):
        gv, gn, gc = rng.standard_normal(n), rng.standard_normal((n, d)), rng.standard_normal((n, d, d - 1))
        k += round(val(d, w, (gv, gn, gc)) * n)
    N = n * chunks; f = k / N; t = np.sqrt(np.log(2 / 1e-9) / (2 * N))
    print(json.dumps({"d": d, "w": W[d], "N": N, "seed": seed, "value": f, "se": float(np.sqrt(f * (1 - f) / N)),
                      "hoeffding_lower": f - t}), flush=True)
