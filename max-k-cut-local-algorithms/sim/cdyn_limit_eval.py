"""Independent re-evaluations of the trained infinite-degree schedules: K solves with fresh noise, n samples each.
usage: cdyn_limit_eval.py k dm.jsonl K n p1 p2 ...  -> one json line per p with mean, sd, K, n"""
import sys, json
import numpy as np
import jax.numpy as jnp
from cdyn_limit import make
k = int(sys.argv[1]); rows = [json.loads(l) for l in open(sys.argv[2])]; K, n = int(sys.argv[3]), int(float(sys.argv[4]))
for p in map(int, sys.argv[5:]):
    x = jnp.asarray([r for r in rows if r["p"] == p][-1]["params"]); coef = make(k, p); vals = []
    for s in range(K):
        g = np.random.default_rng(10 ** 6 + 97 * s + p)
        vals.append(float(coef(x, jnp.asarray(g.integers(k, size=n)), jnp.asarray(g.standard_normal((n, p, k - 1))),
                               jnp.asarray(g.integers(k, size=n)), jnp.asarray(g.standard_normal((n, p, k - 1))))))
    print(json.dumps({"k": k, "p": p, "mean": float(np.mean(vals)), "sd": float(np.std(vals, ddof=1)), "K": K, "n": n}), flush=True)
