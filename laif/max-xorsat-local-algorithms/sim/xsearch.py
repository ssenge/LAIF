"""Random search plus a simplex search on the hard-decision limit value, fixed noise. usage: xsearch.py q p init.jsonl out.jsonl [N] [lin]"""
import sys, json
import numpy as np, jax, jax.numpy as jnp
from scipy.optimize import minimize
from xor_limit import make, draws
q, p = int(sys.argv[1]), int(sys.argv[2]); N = int(sys.argv[5]) if len(sys.argv) > 5 else 1000
lin = len(sys.argv) > 6 and sys.argv[6] == "lin"; nb = 2 * p + 1 + (2 * p + 1 if lin else 0)
nu = jax.jit(make(q, p, lin)); A = draws(7, 50000, p); g = np.random.default_rng(11)
f = lambda x: float(nu(jnp.asarray(x), *A))
cands = [np.array(r["params"], float) for r in map(json.loads, open(sys.argv[3])) if r["q"] == q and r["p"] == p and len(r["params"]) == nb]
cands += [np.concatenate([[g.uniform(-0.8, 0.8)], g.uniform(-3, 3, p), g.uniform(-np.pi, np.pi, p)] + ([g.standard_normal(2 * p + 1)] if lin else [])) for _ in range(N)]
vals = [f(x) for x in cands]; best = None
for i in np.argsort(vals)[::-1][:6]:
    res = minimize(lambda x: -f(x), cands[i], method="Nelder-Mead", options={"maxfev": 800, "xatol": 1e-4, "fatol": 1e-6})
    print(round(vals[i], 4), "->", round(-res.fun, 4), flush=True)
    if best is None or -res.fun > best[0]: best = (-res.fun, res.x)
x = jnp.asarray(best[1]); val = float(nu(x, *draws(12345, 200000, p)))
print("q", q, "p", p, "nu", val, flush=True)
with open(sys.argv[4], "a") as fo: fo.write(json.dumps({"q": q, "p": p, "nu": val, "params": [float(y) for y in best[1]]}) + "\n")
