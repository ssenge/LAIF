"""Refine a schedule of xor_limit.py: gradient steps on the smoothed value, then a simplex search, both on fixed noise.
Without lin: add mixer axis angles (start 0). With lin: add output weights over the trajectory (start: final m only).
usage: xaxis.py q p init.jsonl out.jsonl [steps] [lin]"""
import sys, json
import numpy as np, jax, jax.numpy as jnp
from scipy.optimize import minimize
from xor_limit import make, draws
q, p = int(sys.argv[1]), int(sys.argv[2]); steps = int(sys.argv[5]) if len(sys.argv) > 5 else 300
lin = len(sys.argv) > 6 and sys.argv[6] == "lin"
f = make(q, p, lin); fj = jax.jit(f); A = draws(7, 50000, p)
rows = [r for r in map(json.loads, open(sys.argv[3])) if r["q"] == q and r["p"] == p and len(r["params"]) in ((2 * p + 1, 3 * p + 1) if not lin else (2 * p + 1, 3 * p + 1, 4 * p + 2, 5 * p + 2))]
x0 = np.array(max(rows, key=lambda r: r["nu"])["params"])
if not lin: x0 = x0 if len(x0) == 3 * p + 1 else np.concatenate([x0, np.zeros(p)])
elif len(x0) in (2 * p + 1, 3 * p + 1): x0 = np.concatenate([x0, np.eye(2 * p + 1)[p]])
print("start", float(fj(jnp.asarray(x0), *A)), flush=True)
g = jax.jit(jax.value_and_grad(lambda x, *B: -f(x, *B, 20.0)))
x = jnp.asarray(x0); mo = jnp.zeros_like(x); v = jnp.zeros_like(x); rng = np.random.default_rng(3); best = (float(fj(x, *A)), np.array(x))
x = x + 0.05 * jnp.asarray(rng.standard_normal(x.shape)) * (jnp.arange(x.shape[0]) > (2 * p if not lin else x.shape[0] - 2 * p - 2))   # break the th = 0 symmetry
for i in range(1, steps + 1):
    val, gr = g(x, *draws(int(rng.integers(1 << 30)), 20000, p))
    mo = 0.9 * mo + 0.1 * gr; v = 0.999 * v + 0.001 * gr ** 2
    x = x - 0.005 * (mo / (1 - 0.9 ** i)) / (jnp.sqrt(v / (1 - 0.999 ** i)) + 1e-8)
    if i % 50 == 0:
        e = float(fj(x, *A)); print(i, round(e, 4), flush=True)
        if e > best[0]: best = (e, np.array(x))
res = minimize(lambda y: -float(fj(jnp.asarray(y), *A)), best[1], method="Nelder-Mead", options={"maxfev": 1000, "xatol": 1e-4, "fatol": 1e-6})
xb = res.x if -res.fun > best[0] else best[1]
val = float(fj(jnp.asarray(xb), *draws(12345, 200000, p)))
print("q", q, "p", p, "nu", val, flush=True)
with open(sys.argv[4], "a") as fo: fo.write(json.dumps({"q": q, "p": p, "nu": val, "params": [float(y) for y in xb]}) + "\n")
