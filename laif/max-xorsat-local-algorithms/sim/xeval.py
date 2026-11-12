"""Repeated evaluation with fresh noise for both the solve and the estimate. usage: xeval.py rows.jsonl out.jsonl [reps] [n] [seed0]"""
import sys, json
import numpy as np, jax, jax.numpy as jnp
from xor_limit import make, draws
import xor_mp
reps = int(sys.argv[3]) if len(sys.argv) > 3 else 5; n = int(sys.argv[4]) if len(sys.argv) > 4 else 200000; s0 = int(sys.argv[5]) if len(sys.argv) > 5 else 1000
for r in map(json.loads, open(sys.argv[1])):
    q, p = r["q"], r["p"]; x = jnp.asarray(r["params"])
    nu = jax.jit(xor_mp.make(q, p, r["H"]) if "H" in r else make(q, p, len(r["params"]) in (4 * p + 2, 5 * p + 2)))
    v = [float(nu(x, *draws(s0 + i, n, p))) for i in range(reps)]
    o = {"q": q, "p": p, "nu": float(np.mean(v)), "se": float(np.std(v, ddof=1) / np.sqrt(reps)), "solves": reps, "samples": n, "params": r["params"], **({"H": r["H"]} if "H" in r else {})}
    print(q, p, round(o["nu"], 4), round(o["se"], 4), flush=True)
    with open(sys.argv[2], "a") as fo: fo.write(json.dumps(o) + "\n")
