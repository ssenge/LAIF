"""Re-evaluate every row of hybrid_params.json (QAOA angles and rule) by exact tree contraction."""
import json
import numpy as np
import jax.numpy as jnp
from treeqaoa import unpack
from hybrid import joint
from hybrid_opt import tables, cut_value

worst = 0.0
for h in json.load(open("hybrid_params.json")):
    k, d, q = h["k"], h["d"], h["q"]
    comps, states, S, T = tables(k, d)
    move = {(s[0], tuple(s[1:])): a for s, a in h["move"]}
    acts = np.array([move.get((s[0], tuple(s[1])), 0) for s in states])
    x = np.empty(2 * q); x[0::2], x[1::2] = h["gamma"], h["beta"]
    f, phis, _ = unpack(jnp.array(x), k, q, "grover", "potts", "plus")
    J, _ = joint(f, phis, d)
    val = float(cut_value(jnp.real(J), jnp.array(np.eye(k)[acts]), jnp.array(S), jnp.array(T)))
    worst = max(worst, abs(val - h["cut"]))
    print(k, d, q, h["girth"], f"{val:.7f}")
assert worst < 1e-9, worst
print("all rows reproduced")
