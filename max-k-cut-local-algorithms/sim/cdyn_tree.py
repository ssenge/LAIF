"""Tree value of the colour-vector dynamics of cdyn.py: Random sampling of the i.i.d. seeds of the radius-p neighbourhood of an
edge of the d-regular tree (valid at girth 2p + 2). Empirical variance lower bound (README reference [4]) at confidence 1 - 1e-4.

usage: cdyn_tree.py k d p params.json-line-index samples [batch]
"""
import sys, json, math, time
import numpy as np
import jax, jax.numpy as jnp
from cdyn import wvecs


def make_eval(k, d, p, B):
    u, W = wvecs(k)
    u = jnp.asarray(u, dtype=jnp.complex64); W = jnp.asarray(W, dtype=jnp.float32)
    sizes = [2 * (d - 1) ** q for q in range(p + 1)]

    @jax.jit
    def run(params, key):
        al, g, b = params[0], params[1:p + 1], params[p + 1:]
        keys = jax.random.split(key, p + 1)
        psi = [(jnp.cos(al) * u + jnp.sin(al) * W[jax.random.randint(keys[q], (B, sizes[q]), 0, k)]).astype(jnp.complex64)
               for q in range(p + 1)]
        for t in range(p):
            top = p - t - 1                                          # levels 0..top get time t + 1
            P = [jnp.abs(x) ** 2 for x in psi[:top + 2]]
            new = []
            for q in range(top + 1):
                h = P[q + 1].reshape(B, sizes[q], d - 1, k).sum(axis=2)
                if q == 0:
                    h = h + P[0][:, ::-1]
                else:
                    h = h + jnp.repeat(P[q - 1], d - 1, axis=1)
                x = psi[q] * jnp.exp(-1j * g[t] * h)
                ov = x @ jnp.conj(u)
                new.append(x + (jnp.exp(-1j * b[t]) - 1) * ov[..., None] * u)
            psi = new
        lab = jnp.argmax(jnp.abs(psi[0]), axis=2)
        return jnp.sum(lab[:, 0] != lab[:, 1])
    return run


def evaluate(k, d, p, params, n, B=256, seed=2026):
    run = make_eval(k, d, p, B)
    q = jnp.asarray(params, dtype=jnp.float32); key = jax.random.PRNGKey(seed)
    hits = 0; m = 0
    while m < n:
        key, sub = jax.random.split(key)
        hits += int(run(q, sub)); m += B
    mean = hits / m; var = mean * (1 - mean) * m / (m - 1); L = math.log(2 / 1e-4)
    return mean, math.sqrt(var / m), mean - math.sqrt(2 * var * L / m) - 7 * L / (3 * (m - 1)), m


if __name__ == "__main__":
    k, d, p = map(int, sys.argv[1:4]); line = sys.argv[4]; n = int(float(sys.argv[5]))
    B = int(sys.argv[6]) if len(sys.argv) > 6 else 256
    rows = [json.loads(l) for l in open(line)]
    params = [r for r in rows if r["p"] == p][0]["params"]
    t0 = time.time()
    mean, se, lcb, m = evaluate(k, d, p, params, n, B)
    print(json.dumps({"k": k, "d": d, "p": p, "girth": 2 * p + 2, "samples": m, "mean": round(mean, 6), "se": round(se, 6),
                      "lcb": math.floor(lcb * 1e4) / 1e4, "sec": round(time.time() - t0, 1)}), flush=True)
