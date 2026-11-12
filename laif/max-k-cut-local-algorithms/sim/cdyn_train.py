"""Train the colour-vector dynamics directly on the tree (SGD over fresh seed batches, soft-argmax loss).
usage: cdyn_train.py k d p init.jsonl out.jsonl [steps] [B] [T] [lr]; without a depth-p row in init, extends depth p - 1"""
import sys, json
import numpy as np
import jax, jax.numpy as jnp
from cdyn import wvecs


def make_loss(k, d, p, B, T):
    u, W = wvecs(k)
    u = jnp.asarray(u, dtype=jnp.complex64); W = jnp.asarray(W, dtype=jnp.float32)
    sizes = [2 * (d - 1) ** q for q in range(p + 1)]

    def loss(params, key):
        al, g, b = params[0], params[1:p + 1], params[p + 1:]
        keys = jax.random.split(key, p + 1)
        psi = [(jnp.cos(al) * u + jnp.sin(al) * W[jax.random.randint(keys[q], (B, sizes[q]), 0, k)]).astype(jnp.complex64)
               for q in range(p + 1)]
        for t in range(p):
            top = p - t - 1
            P = [jnp.abs(x) ** 2 for x in psi[:top + 2]]
            new = []
            for q in range(top + 1):
                h = P[q + 1].reshape(B, sizes[q], d - 1, k).sum(axis=2)
                h = h + (P[0][:, ::-1] if q == 0 else jnp.repeat(P[q - 1], d - 1, axis=1))
                x = psi[q] * jnp.exp(-1j * g[t] * h)
                new.append(x + (jnp.exp(-1j * b[t]) - 1) * (x @ jnp.conj(u))[..., None] * u)
            psi = new
        s = jax.nn.softmax(T * jnp.abs(psi[0]) ** 2, axis=2)
        return jnp.mean(jnp.sum(s[:, 0] * s[:, 1], axis=1))
    return jax.jit(jax.value_and_grad(loss))


if __name__ == "__main__":
    k, d, p = map(int, sys.argv[1:4]); src, out = sys.argv[4], sys.argv[5]
    steps = int(sys.argv[6]) if len(sys.argv) > 6 else 300
    B = int(sys.argv[7]) if len(sys.argv) > 7 else 256
    T = float(sys.argv[8]) if len(sys.argv) > 8 else 30.0
    lr = float(sys.argv[9]) if len(sys.argv) > 9 else 0.005
    rows = list(map(json.loads, open(src)))
    same = [r for r in rows if r["p"] == p]
    if same:
        q0 = same[-1]["params"]
    else:                                                   # extend the depth p - 1 schedule by one layer
        r = [r for r in rows if r["p"] == p - 1][-1]["params"]; g, b = r[1:p], r[p:]
        q0 = [r[0]] + g + [g[-1]] + b + [b[-1]]
    q = jnp.asarray(q0, dtype=jnp.float32)
    f = make_loss(k, d, p, B, T); key = jax.random.PRNGKey(5)
    m = jnp.zeros_like(q); v = jnp.zeros_like(q); run = 0.0
    for t in range(1, steps + 1):
        key, sub = jax.random.split(key)
        val, gr = f(q, sub)
        m = 0.9 * m + 0.1 * gr; v = 0.999 * v + 0.001 * gr ** 2
        q = q - lr * (m / (1 - 0.9 ** t)) / (jnp.sqrt(v / (1 - 0.999 ** t)) + 1e-12)
        run = 0.98 * run + 0.02 * float(val)
        if t % 50 == 0: print(t, round(run / (1 - 0.98 ** t), 5), flush=True)
    with open(out, "a") as fh:
        fh.write(json.dumps({"k": k, "d": d, "p": p, "params": [float(x) for x in q]}) + "\n")
