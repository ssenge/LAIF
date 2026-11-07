"""Colour-vector dynamics for Max-k-Cut, a k-colour version of VIRAL (README reference [6]).
Vertex state psi_i in C^k. Seed c_i uniform in [k]: psi_i(0) = cos(al) u + sin(al) w_{c_i}, u uniform unit vector,
w_c = unit vector of e_c - u/sqrt(k). Layer n: psi_i(c) *= exp(-i g_n sum_{j~i} |psi_j(c)|^2), then
psi_i += (exp(-i b_n) - 1) <u|psi_i> u. Output colour argmax_c |psi_i(c)|^2.
train: on a random d-regular graph with the smooth loss mean_edges sum_c P_i(c) P_j(c)."""
import sys, json
import numpy as np
import jax, jax.numpy as jnp
jax.config.update("jax_enable_x64", True)


def wvecs(k):
    u = np.ones(k) / np.sqrt(k)
    W = np.eye(k) - u[None, :] / np.sqrt(k)
    return u, W / np.linalg.norm(W, axis=1, keepdims=True)


def regular_graph(n, d, rng):
    while True:
        st = rng.permutation(np.repeat(np.arange(n), d)).reshape(-1, 2)
        if np.all(st[:, 0] != st[:, 1]): return st


def dyn_graph(params, seeds, E, n, k, p):
    al, g, b = params[0], params[1:p + 1], params[p + 1:]
    u, W = wvecs(k)
    psi = jnp.cos(al) * u[None, :] + jnp.sin(al) * jnp.asarray(W)[seeds]
    psi = psi.astype(jnp.complex128)
    for t in range(p):
        P = jnp.abs(psi) ** 2
        h = jnp.zeros((n, k)).at[E[:, 0]].add(P[E[:, 1]]).at[E[:, 1]].add(P[E[:, 0]])
        psi = psi * jnp.exp(-1j * g[t] * h)
        ov = psi @ u
        psi = psi + (jnp.exp(-1j * b[t]) - 1) * ov[:, None] * u[None, :]
    return psi


def loss(params, seeds, E, n, k, p):
    P = jnp.abs(dyn_graph(params, seeds, E, n, k, p)) ** 2
    return jnp.mean(jnp.sum(P[E[:, 0]] * P[E[:, 1]], axis=1))


def cutfrac(params, seeds, E, n, k, p):
    lab = jnp.argmax(jnp.abs(dyn_graph(params, seeds, E, n, k, p)), axis=1)
    return float(jnp.mean(lab[E[:, 0]] != lab[E[:, 1]]))


def train(k, d, p, init, n=20000, steps=300, lr=0.02, seed=0):
    rng = np.random.default_rng(seed)
    E = jnp.asarray(regular_graph(n, d, rng)); seeds = jnp.asarray(rng.integers(k, size=n))
    f = jax.jit(jax.value_and_grad(lambda q: loss(q, seeds, E, n, k, p)))
    q = jnp.asarray(init, dtype=jnp.float64); m = jnp.zeros_like(q); v = jnp.zeros_like(q)
    for t in range(1, steps + 1):                                   # Adam
        val, gr = f(q)
        m = 0.9 * m + 0.1 * gr; v = 0.999 * v + 0.001 * gr ** 2
        q = q - lr * (m / (1 - 0.9 ** t)) / (jnp.sqrt(v / (1 - 0.999 ** t)) + 1e-12)
    E2 = jnp.asarray(regular_graph(n, d, rng)); s2 = jnp.asarray(rng.integers(k, size=n))
    return np.asarray(q), float(val), cutfrac(q, s2, E2, n, k, p)


if __name__ == "__main__":
    k, d, P = map(int, sys.argv[1:4])
    rng = np.random.default_rng(1)
    q = None
    for p in range(1, P + 1):
        if q is None:
            init = np.concatenate([[0.4], 0.5 * np.ones(p), 0.5 * np.ones(p)])
        else:                                                       # warm start: extend schedules
            al, g, b = q[0], q[1:p], q[p:]
            init = np.concatenate([[al * 0.8], np.append(g, g[-1]), np.append(b, b[-1] * 0.8)])
        best = None
        for trial in range(3):
            st = init + (0 if trial == 0 else 0.1 * rng.standard_normal(len(init)))
            r = train(k, d, p, st, seed=trial)
            if best is None or r[2] > best[2]: best = r
        q = best[0]
        print(json.dumps({"k": k, "d": d, "p": p, "graph_cut": round(best[2], 5), "loss": round(best[1], 5),
                          "params": [round(float(x), 6) for x in q]}), flush=True)
