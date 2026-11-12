"""Infinite-degree limit of a general local message passing for Max-q-XORSAT, as in xor_limit.py but with learned messages.
Vertex sign s; m_0 = tanh(c) s; m_t = f_t(s, phi_1..phi_t) for t < p; output sign(g(s, phi_1..phi_p)); f_t, g small tanh networks.
phi_t = (1/sqrt D) sum_{e ni i} J_e prod_{j in e minus i} m_j(t - 1) on the hypergraph; the limit is the one of xor_limit.py.
Warm start from depth p - 1 (init.jsonl): the new message function is a copy of the last one with zero weight on the new field,
so the start has the value of depth p - 1.
usage: xor_mp.py q p out.jsonl [steps] [H] [seed] [lr] [init.jsonl]"""
import os, sys, json, time
import numpy as np
import jax, jax.numpy as jnp
from xor_limit import draws
jax.config.update("jax_enable_x64", True)


def shapes(p, H):
    return [(H, p + 1), (H,), (H,), ()] * p          # f_1..f_{p-1}, then g as the p-th net; plus c at the end


def unpack(x, p, H):
    out, i = [], 0
    for s in shapes(p, H):
        k = int(np.prod(s)) if s else 1
        out.append(x[i:i + k].reshape(s)); i += k
    return [out[4 * j:4 * j + 4] for j in range(p)], x[i]


def nparams(p, H):
    return sum(int(np.prod(s)) if s else 1 for s in shapes(p, H)) + 1


def extend(x, p, H, rng):
    """Schedule of depth p - 1 to depth p with the same value."""
    nets, c0 = unpack(np.asarray(x), p - 1, H)
    pad = lambda P: [np.concatenate([P[0], np.zeros((H, 1))], 1), P[1], P[2], P[3]]
    nets = [pad(P) for P in nets]
    new = [P for P in nets[:-1]] + ([[a.copy() for a in nets[-2]]] if p > 2 else [[0.5 * rng.standard_normal((H, p + 1)), 0.5 * rng.standard_normal(H), 0.5 * rng.standard_normal(H), np.zeros(())]]) + [nets[-1]]
    return np.concatenate([np.ravel(a) for P in new for a in P] + [[c0]])


def make(q, p, H):
    def net(P, v):
        W, b, a, c = P
        return a @ jnp.tanh(W @ v + b) + c

    def path(x, s, eta, K, ext):
        nets, c0 = unpack(x, p, H)
        ms = [jnp.tanh(c0) * s]; ph = []
        for t in range(p):
            ph.append(eta[t] + ext[t] + sum((K[t, r] * ms[r] for r in range(t)), 0.0))
            v = jnp.concatenate([s[None], jnp.stack(ph), jnp.zeros(p - t - 1)])
            if t + 1 < p: ms.append(jnp.tanh(net(nets[t], v)))
        return jnp.stack(ms), net(nets[p - 1], v)

    vpath = jax.vmap(path, in_axes=(None, 0, 0, None, None))

    def solve(x, ss, z):
        n = z.shape[0]; K = jnp.zeros((p, p)); eta = jnp.zeros((n, p)); zero = jnp.zeros(p)
        for t in range(p):
            M = vpath(x, ss, eta, K, zero)[0][:, :t + 1]
            Q = M.T @ M / n
            L = jnp.linalg.cholesky(Q ** (q - 1) + 1e-12 * jnp.eye(t + 1))
            eta = eta.at[:, :t + 1].set(z[:, :t + 1] @ L.T)
            if t + 1 < p:
                R = jax.jacfwd(lambda ext: vpath(x, ss, eta, K, ext)[0][:, t + 1].mean())(zero)
                M2 = vpath(x, ss, eta, K, zero)[0][:, :t + 2]
                Qr = (M2[:, t + 1:t + 2] * M2[:, :t + 1]).mean(0)
                K = K.at[t + 1, :t + 1].set((q - 1) * R[:t + 1] * Qr ** (q - 2))
        return L, K

    def nu(x, ss, z, ss2, z2, beta=None):
        L, K = solve(x, ss, z)
        M, gf = vpath(x, ss2, z2 @ L.T, K, jnp.zeros(p))
        sg = jnp.sign(gf) if beta is None else jnp.tanh(beta * gf)
        a = jax.scipy.linalg.solve_triangular(L.T, (z2 * sg[:, None]).mean(0), lower=False)
        return np.sqrt(q / 2) * jnp.sum(a * ((M * sg[:, None]).mean(0)) ** (q - 1))
    return nu


if __name__ == "__main__":
    q, p, out = int(sys.argv[1]), int(sys.argv[2]), sys.argv[3]
    steps = int(sys.argv[4]) if len(sys.argv) > 4 else 1500; H = int(sys.argv[5]) if len(sys.argv) > 5 else 8
    seed = int(sys.argv[6]) if len(sys.argv) > 6 else 0; lr = float(sys.argv[7]) if len(sys.argv) > 7 else 0.01
    f = make(q, p, H); fj = jax.jit(f); rng = np.random.default_rng(seed)
    NT, NE, NF = (int(os.environ.get(k, d)) for k, d in (("XMP_NT", 20000), ("XMP_NE", 50000), ("XMP_NF", 200000)))   # sample sizes; lower them at large p to fit memory
    init = [r for r in map(json.loads, open(sys.argv[8])) if r["q"] == q and r.get("H") == H] if len(sys.argv) > 8 else []
    same = [r for r in init if r["p"] == p]; prev = [r for r in init if r["p"] == p - 1]
    if same: x = jnp.asarray(max(same, key=lambda r: r["nu"])["params"])
    elif prev: x = jnp.asarray(extend(max(prev, key=lambda r: r["nu"])["params"], p, H, rng))
    else: x = jnp.asarray(0.5 * rng.standard_normal(nparams(p, H)))
    g = jax.jit(jax.value_and_grad(lambda x, *A: -f(x, *A, 10.0)))
    E = draws(777, NE, p); best = (float(fj(x, *E)), np.array(x))
    mo = jnp.zeros_like(x); v = jnp.zeros_like(x); t0 = time.time()
    for i in range(1, steps + 1):
        val, gr = g(x, *draws(int(rng.integers(1 << 30)), NT, p))
        mo = 0.9 * mo + 0.1 * gr; v = 0.999 * v + 0.001 * gr ** 2
        x = x - lr * (mo / (1 - 0.9 ** i)) / (jnp.sqrt(v / (1 - 0.999 ** i)) + 1e-8)
        if i % 100 == 0:
            e = float(fj(x, *E))
            if e > best[0]: best = (e, np.array(x))
            print(i, round(-float(val), 4), round(e, 4), round(time.time() - t0), flush=True)
    val = float(fj(jnp.asarray(best[1]), *draws(12345, NF, p)))
    print("q", q, "p", p, "H", H, "nu", val, flush=True)
    with open(out, "a") as fo: fo.write(json.dumps({"q": q, "p": p, "H": H, "nu": val, "params": [float(y) for y in best[1]]}) + "\n")
