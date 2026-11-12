"""Infinite-degree limit of the colour-vector dynamics of cdyn.py, with gamma = G / sqrt(d).
Single-site process: phi(t) = eta(t) + sum_{s<t} R(t, s) dP(s), dP = |psi|^2 - 1/k, eta normal with covariance E[dP dP^T],
R(t, s) = E[d dP(t) / d phi(s)] by forward-mode differentiation. Covariance by a triangular factor in the sum-zero basis.
Cut fraction (k-1)/k + C/sqrt(d). Training uses softmax(beta |psi|^2) for the decision, evaluation the argmax.
C = -2 sum_c < Cov^-1 E[eta O_c], E[dP O_c] > with O_c = 1{output colour c} (normal integration by parts).
usage: cdyn_limit.py k p init.jsonl scale out.jsonl [steps] [n]
  init.jsonl holds a schedule for depth p (its gammas multiplied by scale) or for depth p - 1 (extended by one layer)."""
import sys, json, time
import numpy as np
import jax, jax.numpy as jnp
jax.config.update("jax_enable_x64", True)


def basis(k):
    u = np.ones(k) / np.sqrt(k)
    W = np.eye(k) - u[None, :] / np.sqrt(k); W /= np.linalg.norm(W, axis=1, keepdims=True)
    Bq, _ = np.linalg.qr(np.eye(k) - np.outer(u, u))
    return jnp.asarray(u), jnp.asarray(W), jnp.asarray(Bq[:, :k - 1])


def make(k, p):
    u, W, B = basis(k); m = k - 1

    def path(prm, c, eta, R, ext):
        """eta, ext: (p, k); R: (p, p, k, k). Returns dP (p, k) and |psi(p)|^2."""
        al, G, b = prm[0], prm[1:p + 1], prm[p + 1:]
        psi = (jnp.cos(al) * u + jnp.sin(al) * W[c]).astype(jnp.complex128)
        dPs = []
        for t in range(p):
            dP = jnp.abs(psi) ** 2 - 1.0 / k
            dPs.append(dP)
            phi = eta[t] + ext[t] + sum((R[t, s] @ dPs[s] for s in range(t)), jnp.zeros(k))
            psi = psi * jnp.exp(-1j * G[t] * phi)
            psi = psi + (jnp.exp(-1j * b[t]) - 1) * (jnp.conj(u) @ psi) * u
        return jnp.stack(dPs), jnp.abs(psi) ** 2

    vpath = jax.vmap(path, in_axes=(None, 0, 0, None, None))

    def solve(prm, cs, z):
        n = z.shape[0]
        R = jnp.zeros((p, p, k, k)); eta = jnp.zeros((n, p, k)); zero = jnp.zeros((p, k))
        for t in range(p):
            dP = vpath(prm, cs, eta, R, zero)[0][:, :t + 1, :]          # (n, t+1, k)
            X = (dP @ B).reshape(n, -1)
            L = jnp.linalg.cholesky(X.T @ X / n + 1e-12 * jnp.eye((t + 1) * m))
            et = ((z[:, :t + 1, :].reshape(n, -1) @ L.T).reshape(n, t + 1, m)) @ B.T
            eta = eta.at[:, :t + 1, :].set(et)
            if t + 1 < p:
                f = lambda ext: vpath(prm, cs, eta, R, ext)[0][:, t + 1, :].mean(0)
                J = jax.jacfwd(f)(zero)                                   # (k, p, k)
                R = R.at[t + 1, :t + 1].set(jnp.transpose(J[:, :t + 1, :], (1, 0, 2)))
        return L, R, eta

    def coef(prm, cs, z, cs2, z2, beta=None):
        L, R, _ = solve(prm, cs, z)
        n = z2.shape[0]
        eta = ((z2.reshape(n, -1) @ L.T).reshape(n, p, m)) @ B.T
        dP, Pf = vpath(prm, cs2, eta, R, jnp.zeros((p, k)))
        O = jax.nn.one_hot(jnp.argmax(Pf, 1), k) if beta is None else jax.nn.softmax(beta * Pf, 1)
        Xd = (dP @ B).reshape(n, -1); Z = z2.reshape(n, -1)
        a = Z.T @ O / n                                                   # (p m, k)
        bb = Xd.T @ O / n
        return -2 * jnp.sum(a * jax.scipy.linalg.solve_triangular(L, bb, lower=True))
    return coef


if __name__ == "__main__":
    k, p = int(sys.argv[1]), int(sys.argv[2])
    rows = [json.loads(l) for l in open(sys.argv[3])]
    r = [r for r in rows if r["p"] == p] or [r for r in rows if r["p"] == p - 1]
    prm = np.array(r[0]["params"], float)
    if len(prm) < 2 * p + 1:                                              # extend a depth p - 1 schedule
        q = (len(prm) - 1) // 2
        prm = np.concatenate([[prm[0]], prm[1:q + 1], [prm[q]], prm[q + 1:], [prm[-1]]])
    else:
        prm[1:p + 1] *= float(sys.argv[4])
    out = sys.argv[5]; steps = int(sys.argv[6]) if len(sys.argv) > 6 else 300; n = int(sys.argv[7]) if len(sys.argv) > 7 else 20000
    coef = make(k, p); m = k - 1
    rng = np.random.default_rng(0)
    ev = lambda x, s, N: coef(jnp.asarray(x), jnp.asarray(np.random.default_rng(s).integers(k, size=N)),
                              jnp.asarray(np.random.default_rng(s + 1).standard_normal((N, p, m))),
                              jnp.asarray(np.random.default_rng(s + 2).integers(k, size=N)),
                              jnp.asarray(np.random.default_rng(s + 3).standard_normal((N, p, m))))
    g = jax.jit(jax.value_and_grad(lambda x, a, b_, c, d: -coef(x, a, b_, c, d, 30.0)))
    x = jnp.asarray(prm); mo = jnp.zeros_like(x); v = jnp.zeros_like(x); lr = 0.01; t0 = time.time()
    for i in range(1, steps + 1):
        s = int(rng.integers(1 << 30))
        args = [jnp.asarray(np.random.default_rng(s + j).integers(k, size=n)) if j % 2 == 0 else
                jnp.asarray(np.random.default_rng(s + j).standard_normal((n, p, m))) for j in range(4)]
        val, gr = g(x, *args)
        mo = 0.9 * mo + 0.1 * gr; v = 0.999 * v + 0.001 * gr ** 2
        x = x - lr * (mo / (1 - 0.9 ** i)) / (jnp.sqrt(v / (1 - 0.999 ** i)) + 1e-8)
        if i % 50 == 0: print(i, -float(val), round(time.time() - t0), flush=True)
    C = float(ev(np.asarray(x), 12345, 200000))
    print("p", p, "C", C, flush=True)
    with open(out, "a") as fo: fo.write(json.dumps({"k": k, "p": p, "C": C, "params": [float(y) for y in x]}) + "\n")
