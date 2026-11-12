"""Infinite-degree limit of the colour-vector dynamics (cdyn.py) for Max-k-Cut on d-regular trees, gamma = G / sqrt(d).
Single-site process: phi(t) = eta(t) + sum_{s<t} R(t,s) dP(s), dP = |psi|^2 - 1/k, eta normal over (t, colour) with
Cov(eta(t), eta(s)) = E[dP(t) dP(s)^T], R(t, s) = E[d dP(t) / d phi(s)] (k x k). Layer: psi *= exp(-i G_t phi(t)), then mixer.
Cut fraction (k-1)/k + C/sqrt(d) with C = -2 sum_c < Cinv E[eta O_c], E[dP O_c] >, O_c = 1{argmax |psi(p)| = c},
the vectors indexed by (t, colour), t = 0..p-1.
Layer-by-layer numpy version of cdyn_limit.py, used as a cross-check.
usage: cdyn_limit_np.py k p params.jsonl [scale]  (gammas multiplied by scale)"""
import sys, json
import numpy as np
import jax, jax.numpy as jnp
jax.config.update("jax_enable_x64", True)


def wvecs(k):
    u = np.ones(k) / np.sqrt(k)
    W = np.eye(k) - u[None, :] / np.sqrt(k)
    return u, W / np.linalg.norm(W, axis=1, keepdims=True)


def site(params, seed_c, etas, Rs, k, p, extra=None):
    """One site path. etas: (p, k) normal field values; Rs: list of (t, s) -> k x k for s < t.
    extra: optional (p, k) external field (for responses). Returns dP (p, k) and final |psi|^2."""
    al, G, b = params[0], params[1:p + 1], params[p + 1:]
    u, W = wvecs(k); u = jnp.asarray(u); W = jnp.asarray(W)
    psi = (jnp.cos(al) * u + jnp.sin(al) * W[seed_c]).astype(jnp.complex128)
    dPs = []
    for t in range(p):
        dP = jnp.abs(psi) ** 2 - 1.0 / k
        dPs.append(dP)
        phi = etas[t] + sum(Rs[t][s] @ dPs[s] for s in range(t))
        if extra is not None: phi = phi + extra[t]
        psi = psi * jnp.exp(-1j * G[t] * phi)
        psi = psi + (jnp.exp(-1j * b[t]) - 1) * (jnp.conj(u) @ psi) * u
    return jnp.stack(dPs), jnp.abs(psi) ** 2


def solve(params, k, p, n, seed=0):
    """Forward self-consistency; returns covariance C ((p k) x (p k)), responses R, and samples."""
    rng = np.random.default_rng(seed)
    seeds = rng.integers(k, size=n)
    Z = rng.standard_normal((n, p, k))
    C = np.zeros((p * k, p * k)); R = [[None] * p for _ in range(p)]
    params = jnp.asarray(params)

    def paths(etas, Rl, ext=None):
        f = lambda c, e, x: site(params, c, e, Rl, k, p, x)[0]
        if ext is None:
            return jax.vmap(lambda c, e: site(params, c, e, Rl, k, p)[0])(seeds, etas)
        return jax.vmap(f)(seeds, etas, ext)

    eta = np.zeros((n, p, k))
    for t in range(p):
        # dP(t) depends on eta(0..t-1) and R(.,.) with indices < t: compute with current partial objects
        Rl = [[(jnp.asarray(R[a][b_]) if (R[a][b_] is not None) else jnp.zeros((k, k))) for b_ in range(p)] for a in range(p)]
        dP = np.asarray(paths(jnp.asarray(eta), Rl))           # (n, p, k); entries up to t are final
        X = dP[:, :t + 1, :].reshape(n, -1)
        Ct = X.T @ X / n
        C[:(t + 1) * k, :(t + 1) * k] = Ct
        # eta(0..t) jointly normal with covariance Ct (in the sum-zero subspace; use eigen-decomposition)
        w, V = np.linalg.eigh(Ct); w = np.clip(w, 0, None)
        Lm = V * np.sqrt(w)
        eta[:, :t + 1, :] = (Z[:, :t + 1, :].reshape(n, -1) @ Lm.T).reshape(n, t + 1, k) if t == 0 else eta[:, :t + 1, :]
        if t > 0:
            # extend eta(t) conditionally on eta(0..t-1): build full and keep old block
            full = (np.concatenate([Z[:, :t + 1, :].reshape(n, -1)], 1) @ Lm.T).reshape(n, t + 1, k)
            eta[:, :t + 1, :] = full
        # responses R(t+1, s) = E[d dP(t+1) / d ext(s)] for s <= t, by forward-mode autodiff of the mean
        if t + 1 < p:
            Rl = [[(jnp.asarray(R[a][b_]) if (R[a][b_] is not None) else jnp.zeros((k, k))) for b_ in range(p)] for a in range(p)]
            def mean_dP(ext):
                return paths(jnp.asarray(eta), Rl, jnp.broadcast_to(ext, (n, p, k)))[:, t + 1, :].mean(0)
            J = np.asarray(jax.jacfwd(mean_dP)(jnp.zeros((p, k))))   # (k, p, k)
            for s in range(t + 1):
                R[t + 1][s] = J[:, s, :]
    return C, R, seeds, eta


def coefficient(params, k, p, n, seed=0, Ctrain=None):
    C, R, seeds, eta = solve(params, k, p, n, seed)
    Rl = [[(jnp.asarray(R[a][b_]) if (R[a][b_] is not None) else jnp.zeros((k, k))) for b_ in range(p)] for a in range(p)]
    # fresh samples for the final expectations, eta from the solved covariance
    rng = np.random.default_rng(seed + 1000)
    seeds2 = rng.integers(k, size=n)
    w, V = np.linalg.eigh(C); w = np.clip(w, 0, None); Lm = V * np.sqrt(w)
    eta2 = (rng.standard_normal((n, p * k)) @ Lm.T).reshape(n, p, k)
    out = jax.vmap(lambda c, e: site(jnp.asarray(params), c, e, Rl, k, p))(seeds2, jnp.asarray(eta2))
    dP = np.asarray(out[0]).reshape(n, -1); Pfin = np.asarray(out[1])
    col = Pfin.argmax(1)
    Ci = np.linalg.pinv(C, rcond=1e-10)
    E = eta2.reshape(n, -1); tot = 0.0
    for c in range(k):
        m = col == c
        tot += (Ci @ (E[m].sum(0) / n)) @ (dP[m].sum(0) / n)
    return -2 * tot


if __name__ == "__main__":
    k, p = int(sys.argv[1]), int(sys.argv[2])
    rows = [json.loads(l) for l in open(sys.argv[3])]
    prm = [r for r in rows if r["p"] == p][0]["params"]
    scale = float(sys.argv[4]) if len(sys.argv) > 4 else 1.0
    prm = np.array(prm); prm[1:p + 1] *= scale
    print(coefficient(prm, k, p, 200000))
