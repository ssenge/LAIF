"""Infinite-degree limit of the spin dynamics (VIRAL with a q-body field) for Max-q-XORSAT on (D+1)-regular q-uniform
hypergraphs of large girth. Vertex state psi in C^2, m = |psi_0|^2 - |psi_1|^2, start cos(a) u + sin(a) s (e_0 - e_1)/sqrt2
with a random sign s. Layer t: psi(sigma) *= exp(-i G_t sigma phi_t), sigma = +1, -1; then psi += (e^{-i b_t} - 1) <u, psi> u.
phi_t = (1/sqrt D) sum_{e ni i} J_e prod_{j in e minus i} m_j(t). Output sign(m(p)).
Limit: phi_t = eta_t + sum_{s<t} K(t, s) m_s, eta normal with covariance Q^(q-1) (entrywise), Q = E[m m^T],
K(t, s) = (q-1) R(t, s) Q(t, s)^(q-2), R = E[dm_t / dphi_s]. Satisfied fraction 1/2 + nu sqrt(q / (2D)) with
nu = sqrt(q/2) sum_t E[d sigma / d phi_t] E[m_t sigma]^(q-1), and E[d sigma / d phi] = Cov^-1 E[eta sigma].
usage: xor_limit.py q p init.jsonl out.jsonl [steps] [n] [lr]"""
import sys, json, time
import numpy as np
import jax, jax.numpy as jnp
jax.config.update("jax_enable_x64", True)
U = jnp.asarray([1.0, 1.0]) / np.sqrt(2); W = jnp.asarray([1.0, -1.0]) / np.sqrt(2); SG = jnp.asarray([1.0, -1.0])


def make(q, p, lin=False):
    nb = 2 * p + 1 if lin else None   # lin: last 2p+1 entries weight (m_0..m_{p-1}, m_p, phi_1..phi_p) in the output sign
    def path(prm, s, eta, K, ext):
        w = prm[-nb:] if lin else None; prm = prm[:-nb] if lin else prm
        al, G, b = prm[0], prm[1:p + 1], prm[p + 1:2 * p + 1]
        th = prm[2 * p + 1:] if prm.shape[0] > 2 * p + 1 else None   # optional mixer axis angles
        psi = (jnp.cos(al) * U + jnp.sin(al) * s * W).astype(jnp.complex128)
        ms = []; ph = []
        for t in range(p):
            m = jnp.abs(psi[0]) ** 2 - jnp.abs(psi[1]) ** 2
            ms.append(m)
            phi = eta[t] + ext[t] + sum((K[t, r] * ms[r] for r in range(t)), 0.0)
            ph.append(phi)
            psi = psi * jnp.exp(-1j * G[t] * SG * phi)
            if th is None:
                psi = psi + (jnp.exp(-1j * b[t]) - 1) * (U @ psi) * U
            else:   # rotation by b_t about the axis at angle th_t in the x-y plane (th = 0: the mixer above, up to phase)
                psi = jnp.cos(b[t] / 2) * psi - 1j * jnp.sin(b[t] / 2) * jnp.stack([jnp.exp(-1j * th[t]) * psi[1], jnp.exp(1j * th[t]) * psi[0]])
        mf = jnp.abs(psi[0]) ** 2 - jnp.abs(psi[1]) ** 2
        return jnp.stack(ms), (mf if not lin else jnp.concatenate([jnp.stack(ms), mf[None], jnp.stack(ph)]) @ w)

    vpath = jax.vmap(path, in_axes=(None, 0, 0, None, None))

    def solve(prm, ss, z):
        n = z.shape[0]; K = jnp.zeros((p, p)); eta = jnp.zeros((n, p)); zero = jnp.zeros(p)
        for t in range(p):
            M = vpath(prm, ss, eta, K, zero)[0][:, :t + 1]
            Q = M.T @ M / n
            L = jnp.linalg.cholesky(Q ** (q - 1) + 1e-12 * jnp.eye(t + 1))
            eta = eta.at[:, :t + 1].set(z[:, :t + 1] @ L.T)
            if t + 1 < p:
                R = jax.jacfwd(lambda ext: vpath(prm, ss, eta, K, ext)[0][:, t + 1].mean())(zero)
                M2 = vpath(prm, ss, eta, K, zero)[0][:, :t + 2]
                Qr = (M2[:, t + 1:t + 2] * M2[:, :t + 1]).mean(0)
                K = K.at[t + 1, :t + 1].set((q - 1) * R[:t + 1] * Qr ** (q - 2))
        return L, K

    def nu(prm, ss, z, ss2, z2, beta=None):
        L, K = solve(prm, ss, z)
        eta = z2 @ L.T
        M, mf = vpath(prm, ss2, eta, K, jnp.zeros(p))
        sg = jnp.sign(mf) if beta is None else jnp.tanh(beta * mf)
        n = z2.shape[0]
        a = jax.scipy.linalg.solve_triangular(L.T, (z2 * sg[:, None]).mean(0), lower=False)   # Cov^-1 E[eta sigma]
        return np.sqrt(q / 2) * jnp.sum(a * ((M * sg[:, None]).mean(0)) ** (q - 1))
    return nu


def draws(s, n, p):
    g = np.random.default_rng(s)
    return [jnp.asarray(g.choice([-1.0, 1.0], size=n)), jnp.asarray(g.standard_normal((n, p))),
            jnp.asarray(g.choice([-1.0, 1.0], size=n)), jnp.asarray(g.standard_normal((n, p)))]


if __name__ == "__main__":
    q, p = int(sys.argv[1]), int(sys.argv[2])
    rows = [json.loads(l) for l in open(sys.argv[3])] if len(sys.argv) > 3 and sys.argv[3] != "-" else []
    r = [r for r in rows if r["q"] == q and r["p"] == p] or [r for r in rows if r["q"] == q and r["p"] == p - 1]
    if r:
        x = np.array(r[-1]["params"], float)
        if len(x) < 2 * p + 1:
            k_ = (len(x) - 1) // 2; x = np.concatenate([[x[0]], x[1:k_ + 1], [0.1 * x[k_]], x[k_ + 1:], [0.1 * x[-1]]])   # nearly idle layer
    else:
        x = np.concatenate([[0.3], np.full(p, 0.5), np.full(p, 0.6)])
    out = sys.argv[4]; steps = int(sys.argv[5]) if len(sys.argv) > 5 else 400; n = int(sys.argv[6]) if len(sys.argv) > 6 else 20000
    f = make(q, p); fj = jax.jit(f); lr = float(sys.argv[7]) if len(sys.argv) > 7 else 0.01
    g = jax.jit(jax.value_and_grad(lambda x, *A: -f(x, *A, 20.0)))
    E = draws(777, 50000, p); best = (float(fj(jnp.asarray(x), *E)), np.array(x))
    x = jnp.asarray(x); mo = jnp.zeros_like(x); v = jnp.zeros_like(x); rng = np.random.default_rng(0); t0 = time.time()
    for i in range(1, steps + 1):
        val, gr = g(x, *draws(int(rng.integers(1 << 30)), n, p))
        mo = 0.9 * mo + 0.1 * gr; v = 0.999 * v + 0.001 * gr ** 2
        x = x - lr * (mo / (1 - 0.9 ** i)) / (jnp.sqrt(v / (1 - 0.999 ** i)) + 1e-8)
        if i % 50 == 0:
            e = float(fj(x, *E))
            if e > best[0]: best = (e, np.array(x))
            print(i, -float(val), round(e, 4), round(time.time() - t0), flush=True)
    x = jnp.asarray(best[1])                                     # best checkpoint on fixed evaluation noise
    val = float(fj(x, *draws(12345, 200000, p)))
    print("q", q, "p", p, "nu", val, flush=True)
    with open(out, "a") as fo: fo.write(json.dumps({"q": q, "p": p, "nu": val, "params": [float(y) for y in x]}) + "\n")
