"""Uniformly damped spring networks M x'' + 2 g M x' + K x = 0: exact solution against the two random-walk
estimators of the notes.

exact      eigen-decomposition of A~ = M^{-1/2} K M^{-1/2}, mode propagator from scalar_check.mode
heat walk  x(t) ~ e^{-sA}(x0 + v0/(2g)), s = t/(2g), A = M^{-1} K, by killed continuous-time random walks
poisson    for g^2 >= max_j K_jj/m_j: x(t) = E[P^{floor(N/2)} x0 + 1{N odd} P^{(N-1)/2} v0/g], N ~ Poisson(g t)

Checks (1) the Poisson identity exactly through its series, (2) both walk estimators against the exact
positions at one node, and (3) the energy-norm distance between the exact state and the heat model against
the bound 0.47/(g t)."""
import numpy as np
from scipy.linalg import expm
from scipy.stats import poisson
import scalar_check as sc

rng = np.random.default_rng(7)


def network(N, d, walls):
    K = np.zeros((N, N))
    for j in range(N):
        for k in rng.choice(N, size=d // 2, replace=False):
            if k != j and K[j, k] == 0:
                c = rng.uniform(0.2, 1.0)
                K[j, k] = K[k, j] = -c
    np.fill_diagonal(K, 0)
    K[np.diag_indices(N)] = -K.sum(1) + walls * rng.uniform(0, 0.3, N)
    m = rng.uniform(0.5, 2.0, N)
    return K, m


def exact(K, m, g, t, x0, v0):
    s = 1 / np.sqrt(m)
    At = s[:, None] * K * s[None, :]
    lam, U = np.linalg.eigh(At)
    lam = np.clip(lam, 0, None)
    u0, w0 = U.T @ (np.sqrt(m) * x0), U.T @ (np.sqrt(m) * v0)
    l = lam / g ** 2
    F, G, Gd = sc.mode(l, g * t)
    u = F * u0 + G / g * w0                     # u(t) per mode (G/g is the solution with u'(0) = 1)
    w = -lam * G / g * u0 + Gd * w0
    return s * (U @ u), s * (U @ w), lam, U, u, w


def heat_walk(K, m, s, y0, j, walks):
    rates = -K / m[:, None]
    np.fill_diagonal(rates, 0)
    out = rates.sum(1)
    kill = np.diag(K) / m - out
    tot = out + kill
    acc = 0.0
    for _ in range(walks):
        v, clock = j, rng.exponential(1 / tot[j])
        alive = True
        while clock < s:
            if rng.random() < kill[v] / tot[v]:
                alive = False
                break
            v = rng.choice(len(m), p=rates[v] / out[v])
            clock += rng.exponential(1 / tot[v])
        acc += y0[v] if alive else 0.0
    return acc / walks


def poisson_walk(K, m, g, t, x0, v0, j, walks):
    A = K / m[:, None]
    P = (g * g * np.eye(len(m)) - A) / g ** 2
    assert P.min() >= -1e-12
    acc = 0.0
    for _ in range(walks):
        Nn = rng.poisson(g * t)
        v, alive = j, True
        for _ in range(Nn // 2):
            row = np.clip(P[v], 0, None)
            stay = row.sum()
            if rng.random() > stay:
                alive = False
                break
            v = rng.choice(len(m), p=row / stay)
        if alive:
            acc += x0[v] + (v0[v] / g if Nn % 2 else 0.0)
    return acc / walks


def poisson_series(K, m, g, t, x0, v0, kmax=400):
    A = K / m[:, None]
    P = (g * g * np.eye(len(m)) - A) / g ** 2
    x, Pk_x, Pk_v = np.zeros_like(x0), x0.copy(), v0.copy()
    for k in range(kmax):
        x += poisson.pmf(2 * k, g * t) * Pk_x + poisson.pmf(2 * k + 1, g * t) * (Pk_x + Pk_v / g)
        Pk_x, Pk_v = P @ Pk_x, P @ Pk_v
    return x


if __name__ == "__main__":
    ok = True
    N = 60
    for trial in range(3):
        K, m = network(N, 4, walls=1)
        x0 = np.zeros(N); v0 = np.zeros(N); v0[0] = 1.0; x0[1] = 0.5
        a = (np.diag(K) / m).max()
        # (1) Poisson identity, g above every clamped-node frequency
        g = 1.05 * np.sqrt(a); t = 7.0
        xe = exact(K, m, g, t, x0, v0)[0]
        xs = poisson_series(K, m, g, t, x0, v0)
        e1 = np.abs(xe - xs).max()
        # (2) walk estimators at node j = 2
        j, W = 2, 20000
        pw = poisson_walk(K, m, g, t, x0, v0, j, W)
        gh, th = 0.4, 15.0                      # free network (zero mode kept), gt = 6
        K, m = network(N, 4, walls=0)
        xe2 = exact(K, m, gh, th, x0, v0)[0]
        y0 = x0 + v0 / (2 * gh)
        hw = heat_walk(K, m, th / (2 * gh), y0, j, W)
        hx = (expm(-(th / (2 * gh)) * K / m[:, None]) @ y0)[j]
        # (3) energy-norm distance between exact state and heat model
        s = 1 / np.sqrt(m)
        At = s[:, None] * K * s[None, :]
        lam, U = np.linalg.eigh(At); lam = np.clip(lam, 0, None)
        E0 = 0.5 * (np.sum(m * v0 ** 2) + x0 @ K @ x0)
        _, _, _, _, u, w = exact(K, m, gh, th, x0, v0)
        u0, w0 = U.T @ (np.sqrt(m) * x0), U.T @ (np.sqrt(m) * v0)
        h = np.exp(-th * lam / (2 * gh))
        uh = h * (u0 + w0 / (2 * gh)); wh = -lam / (2 * gh) * uh
        dist = np.sqrt(np.sum(lam * (u - uh) ** 2 + (w - wh) ** 2))
        bound = 0.47 / (gh * th) * np.sqrt(2 * E0)
        good = e1 < 1e-9 and abs(pw - xe[j]) < 4 * np.sqrt(1 / W) and abs(hw - hx) < 4 * np.sqrt(1 / W) * np.abs(y0).max() and dist <= bound
        ok &= good
        print(f"trial {trial}: Poisson series vs exact {e1:.1e}; node {j}: exact {xe[j]:+.4f} Poisson walk {pw:+.4f}; "
              f"g={gh}, t={th}: exact {xe2[j]:+.4f} heat {hx:+.4f} heat walk {hw:+.4f}; "
              f"energy distance {dist:.4f} <= bound {bound:.4f}: {good}")
    print("all checks passed" if ok else "SOME CHECK FAILED")
