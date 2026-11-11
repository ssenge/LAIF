# Phase algorithm on the ball (Theorem 2 of NOTES.md), simulated with the exact output law of amplitude estimation.
# Usage: python regret_ball.py d_list T_list [runs] [K]
import sys
import numpy as np

H = 5


def ae_sample(mu, M, rng, size):
    """size outputs of amplitude estimation with register M on mean mu (exact output distribution)."""
    th = np.arcsin(np.sqrt(min(max(mu, 0.0), 1.0))) / np.pi
    y = np.arange(M)

    def fejer(dl):
        s = np.sin(np.pi * dl)
        out = np.ones_like(dl)
        nz = np.abs(s) > 1e-15
        out[nz] = np.sin(M * np.pi * dl[nz]) ** 2 / (M * M * s[nz] ** 2)
        return out

    p = 0.5 * (fejer(y / M - th) + fejer(y / M + th))
    p /= p.sum()
    return np.sin(np.pi * rng.choice(M, size=size, p=p) / M) ** 2


def estimate(mu, M, rng):
    """median of H runs; returns (estimate, queries)."""
    return float(np.median(ae_sample(mu, M, rng, H))), H * (2 * M - 1)


def run(d, T, rng, K):
    th = rng.normal(size=d)
    th *= rng.uniform(0.05, 1.0) / np.linalg.norm(th)       # |theta| in [0.05, 1]
    nth = np.linalg.norm(th)
    mu = lambda x: (1 + x @ th) / 2
    reg = lambda x: (nth - x @ th) / 2
    used, regret, a, est = 0, 0.0, 1.0, None
    while used < T:
        if est is None or np.linalg.norm(est) == 0:
            c, s = np.eye(d)[0], 1.0
        else:
            c, s = est / np.linalg.norm(est), min(1.0, a / np.linalg.norm(est))
        M = int(np.ceil(K * np.sqrt(d) / (s * a)))
        Q = np.linalg.qr(np.column_stack([c, rng.normal(size=(d, d - 1))]))[0]
        U = Q[:, 1:]
        U -= np.outer(c, c @ U)
        U /= np.linalg.norm(U, axis=0)
        new = np.zeros(d)
        for j, x in enumerate([c] + [v for u in U.T for v in (np.cos(s) * c + np.sin(s) * u, np.cos(s) * c - np.sin(s) * u)]):
            e, q = estimate(mu(x), M, rng)
            q = min(q, T - used)
            used += q
            regret += q * reg(x)
            if used >= T:
                return regret, nth
            if j == 0:
                new += (2 * e - 1) * c
            elif j % 2 == 1:
                ep = e
            else:
                new += (ep - e) / np.sin(s) * U[:, (j - 1) // 2]
        est, a = new, a / 2
    return regret, nth


if __name__ == "__main__":
    runs = int(sys.argv[3]) if len(sys.argv) > 3 else 5
    K = float(sys.argv[4]) if len(sys.argv) > 4 else 30.1
    rng = np.random.default_rng(1)
    for d in [int(v) for v in sys.argv[1].split(",")]:
        for T in [int(float(v)) for v in sys.argv[2].split(",")]:
            R = np.array([run(d, T, rng, K)[0] for _ in range(runs)])
            bound = (6923 * d ** 1.5 + 25 * d) * (np.log2(T) + 1)
            assert R.max() <= bound
            print(f"K={K} d={d:3d} T={T:.0e} regret mean {R.mean():10.1f} max {R.max():10.1f}  "
                  f"mean/(d^1.5 ln T) {R.mean() / (d ** 1.5 * np.log(T)):7.2f}  (Theorem 2 bound {bound:.3g})", flush=True)
