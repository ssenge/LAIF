"""Checks Lemma 1: for K(x,x') = p_0 + sum_i p_i cos(<w_i, x - x'>) and every input law P,
max(p_0, max_i p_i / 2) <= ||T_K|| <= 1, with equality on the uniform law of the torus for
integer frequencies. For an empirical law P_m on points x_1..x_m, ||T_K|| = lambda_max(K / m).
"""
import itertools
import numpy as np


def kernel(X, W, p0, p):
    G = X @ W.T  # (m, k)
    C, S = np.cos(G), np.sin(G)
    return p0 + (C * p) @ C.T + (S * p) @ S.T


def opnorm(X, W, p0, p):
    return np.linalg.eigvalsh(kernel(X, W, p0, p) / len(X))[-1]


def weights(k, rng, peaked):
    q = rng.exponential(size=k + 1) ** (6 if peaked else 1)
    q /= q.sum()
    return q[0], q[1:]


def encoder(X, rng, width=16, out=3):
    """A random two-layer tanh network, scaled to angles."""
    A = rng.normal(size=(X.shape[1], width))
    B = rng.normal(size=(width, out))
    return np.pi * np.tanh(np.tanh(X @ A) @ B)


def check(rng):
    d, k, m = 3, 40, 400
    worst = np.inf
    laws = {
        "uniform": lambda: rng.uniform(-np.pi, np.pi, size=(m, d)),
        "two points": lambda: np.repeat(rng.normal(size=(2, d)), m // 2, axis=0),
        "gaussian, small": lambda: 0.05 * rng.normal(size=(m, d)),
        "encoder pushforward": lambda: encoder(rng.normal(size=(m, 5)), rng),
        "encoder, collapsed": lambda: encoder(0.01 * rng.normal(size=(m, 5)), rng),
    }
    for integer in (True, False):
        for peaked in (False, True):
            for name, law in laws.items():
                for _ in range(5):
                    W = rng.integers(-4, 5, size=(k, d)) if integer else 3 * rng.normal(size=(k, d))
                    p0, p = weights(k, rng, peaked)
                    lo = max(p0, p.max() / 2)
                    t = opnorm(law(), W, p0, p)
                    assert lo - 1e-9 <= t <= 1 + 1e-9, (name, lo, t)
                    worst = min(worst, t / lo)
    print(f"lower bound max(p0, pmax/2) <= ||T_K|| <= 1 on {2 * 2 * len(laws) * 5} cases; "
          f"smallest ratio ||T_K|| / bound = {worst:.4f}")


def check_equality(rng):
    """Uniform law on the torus, integer frequencies: exact grid quadrature gives equality."""
    d, n = 2, 12
    grid = np.array(list(itertools.product(2 * np.pi * np.arange(n) / n, repeat=d)))
    W = np.array([[1, 0], [0, 1], [1, 1], [2, -1], [3, 2]])
    for _ in range(5):
        p0, p = weights(len(W), rng, peaked=True)
        t = opnorm(grid, W, p0, p)
        assert abs(t - max(p0, p.max() / 2)) < 1e-12
    print("uniform law on the torus, integer frequencies: ||T_K|| = max(p0, pmax/2) exactly")


if __name__ == "__main__":
    rng = np.random.default_rng(11)
    check(rng)
    check_equality(rng)
    print("Lemma 1 checks pass")
