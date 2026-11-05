#!/usr/bin/env python3
"""Checks the optimization side of ../README.md (Case 1: smooth components, strongly convex regularizer).

1. Lemma 1: with the constants of Section 2, F(0) - F* <= Delta, and every x with |<x, v_t>| < c/2 for some chain
   vector v_t has F(x) - F* > 3 eps (checked by minimizing one chain with that coordinate pinned to +-c/2).
2. Each component is convex and 1-smooth (largest Hessian eigenvalue <= 1 on random points).
   Remark 2: with the constants printed in Lemma 5 of [1], F(0) - F* is n Delta.
3. Lemma 4: the gradient of a component at a query x of norm <= R is computed exactly from x and the keys that the
   discrete oracle reveals for the candidate sets S_j(x), and sum_j |S_j(x)| < 4 R^2 / c^2.
"""
import numpy as np
from scipy.optimize import minimize


def phi(z, c):
    a = np.abs(z)
    return np.where(a <= c, 0.0, np.where(a <= 2 * c, 2 * (a - c) ** 2, z * z - 2 * c * c))


def dphi(z, c):
    a = np.abs(z)
    return np.where(a <= c, 0.0, np.where(a <= 2 * c, 4 * (a - c) * np.sign(z), 2 * z))


def d2phi(z, c):
    a = np.abs(z)
    return np.where(a <= c, 0.0, np.where(a <= 2 * c, 4.0, 2.0))


def constants(n, kappa, Delta, eps):
    """l = 1. Returns the instance constants of Section 2, or None if k < 1."""
    mu = 1 / kappa
    mt = n * mu
    Q = (1 / mt + 1) / 2
    q = (np.sqrt(Q) - 1) / (np.sqrt(Q) + 1)
    N = n // 2
    a = (1 - mt) / (16 * n)
    # largest k with q^(2k+1) > 3 eps / (mu Delta)
    k = int(np.ceil((np.log(mu * Delta / (3 * eps)) / np.log(1 / q) - 1) / 2)) - 1
    if k < 1:
        return None
    assert q ** (2 * k + 1) > 3 * eps / (mu * Delta) >= q ** (2 * k + 3)
    C = np.sqrt(Delta / (2 * N * a * q))
    c = C * q ** (k + 1) * np.sqrt(mt / (2 * (k + 1)))
    return dict(n=n, N=N, mu=mu, mt=mt, Q=Q, q=q, zeta=1 - q, a=a, k=k, C=C, c=c, eps=eps, Delta=Delta)


def chain_value(y, p):
    """Share of F carried by one chain: a [y0^2 - 2 C y0 + sum phi(y_{r-1} - y_r) + zeta phi(y_k)] + mu/2 |y|^2."""
    a, c = p['a'], p['c']
    d = y[:-1] - y[1:]
    val = a * (y[0] ** 2 - 2 * p['C'] * y[0] + phi(d, c).sum() + p['zeta'] * phi(y[-1], c)) + p['mu'] / 2 * y @ y
    g = p['mu'] * y.copy()
    gd = a * dphi(d, c)
    g[:-1] += gd
    g[1:] -= gd
    g[0] += a * (2 * y[0] - 2 * p['C'])
    g[-1] += a * p['zeta'] * dphi(y[-1], c)
    return val, g


def chain_min(p, pin=None):
    k = p['k']
    free = [r for r in range(k + 1) if pin is None or r != pin[0]]

    def full(z):
        y = np.empty(k + 1)
        y[free] = z
        if pin is not None:
            y[pin[0]] = pin[1]
        return y

    def f(z):
        v, g = chain_value(full(z), p)
        return v, g[free]

    y0 = p['C'] * p['q'] ** np.arange(1, k + 2)
    r = minimize(f, y0[free], jac=True, method='L-BFGS-B',
                 options=dict(ftol=1e-16, gtol=1e-14, maxiter=200000, maxcor=50))
    assert np.abs(r.jac).max() < 1e-7, np.abs(r.jac).max()  # value error <= |grad|^2 / mu, far below eps
    return r.fun, full(r.x)


def check_lemma1():
    for n, kappa, eps in [(2, 200, 1e-4), (2, 800, 1e-6), (4, 1600, 1e-6), (6, 600, 1e-5), (2, 3200, 1e-7)]:
        p = constants(n, kappa, 1.0, eps)
        Gs, ys = chain_min(p)
        gap0 = p['N'] * (0 - Gs)  # F(0) - F*, all chains equal, the rest of x is 0 at the optimum
        assert gap0 <= p['Delta'] + 1e-12, gap0
        bound = 0.41 * p['mu'] * p['C'] ** 2 * p['q'] ** (2 * p['k'] + 2)
        assert bound > 3 * eps
        worst = min(min(chain_min(p, (t, s * p['c'] / 2))[0] for s in (1, -1)) - Gs for t in range(p['k'] + 1))
        assert worst >= bound * (1 - 1e-9) and worst > 3 * eps, (worst, bound)
        print(f"n={n} kappa={kappa} eps={eps:g}: k={p['k']}, c={p['c']:.2e}, F(0)-F*={gap0:.4f} <= 1, "
              f"min gap with one |y_t| <= c/2: {worst:.3e} >= bound {bound:.3e} > 3 eps")


def check_remark():
    """Remark 2: with the constant C of Lemma 5 of [1], F(0) - F* is about n Delta."""
    for n, kappa, eps in [(2, 800, 1e-6), (4, 1600, 1e-6), (8, 1600, 1e-6)]:
        p = constants(n, kappa, 1.0, eps)
        Q = p['Q']
        p['k'] = int(np.floor((np.sqrt(Q) - 1) / 4 * np.log(1 / (n * eps * (np.sqrt(Q) - 1) ** 2)))) - 1
        p['C'] = np.sqrt(1 / p['mu']) * 4 / (np.sqrt(Q) - 1)
        p['c'] = min(1.0, np.sqrt(8 * n * eps / ((1 - p['mt']) * (p['k'] + 1))), p['C'] * p['q'] ** (p['k'] + 1))
        gap0 = p['N'] * (0 - chain_min(p)[0])
        assert abs(gap0 / n - 1) < 1e-3, gap0
        print(f"constants of [1], n={n}, Delta=1: F(0)-F* = {gap0:.4f}")


def components(p, V, x):
    """Values, gradients and Hessians of f_{1}, f_{2} of one chain with orthonormal columns V = [v_0 ... v_k]."""
    a16 = (1 - p['mt']) / 16
    y = V.T @ x
    k, c = p['k'], p['c']
    out = []
    for part in (1, 2):
        g = np.zeros_like(x)
        H = np.zeros((len(x), len(x)))
        if part == 1:
            g += (2 * y[0] - 2 * p['C']) * V[:, 0]
            H += 2 * np.outer(V[:, 0], V[:, 0])
        else:
            g += p['zeta'] * dphi(y[k], c) * V[:, k]
            H += p['zeta'] * d2phi(y[k], c) * np.outer(V[:, k], V[:, k])
        for r in range(1, k + 1):
            if r % 2 == (0 if part == 1 else 1):
                w = V[:, r - 1] - V[:, r]
                z = y[r - 1] - y[r]
                g += dphi(z, c) * w
                H += d2phi(z, c) * np.outer(w, w)
        out.append((a16 * g, a16 * H))
    return out


def check_smoothness(rng):
    p = constants(2, 800, 1.0, 1e-6)
    k = p['k']
    V = np.linalg.qr(rng.normal(size=(k + 8, k + 1)))[0]
    worst = 0.0
    for _ in range(2000):
        x = V @ (p['c'] * rng.normal(size=k + 1) * rng.choice([0.3, 1, 3]))
        for _, H in components(p, V, x):
            ev = np.linalg.eigvalsh(H)
            assert ev.min() > -1e-12
            worst = max(worst, ev.max())
    assert worst <= 1
    print(f"components convex, largest Hessian eigenvalue seen {worst:.3f} <= 1 (k={k})")


def check_simulation(rng):
    """Lemma 3 on small instances: A candidates per chain position, true keys m, query x of norm <= R."""
    p = constants(2, 200, 1.0, 1e-4)
    k, c = p['k'], p['c']
    A, chains = 6, 2
    d = chains * (k + 1) * A + 20
    U = np.linalg.qr(rng.normal(size=(d, d)))[0][:, :chains * (k + 1) * A].reshape(d, chains, k + 1, A)
    R = 4 * c * np.sqrt(k)
    worst = 0
    for trial in range(3000):
        m = rng.integers(A, size=(chains, k + 1))
        # a query that correlates with a random handful of candidates, true or false, plus noise
        x = np.zeros(d)
        for _ in range(rng.integers(1, 2 * k)):
            ch, j, al = rng.integers(chains), rng.integers(k + 1), rng.integers(A)
            x += rng.choice([-1, 1]) * rng.uniform(0.3, 3) * c * U[:, ch, j, al]
        x += 0.3 * c * rng.normal(size=d) / np.sqrt(d)
        if np.linalg.norm(x) > R:
            x *= R / np.linalg.norm(x)
        ch = rng.integers(chains)
        V = U[:, ch, np.arange(k + 1), m[ch]]
        true = [g for g, _ in components(p, V, x)]
        # candidate sets and the keys the discrete oracle reveals
        S = [set(np.flatnonzero(np.abs(U[:, ch, j, :].T @ x) > c / 2)) for j in range(k + 1)]
        size = sum(len(s) for s in S)
        all_sizes = (np.abs(np.tensordot(x, U, axes=(0, 0))) > c / 2).sum()
        assert all_sizes < 4 * (x @ x) / c ** 2 + 1e-9
        worst = max(worst, size)
        hit = [m[ch, j] in S[j] for j in range(k + 1)]
        revealed = [j == 0 or any(hit[t] for t in (j - 1, j, j + 1) if 0 <= t <= k) for j in range(k + 1)]
        # rebuild the gradient from revealed keys only: a term is used iff all of its vectors are revealed
        a16 = (1 - p['mt']) / 16
        y = {j: U[:, ch, j, m[ch, j]] @ x for j in range(k + 1) if revealed[j]}
        vv = {j: U[:, ch, j, m[ch, j]] for j in y}
        sim = [a16 * (2 * y[0] - 2 * p['C']) * vv[0], np.zeros(d)]
        if k in y:
            sim[1] += a16 * p['zeta'] * dphi(y[k], c) * vv[k]
        for r in range(1, k + 1):
            if r - 1 in y and r in y:
                sim[0 if r % 2 == 0 else 1] += a16 * dphi(y[r - 1] - y[r], c) * (vv[r - 1] - vv[r])
        for t, s in zip(true, sim):
            assert np.allclose(t, s, atol=1e-14), np.abs(t - s).max()
    print(f"gradient simulation exact on 3000 queries (k={k}, A={A}), largest candidate set total {worst}")


def main():
    rng = np.random.default_rng(8)
    check_lemma1()
    check_remark()
    check_smoothness(rng)
    check_simulation(rng)


if __name__ == "__main__":
    main()
