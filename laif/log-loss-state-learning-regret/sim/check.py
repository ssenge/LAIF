"""Checks for the note on the minimax regret of online learning of quantum states (README.md).

1. The volume formula for the state set, against the ball of qubit states (d = 2) and a sampled count (d = 3).
2. Linear inversion with uniform rank-one outcomes is unbiased with second moment (d + 1) k / d per round.
3. The constants of Theorem 1: c_d and C_d = exp(2 c_d / k) / d^3, decreasing over every d <= 10^5.
4. A plug-in learner on d = 2 against the best state in hindsight, versus the lower bound.
5. The uniform-prior mixture on d = 2 stays below the bound log C(T + k, k) of [1, Theorem 4.5].
"""
import math

import numpy as np

rng = np.random.default_rng(7)


def log_volume(d):
    """log of the flat volume of the d x d density matrices (trace-norm-2 metric on traceless part)."""
    return (0.5 * math.log(d) + d * (d - 1) / 2 * math.log(2 * math.pi)
            + sum(math.lgamma(j) for j in range(1, d + 1)) - math.lgamma(d * d))


def c_const(d):
    k = d * d - 1
    return k / 2 * math.log(2 * math.pi * math.e * (d + 1) / d) - log_volume(d)


def lower_bound(d, T):
    return (d * d - 1) / 2 * math.log(T) - c_const(d)


def herm_basis(d):
    """Orthonormal basis (trace inner product) of the traceless self-adjoint matrices."""
    B = []
    for i in range(d):
        for j in range(i + 1, d):
            E = np.zeros((d, d), complex); E[i, j] = E[j, i] = 1 / math.sqrt(2); B.append(E)
            E = np.zeros((d, d), complex); E[i, j] = -1j / math.sqrt(2); E[j, i] = 1j / math.sqrt(2); B.append(E)
    for m in range(1, d):
        E = np.zeros((d, d), complex)
        E[np.arange(m), np.arange(m)] = 1
        E[m, m] = -m
        B.append(E / math.sqrt(m * (m + 1)))
    return np.array(B)


def check_volume():
    v2 = math.exp(log_volume(2))
    ball = 4 / 3 * math.pi * (1 / math.sqrt(2)) ** 3
    assert abs(v2 - ball) < 1e-12
    print(f"1. d=2: volume {v2:.6f}, ball of qubit states, radius 1/sqrt2 {ball:.6f}")
    d, B = 3, herm_basis(3)
    R = math.sqrt(1 - 1 / d)  # every state is within this distance of I/d
    hits, n = 0, 0
    for _ in range(40):
        x = rng.uniform(-R, R, (250000, 8))
        rho = np.eye(d) / d + np.tensordot(x, B, axes=1)
        hits += int(np.sum(np.linalg.eigvalsh(rho)[:, 0] >= 0)); n += len(x)
    est = hits / n * (2 * R) ** 8
    se = est / math.sqrt(hits)
    exact = math.exp(log_volume(3))
    assert abs(est - exact) < 4 * se
    print(f"   d=3: sampled {est:.5f} +- {se:.5f}, formula {exact:.5f}")


def unit_vectors(n, d):
    g = rng.normal(size=(n, d)) + 1j * rng.normal(size=(n, d))
    return g / np.linalg.norm(g, axis=1, keepdims=True)


def sample_outcomes(rho, n):
    """Unit vectors with density d <v|rho|v> with respect to the uniform measure (rejection)."""
    lmax = np.linalg.eigvalsh(rho)[-1]
    out = []
    while sum(len(o) for o in out) < n:
        v = unit_vectors(4 * n, len(rho))
        p = np.einsum("ni,ij,nj->n", v.conj(), rho, v).real
        out.append(v[rng.random(len(v)) < p / lmax])
    return np.concatenate(out)[:n]


def random_state(d):
    """A state from the flat measure: G G^* / tr with G a square matrix of complex normal entries."""
    g = rng.normal(size=(d, d)) + 1j * rng.normal(size=(d, d))
    r = g @ g.conj().T
    return r / np.trace(r).real


def check_inversion():
    print("2. linear inversion (d + 1) v v^* - I:")
    for d in [2, 3, 5]:
        rho = random_state(d)
        n = 200000
        v = sample_outcomes(rho, n)
        X = (d + 1) * np.einsum("ni,nj->nij", v, v.conj()) - np.eye(d)
        mean = X.mean(axis=0)
        err = np.linalg.norm(mean - rho)
        second = np.mean(np.sum(np.abs(X - rho) ** 2, axis=(1, 2)))
        pred = d * d + d - 1 - np.trace(rho @ rho).real
        assert err < 6 * math.sqrt(pred / n) and abs(second - pred) < 0.01 * pred
        assert pred <= (d + 1) * (d * d - 1) / d + 1e-12
        print(f"   d={d}: |mean - rho| = {err:.4f}, second moment {second:.3f} vs {pred:.3f}"
              f" <= (d+1)k/d = {(d + 1) * (d * d - 1) / d:.3f}")


def check_constants():
    print("3. c_d and C_d = exp(2 c_d / k) / d^3 for every d <= 10^5:")
    lg, prev = 0.0, math.inf  # lg: running sum of log Gamma(j), j <= d
    for d in range(1, 100001):
        lg += math.lgamma(d)
        if d < 2:
            continue
        k = d * d - 1
        logv = 0.5 * math.log(d) + d * (d - 1) / 2 * math.log(2 * math.pi) + lg - math.lgamma(d * d)
        c = k / 2 * math.log(2 * math.pi * math.e * (d + 1) / d) - logv
        C = math.exp(2 * c / k) / d ** 3
        assert C < prev
        prev = C
        if d in (2, 3, 5, 10, 50, 400, 2000, 100000):
            assert abs(logv - log_volume(d)) <= 1e-9 * abs(logv)
            print(f"   d={d:6d}: c_d = {c:15.3f}, C_d = {C:.6f}, e^(1/2)(1 + 1/d) = {math.exp(0.5) * (1 + 1 / d):.6f}")
    assert math.exp(2 * c_const(2) / 3) / 8 < 2.47
    print("   C_d is strictly decreasing and C_2 < 2.47")


def mle(A, iters=400):
    """Best fixed state for the losses -log <v|rho|v> (diluted fixed-point iteration)."""
    d = A.shape[1]
    rho = np.eye(d) / d
    for _ in range(iters):
        p = np.einsum("ni,ij,nj->n", A.conj(), rho, A).real
        R = np.einsum("ni,nj->ij", A / p[:, None], A.conj()) / len(A)
        M = 0.5 * (np.eye(d) + R)
        rho = M @ rho @ M
        rho /= np.trace(rho).real
    p = np.einsum("ni,ij,nj->n", A.conj(), rho, A).real
    return -np.sum(np.log(p))


def plugin_regret(d, T, rho):
    v = sample_outcomes(rho, T)
    S = np.zeros((d, d), complex)
    loss = 0.0
    for t in range(T):
        est = (d + 1) * S / max(t, 1) - (np.eye(d) if t else 0)
        w, U = np.linalg.eigh(est if t else np.eye(d) / d)
        w = np.clip(w, 0, None); w = w / w.sum() if w.sum() > 0 else np.ones(d) / d
        lam = d / (d + t + 1)  # mix towards I/d so that no outcome has probability 0
        r = (1 - lam) * (U * w) @ U.conj().T + lam * np.eye(d) / d
        loss -= math.log(np.real(v[t].conj() @ r @ v[t]))
        S += np.outer(v[t], v[t].conj())
    return loss - mle(v)


def check_learner():
    print("4. plug-in learner on d = 2, mean regret over random states vs Theorem 1:")
    for T in [100, 1000, 5000]:
        regs = [plugin_regret(2, T, random_state(2)) for _ in range(40 if T < 5000 else 12)]
        m, s = float(np.mean(regs)), float(np.std(regs) / math.sqrt(len(regs)))
        lb = lower_bound(2, T)
        assert m + 3 * s >= lb
        print(f"   T={T:5d}: regret {m:7.3f} +- {s:.3f}, lower bound {lb:7.3f}")


def mixture_regret(A, ngrid=60):
    """Regret of the uniform-prior mixture on d = 2, by quadrature over the ball of qubit states."""
    s = np.array([[[0, 1], [1, 0]], [[0, -1j], [1j, 0]], [[1, 0], [0, -1]]])
    g = (np.arange(ngrid) + 0.5) / ngrid * 2 - 1
    X, Y, Z = np.meshgrid(g, g, g, indexing="ij")
    keep = X ** 2 + Y ** 2 + Z ** 2 <= 1
    r = np.stack([X[keep], Y[keep], Z[keep]], 1)
    # <v|rho|v> = (1 + r . n(v)) / 2 with n(v) the coordinate vector of v
    n = np.real(np.einsum("ti,kij,tj->tk", A.conj(), s, A))
    ll = np.log((1 + r @ n.T) / 2).sum(axis=1)
    top = ll.max()
    mix = top + math.log(np.mean(np.exp(ll - top)))
    return -mix - mle(A)


def check_mixture():
    print("5. uniform-prior mixture on d = 2 against log C(T + k, k):")
    k = 3
    for T in [50, 200, 1000]:
        worst = 0.0
        for kind in ["random", "basis", "state"]:
            if kind == "random":
                A = unit_vectors(T, 2)
            elif kind == "basis":
                A = np.eye(2, dtype=complex)[rng.integers(0, 2, T)]
            else:
                A = sample_outcomes(random_state(2), T)
            worst = max(worst, mixture_regret(A))
        ub = math.log(math.comb(T + k, k))
        assert worst <= ub
        print(f"   T={T:5d}: largest regret {worst:6.3f}, bound {ub:6.3f}, lower bound {lower_bound(2, T):6.3f}")


if __name__ == "__main__":
    check_volume()
    check_inversion()
    check_constants()
    check_learner()
    check_mixture()
    print("all checks passed")
