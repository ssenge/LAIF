#!/usr/bin/env python3
"""Checks Theorems 1 and 2 of ../README.md on small dense instances of the free fermion stacked LCU.

A = L_l ... L_1 with L_j = sum_i a^j_i U_ji, a^j in the simplex, and U_ji = e^{i alpha} times a product of Gaussian
generators exp(t/2 c_p c_q). The unnormalised loss is m = <0| A^dag O A |0>. Expanding the product,
m = E_{a,b} <0| U_b^dag O U_a |0>, with the layer indices of a and b drawn independently from the a^j.

1. The sampled estimator is unbiased, and its error after N samples obeys the Hoeffding bound.
2. The sampled estimators of d m / d a^j_i and of d m / d t (one generator angle) are unbiased.
3. E[p_s] = (2/(k+1))^l for Dirichlet coefficients and independent uniform phases, where p_s = <0|A^dag A|0>.
The dense matrices only stand in for the O(n^3) phased Gaussian routines; the estimator is the same.
"""
import numpy as np
from scipy.linalg import expm

X, Y, Z, I2 = (np.array(m, dtype=complex) for m in ([[0, 1], [1, 0]], [[0, -1j], [1j, 0]], [[1, 0], [0, -1]], np.eye(2)))


def kron_all(ms):
    out = np.array([[1.0 + 0j]])
    for m in ms:
        out = np.kron(out, m)
    return out


def majoranas(n):
    cs = []
    for j in range(n):
        pre = [Z] * j
        post = [I2] * (n - j - 1)
        cs += [kron_all(pre + [X] + post), kron_all(pre + [Y] + post)]
    return cs


def random_gaussian(cs, g, rng):
    """(phase, list of generators (p, q, t)) and the dense unitary."""
    alpha = rng.uniform(0, 2 * np.pi)
    gens = [(*rng.choice(len(cs), 2, replace=False), rng.uniform(0, 2 * np.pi)) for _ in range(g)]
    U = np.exp(1j * alpha) * np.eye(cs[0].shape[0], dtype=complex)
    for p, q, t in gens:
        U = expm(t / 2 * cs[p] @ cs[q]) @ U
    return U, alpha, gens


def build(n, k, l, g, rng):
    cs = majoranas(n)
    Us = [[random_gaussian(cs, g, rng) for _ in range(k)] for _ in range(l)]
    a = [rng.dirichlet(np.ones(k)) for _ in range(l)]
    return cs, Us, a


def apply_path(Us, idx, psi):
    for j, i in enumerate(idx):
        psi = Us[j][i][0] @ psi
    return psi


def exact_m(Us, a, O, psi0):
    phi = psi0
    for j in range(len(Us)):
        phi = sum(a[j][i] * Us[j][i][0] @ phi for i in range(len(a[j])))
    return np.vdot(phi, O @ phi).real, np.vdot(phi, phi).real


def estimate(Us, a, O, psi0, N, rng):
    l, k = len(a), len(a[0])
    vals = np.empty(N)
    for s in range(N):
        ia = [rng.choice(k, p=a[j]) for j in range(l)]
        ib = [rng.choice(k, p=a[j]) for j in range(l)]
        vals[s] = np.vdot(apply_path(Us, ib, psi0), O @ apply_path(Us, ia, psi0)).real
    return vals


def check_estimator(rng):
    n, k, l, g = 4, 3, 3, 6
    cs, Us, a = build(n, k, l, g, rng)
    O = -1j * cs[0] @ cs[1]  # Z_1, with ||h||_1 = 1
    psi0 = np.zeros(2 ** n, dtype=complex)
    psi0[0] = 1
    m, ps = exact_m(Us, a, O, psi0)
    vals = estimate(Us, a, O, psi0, 200000, rng)
    assert np.abs(vals).max() <= 1 + 1e-12
    z = (vals.mean() - m) / (vals.std() / np.sqrt(len(vals)))
    assert abs(z) < 4.5, z
    # Hoeffding: N = 2 ln(2/delta) / eps^2 samples give |error| <= eps with probability >= 1 - delta
    eps, delta = 0.05, 0.05
    N = int(np.ceil(2 * np.log(2 / delta) / eps ** 2))
    fails = sum(abs(estimate(Us, a, O, psi0, N, rng).mean() - m) > eps for _ in range(200))
    assert fails <= 0.05 * 200 + 10, fails
    print(f"n={n} k={k} l={l}: m = {m:+.5f}, p_s = {ps:.4f}, mean of 2e5 samples {vals.mean():+.5f} (z = {z:+.2f}); "
          f"{fails}/200 runs with N = {N} missed eps = {eps}")
    return cs, Us, a, O, psi0


def check_gradients(cs, Us, a, O, psi0, rng):
    l, k = len(a), len(a[0])
    # coefficient derivative d m / d a^j_i (a^j treated as free variables): fix the index of one side to i
    j, i = 1, 2
    h = 1e-6
    ap = [x.copy() for x in a]
    ap[j][i] += h
    am = [x.copy() for x in a]
    am[j][i] -= h
    fd = (exact_m(Us, ap, O, psi0)[0] - exact_m(Us, am, O, psi0)[0]) / (2 * h)
    vals = []
    for _ in range(100000):
        ia = [rng.choice(k, p=a[t]) for t in range(l)]
        ib = [rng.choice(k, p=a[t]) for t in range(l)]
        ia[j] = i
        vals.append(2 * np.vdot(apply_path(Us, ib, psi0), O @ apply_path(Us, ia, psi0)).real)
    vals = np.array(vals)
    z = (vals.mean() - fd) / (vals.std() / np.sqrt(len(vals)))
    assert abs(z) < 4.5, z
    print(f"d m / d a^{j}_{i}: finite difference {fd:+.5f}, sampled {vals.mean():+.5f} (z = {z:+.2f})")
    # angle derivative of the first generator of U_{j,i}: insert (1/2) c_p c_q after that generator
    U, alpha, gens = Us[j][i]
    p, q, t = gens[0]

    def unitary(t0):
        V = np.exp(1j * alpha) * np.eye(U.shape[0], dtype=complex)
        for s, (pp, qq, tt) in enumerate(gens):
            V = expm((t0 if s == 0 else tt) / 2 * cs[pp] @ cs[qq]) @ V
        return V

    def m_with(V):
        Us2 = [row[:] for row in Us]
        Us2[j] = Us[j][:]
        Us2[j][i] = (V, alpha, gens)
        return exact_m(Us2, a, O, psi0)[0]

    fd = (m_with(unitary(t + h)) - m_with(unitary(t - h))) / (2 * h)
    dU = np.exp(1j * alpha) * np.eye(U.shape[0], dtype=complex)
    for s, (pp, qq, tt) in enumerate(gens):
        G = expm(tt / 2 * cs[pp] @ cs[qq])
        dU = (G @ (0.5 * cs[pp] @ cs[qq]) if s == 0 else G) @ dU
    vals = []
    for _ in range(100000):
        ia = [rng.choice(k, p=a[s]) for s in range(l)]
        ib = [rng.choice(k, p=a[s]) for s in range(l)]
        ia[j] = i
        phi = psi0
        for s, r in enumerate(ia):
            phi = (dU if s == j else Us[s][r][0]) @ phi
        vals.append(2 * a[j][i] * np.vdot(apply_path(Us, ib, psi0), O @ phi).real)
    vals = np.array(vals)
    assert np.abs(vals).max() <= 2 * a[j][i] * 0.5 + 1e-12
    z = (vals.mean() - fd) / (vals.std() / np.sqrt(len(vals)))
    assert abs(z) < 4.5, z
    print(f"d m / d t (generator angle in U_{j}{i}): finite difference {fd:+.5f}, sampled {vals.mean():+.5f} (z = {z:+.2f})")


def check_ps(rng):
    n, k, l, g = 3, 3, 2, 4
    psi0 = np.zeros(2 ** n, dtype=complex)
    psi0[0] = 1
    vals = [exact_m(*build(n, k, l, g, rng)[1:], np.eye(2 ** n), psi0)[1] for _ in range(20000)]
    target = (2 / (k + 1)) ** l
    z = (np.mean(vals) - target) / (np.std(vals) / np.sqrt(len(vals)))
    assert abs(z) < 4.5, z
    print(f"E[p_s] for k={k}, l={l}: sampled {np.mean(vals):.4f}, (2/(k+1))^l = {target:.4f} (z = {z:+.2f})")


def main():
    rng = np.random.default_rng(3)
    inst = check_estimator(rng)
    check_gradients(*inst, rng)
    check_ps(rng)


if __name__ == "__main__":
    main()
