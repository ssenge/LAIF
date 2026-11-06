"""Checks for the tightness of the spectral capacity bound for single-qubit data reuploaders.

Model: U(x) = W_R e^{-ixZ} W_{R-1} ... e^{-ixZ} W_0, f(x) = B <0|U^dag Z U|0>, frequencies 2j, |j| <= R.
1. Realizability: every real F(x) = sum_{|j|<=R} c_j e^{2ijx} with |F| <= 1 is f/B for some blocks
   (factorization of nonnegative trigonometric polynomials, then layer stripping).
2. Lower bound: on R + 1 equispaced nodes with n/(R + 1) samples each, kernel interpolants realize every
   sign pattern with amplitude B, so the empirical Rademacher complexity is >= B sqrt((R + 1)/(2n)).
"""
import numpy as np


def factor(c):
    """g(w) = sum_{|j|<=R} c_j w^j >= 0 on |w| = 1 -> polynomial p of degree R with |p(w)|^2 = g(w)."""
    R = (len(c) - 1) // 2
    if R == 0:
        return np.array([np.sqrt(max(np.real(c[0]), 0))], complex)
    r = R
    while r > 0 and abs(c[R + r]) < 1e-12:  # true degree r <= R; pad the factor with zeros
        r -= 1
    if r < R:
        return np.concatenate([factor(c[R - r:R + r + 1]), np.zeros(R - r)])
    roots = np.roots(c[::-1])  # w^R g(w), coefficients from highest power
    inside = roots[np.argsort(np.abs(roots))][:R]  # one root of each reciprocal pair
    p = np.poly(inside)[::-1]  # coefficients of prod (w - r), lowest power first
    w = np.exp(1j * 0.3)
    scale = np.sqrt(np.real(np.polyval(c[::-1], w) / w ** R) / abs(np.polyval(p[::-1], w)) ** 2)
    return p * scale


def target(R, rng):
    """A random real trigonometric polynomial in y = 2x of degree R with sup norm < 1."""
    c = rng.normal(size=R + 1) + 1j * rng.normal(size=R + 1)
    c[0] = rng.normal()
    full = np.concatenate([np.conj(c[:0:-1]), c])  # c_{-R} .. c_R
    ys = np.linspace(0, 2 * np.pi, 4096, endpoint=False)
    vals = np.real(np.exp(1j * np.outer(ys, np.arange(-R, R + 1))) @ full)
    return full / (np.max(np.abs(vals)) * 1.05)


def laurent_matrix(F):
    """U(z) with U_00 = z^-R p(z^2), U_10 = z^-R q(z^2); coefficients C[k] of z^(k - R), k = 0..2R."""
    R = (len(F) - 1) // 2
    one = np.zeros(2 * R + 1, complex)
    one[R] = 1
    p = factor((one + F) / 2)
    q = factor((one - F) / 2)
    C = np.zeros((2 * R + 1, 2, 2), complex)
    for j in range(R + 1):
        C[2 * j, 0, 0] = p[j]          # z^(2j - R)
        C[2 * j, 1, 0] = q[j]
        C[2 * R - 2 * j, 0, 1] = -np.conj(q[j])  # conj on |z| = 1: z^(R - 2j)
        C[2 * R - 2 * j, 1, 1] = np.conj(p[j])
    return C


def strip_layers(C):
    """Write U(z) = W_R D(z) W_{R-1} ... D(z) W_0 with D(z) = diag(z^-1, z) = e^{-ixZ}."""
    Ws = []
    while len(C) > 1:
        top = C[-1]  # coefficient of the highest power z^deg
        u, s, vh = np.linalg.svd(top)
        ub, sb, _ = np.linalg.svd(C[0])
        if s[0] > 1e-9:
            v = u[:, 1]  # v ⟂ range(top)
        elif sb[0] > 1e-9:  # top is zero: second column ⟂ range(bottom)
            v = np.array([np.conj(ub[1, 1]), -np.conj(ub[0, 1])])
        else:
            v = np.array([1, 0], complex)
        W = np.column_stack([v, np.array([-np.conj(v[1]), np.conj(v[0])])])
        V = np.einsum("ij,kjl->kil", W.conj().T, C)  # W^dag U, still degree deg
        assert np.allclose(V[-1][0], 0, atol=1e-7) and np.allclose(V[0][1], 0, atol=1e-7)
        # diag(z, z^-1) W^dag U has degree deg - 1: top row times z, bottom row times z^-1
        new = np.zeros((len(C) - 2, 2, 2), complex)
        new[:, 0, :] = V[:-2, 0, :]   # z * (z^(k - deg)) row 0 shifts up by one power
        new[:, 1, :] = V[2:, 1, :]
        Ws.append(W)
        C = new
    Ws.append(C[0])
    return Ws[::-1]  # W_0, ..., W_R


def model(Ws, x):
    U = Ws[0]
    for W in Ws[1:]:
        U = W @ np.diag([np.exp(-1j * x), np.exp(1j * x)]) @ U
    psi = U[:, 0]
    return abs(psi[0]) ** 2 - abs(psi[1]) ** 2


def check_realizable(rng):
    for R in (1, 2, 3, 5, 8):
        for _ in range(3):
            F = target(R, rng)
            Ws = strip_layers(laurent_matrix(F))
            assert len(Ws) == R + 1
            for W in Ws:
                assert np.allclose(W.conj().T @ W, np.eye(2), atol=1e-7)
            xs = rng.uniform(0, 2 * np.pi, size=50)
            Fx = np.real(np.exp(2j * np.outer(xs, np.arange(-R, R + 1))) @ F)
            fx = np.array([model(Ws, x) for x in xs])
            assert np.max(np.abs(Fx - fx)) < 1e-6, (R, np.max(np.abs(Fx - fx)))
    print("realizability: random |F| < 1 of degree R = 1..8 reproduced by R uploads, error < 1e-6")


def kernel(R, y):
    k = np.arange(-R, R + 1)
    return np.real(np.exp(1j * np.outer(y, k)) @ (1 - np.abs(k) / (R + 1)))


def check_lower_bound(rng):
    """R + 1 equispaced nodes y_a = 2 pi a/(R + 1): phi(y_a - y_b) = delta_ab and sum_b phi(y - y_b) = 1,
    so B sum_b s_b phi(y - y_b) is a model with values B s_a at the nodes for every sign vector s."""
    from math import comb
    B = 1.0
    for R in (1, 2, 3, 5, 8, 20, 50):
        nodes = 2 * np.pi * np.arange(R + 1) / (R + 1)
        Phi = np.array([kernel(R, nodes - t) for t in nodes]) / (R + 1)
        assert np.allclose(Phi, np.eye(R + 1), atol=1e-9)
        ys = rng.uniform(0, 2 * np.pi, size=2000)
        assert np.allclose(sum(kernel(R, ys - t) for t in nodes) / (R + 1), 1, atol=1e-9)
        if R <= 8:  # realize the interpolant of a random sign vector as a circuit
            sgn = rng.choice([-1, 1], size=R + 1)
            k = np.arange(-R, R + 1)
            F = 0.99 * sum(sb * np.exp(-1j * k * t) for sb, t in zip(sgn, nodes)) * (1 - np.abs(k) / (R + 1)) / (R + 1)
            Ws = strip_layers(laurent_matrix(F))
            assert np.allclose([model(Ws, t / 2) for t in nodes], 0.99 * sgn, atol=1e-6)
            # Monte Carlo of E sup over circuits, sup taken at the circuit for sign(S_a); 4 copies per node
            vals = []
            for _ in range(400):
                sig = rng.choice([-1, 1], size=(R + 1, 4))
                s_a = np.where(sig.sum(axis=1) >= 0, 1, -1)
                G = 0.99 * sum(sb * np.exp(-1j * k * t) for sb, t in zip(s_a, nodes)) * (1 - np.abs(k) / (R + 1)) / (R + 1)
                Wc = strip_layers(laurent_matrix(G))
                fx = np.array([model(Wc, t / 2) for t in nodes])
                vals.append((sig.sum(axis=1) @ fx) / (4 * (R + 1)))
            exact = 0.99 * B * 1.5 / 4  # E|S| = 3/2 for 4 signs
            assert abs(np.mean(vals) - exact) < 5 * np.std(vals) / np.sqrt(len(vals))
            mc = f"; circuits at 4 copies per node: {np.mean(vals):.4f} vs 0.99 x exact {exact:.4f}"
        else:
            mc = ""
        for per in (1, 4, 25):
            n = per * (R + 1)
            mean_abs = sum(comb(per, h) * abs(2 * h - per) for h in range(per + 1)) / 2 ** per
            rad = B * (R + 1) * mean_abs / n  # exact: the sup is attained by the interpolant of sign(S_a)
            low, up = B * np.sqrt((R + 1) / (2 * n)), B * np.sqrt((2 * R + 1) / n)
            assert low - 1e-12 <= rad <= up and low >= 0.5 * up
        print(f"R = {R}: kernel interpolation exact on {R + 1} nodes{mc}; at n = {n}: Rademacher = {rad:.4f}, "
              f"lower bound sqrt((R+1)/2n) = {low:.4f}, spectral upper bound sqrt(|K_R|/n) = {up:.4f}")


if __name__ == "__main__":
    rng = np.random.default_rng(16)
    check_realizable(rng)
    check_lower_bound(rng)
    print("capacity tightness checks pass")
