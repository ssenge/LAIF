"""Checks for the tightness of the spectral capacity bound for single-qubit data reuploaders.

Model: U(x) = W_R e^{-ixZ} W_{R-1} ... e^{-ixZ} W_0, f(x) = B <0|U^dag Z U|0>, frequencies 2j, |j| <= R.
1. Realizability: every real F(x) = sum_{|j|<=R} c_j e^{2ijx} with |F| <= 1 is f/B for some blocks
   (Fejer-Riesz, then layer stripping of the Laurent polynomial matrix).
2. Lower bound: on R + 1 equispaced nodes with n/(R + 1) samples each, the Fejer interpolants realize every
   sign pattern with amplitude B, so the empirical Rademacher complexity is >= B sqrt((R + 1)/(2n)).
"""
import numpy as np


def fejer_riesz(c):
    """g(w) = sum_{|j|<=R} c_j w^j >= 0 on |w| = 1 -> polynomial p of degree R with |p(w)|^2 = g(w)."""
    R = (len(c) - 1) // 2
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
    p = fejer_riesz((one + F) / 2)
    q = fejer_riesz((one - F) / 2)
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
        v = u[:, 1] if s[0] > 1e-9 else np.array([1, 0], complex)  # v ⟂ range(top)
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


def fejer(R, y):
    k = np.arange(-R, R + 1)
    return np.real(np.exp(1j * np.outer(y, k)) @ (1 - np.abs(k) / (R + 1)))


def check_lower_bound(rng):
    """R + 1 equispaced nodes y_a = 2 pi a/(R + 1): phi(y_a - y_b) = delta_ab and sum_b phi(y - y_b) = 1,
    so B sum_b s_b phi(y - y_b) is a model with values B s_a at the nodes for every sign vector s."""
    from math import comb
    B = 1.0
    for R in (1, 2, 3, 5, 8, 20, 50):
        nodes = 2 * np.pi * np.arange(R + 1) / (R + 1)
        Phi = np.array([fejer(R, nodes - t) for t in nodes]) / (R + 1)
        assert np.allclose(Phi, np.eye(R + 1), atol=1e-9)
        ys = rng.uniform(0, 2 * np.pi, size=2000)
        assert np.allclose(sum(fejer(R, ys - t) for t in nodes) / (R + 1), 1, atol=1e-9)
        if R <= 8:  # realize the interpolant of a random sign vector as a circuit
            sgn = rng.choice([-1, 1], size=R + 1)
            k = np.arange(-R, R + 1)
            F = 0.99 * sum(sb * np.exp(-1j * k * t) for sb, t in zip(sgn, nodes)) * (1 - np.abs(k) / (R + 1)) / (R + 1)
            Ws = strip_layers(laurent_matrix(F))
            assert np.allclose([model(Ws, t / 2) for t in nodes], 0.99 * sgn, atol=1e-6)
        for per in (1, 4, 25):
            n = per * (R + 1)
            mean_abs = sum(comb(per, h) * abs(2 * h - per) for h in range(per + 1)) / 2 ** per
            rad = B * (R + 1) * mean_abs / n  # exact: the sup is attained by the interpolant of sign(S_a)
            low, up = B * np.sqrt((R + 1) / (2 * n)), B * np.sqrt((2 * R + 1) / n)
            assert low - 1e-12 <= rad <= up and low >= 0.5 * up
        print(f"R = {R}: Fejer interpolation exact on {R + 1} nodes; at n = {n}: Rademacher = {rad:.4f}, "
              f"lower bound sqrt((R+1)/2n) = {low:.4f}, spectral upper bound sqrt(|K_R|/n) = {up:.4f}")


if __name__ == "__main__":
    rng = np.random.default_rng(16)
    check_realizable(rng)
    check_lower_bound(rng)
    print("capacity tightness checks pass")
