# Constants of the lower bound (Theorem 1 of NOTES.md), with asserts.
# python lbconst.py            check the chosen parameters for D = 2 .. 600
from math import pi, e, sqrt, log, exp

G = 1 / sqrt(3)            # generator norm per unit |<x, v>| (mean slope 1/2 times arcsin-sqrt slope <= 2/sqrt(3) on [1/4, 3/4])
YMAX = 0.25                # prior cap |y| <= YMAX
C, KAPPA = 1000.0, 1.0     # t0 = C D^{3/2}, tau = KAPPA sqrt(D) / (G t0)
N1A = sqrt(1 - YMAX ** 2)
N1B = sqrt(1 - (2 * YMAX) ** 2)


def params(D):
    t0 = C * D ** 1.5
    tau = KAPPA * sqrt(D) / (G * t0)
    s0 = 0.5 - tau
    h = YMAX / sqrt(D)
    R = pi ** 2 / tau ** 2 + D ** 2 / (4 * s0 ** 2)
    Tang = (D * pi ** 2 / (2 * h ** 2) + YMAX ** 2 / (2 * N1A ** 3)) / (s0 ** 2 * N1A)
    return t0, tau, s0, R, Tang


def per_time(D, t):
    """returns b_t (with b_t^2 <= beta''^2 t) and brk_t = (2 pi n1^2 / (e X_t tau^2))^{1/D} at time t >= t0."""
    t0, tau, s0, R, Tang = params(D)
    assert t >= t0 and D ** 1.5 / s0 <= G * t
    A = D * pi / (sqrt(2) * s0)
    B = sqrt(D) / N1B * G * t * (2 + 2 * pi / KAPPA)
    eps = sqrt(A / B)
    assert eps * sqrt(D) <= YMAX
    delta = eps * sqrt(D) / N1B
    cells = D * (pi / (2 * eps)) ** 2 / s0 ** 2
    # b_t = sqrt(D T_tan) + G t delta with T_tan = 2 cells + 4 delta^2 R + 4 Tang
    Ttan = 2 * cells + 4 * delta ** 2 * R + 4 * Tang
    b_exact = sqrt(D * Ttan) + G * t * delta
    b_bound = 2 * sqrt(A * B) + 2 * sqrt(D * Tang)
    assert b_exact <= b_bound * (1 + 1e-12)
    Xtau2 = 2 * (R + Tang + cells) * tau ** 2 + 2 * KAPPA ** 2 * D * (t / t0) ** 2   # X tau^2, G t tau = KAPPA sqrt(D) t / t0
    brk = exp((log(2 * pi * N1A ** 2 / e) - log(Xtau2)) / D)
    return b_bound, brk


def theorem(D, verbose=False):
    t0, tau, s0, R, Tang = params(D)
    W = D / 2                                 # window t1 = t0 e^W
    ts = [t0 * exp(W * i / 200) for i in range(201)]
    vals = [per_time(D, t) for t in ts]
    # b_t / sqrt(t) is decreasing in t (b = a sqrt(t) + const), so its maximum is at t0; brk_t decreases in t
    beta2 = 2 * (vals[0][0] / sqrt(t0)) ** 2
    assert all(2 * b * b <= beta2 * t * (1 + 1e-12) for (b, _), t in zip(vals, ts))
    brk = vals[-1][1]
    assert all(v[1] >= brk * (1 - 1e-12) for v in vals)
    c = 8 * G ** 2 / s0
    q2 = s0 * D ** 3 * brk / (32 * e ** 2 * (s0 + tau) ** 2)
    K = 2 * sqrt(c / q2) + beta2 / q2 + c / (beta2 * t0)
    c_lb = min(1 / (2 * K), beta2 / (2 * c)) / D ** 1.5   # R >= c_lb D^{3/2} ln(t1 / t0)
    if verbose:
        print(f"D={D:6d} t0={t0:.3g} tau={tau:.2e} brk={brk:.3f} beta^2/D^1.5={beta2 / D ** 1.5:8.2f} "
              f"q^2/D^3={q2 / D ** 3:.5f}  R >= {c_lb:.3e} D^1.5 ln(t1/t0)")
    return c_lb


if __name__ == "__main__":
    worst = min(theorem(D, verbose=D in (2, 3, 5, 10, 30, 100, 600)) for D in list(range(2, 200)) + [300, 450, 600])
    print("worst constant over the checked D:", worst)
    assert worst >= 3.5e-6
    print("lower bound constants: ok (c >= 3.5e-6, t0 = 1000 D^{3/2}, window t0 .. t0 e^{D/2})")
