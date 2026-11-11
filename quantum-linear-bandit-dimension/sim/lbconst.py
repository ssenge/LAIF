# Constants of the lower bound (Theorem 1 of NOTES.md), with asserts.
# python lbconst.py    checks every D = 2 .. DSTAR - 1 on a grid of times, then all D >= DSTAR by a uniform bound.
# Times are written t = t0 e^u, and every quantity is computed scaled by its growth in t, so no value overflows.
from math import pi, e, sqrt, log, exp

G = 1 / sqrt(3)            # generator norm per unit |<x, v>| (mean slope 1/2 times arcsin-sqrt slope <= 2/sqrt(3) on [1/4, 3/4])
YMAX = 0.25                # prior cap |y| <= YMAX
C, KAPPA = 1000.0, 1.0     # t0 = C D^{3/2}, tau = KAPPA sqrt(D) / (G t0)
N1A = sqrt(1 - YMAX ** 2)
N1B = sqrt(1 - (2 * YMAX) ** 2)
DSTAR = 5000
CONST = 3.6e-6             # constant claimed in Theorem 1


def params(D):
    t0 = C * D ** 1.5
    tau = KAPPA * sqrt(D) / (G * t0)
    s0 = 0.5 - tau
    h = YMAX / sqrt(D)
    R = pi ** 2 / tau ** 2 + D ** 2 / (4 * s0 ** 2)
    Tang = (D * pi ** 2 / (2 * h ** 2) + YMAX ** 2 / (2 * N1A ** 3)) / (s0 ** 2 * N1A)
    return t0, tau, s0, R, Tang


def per_time(D, u):
    """at t = t0 e^u: returns b_t / sqrt(t) (b_t^2 <= beta''^2 t) and brk_t = (2 pi n1^2 / (e X_t tau^2))^{1/D}."""
    t0, tau, s0, R, Tang = params(D)
    t = t0 * exp(u) if u < 700 else float("inf")
    assert u >= 0 and D ** 1.5 / s0 <= G * t0
    A = D * pi / (sqrt(2) * s0)
    Bt = sqrt(D) / N1B * G * (2 + 2 * pi / KAPPA)          # B_t / t
    eps2t = A / Bt                                          # eps^2 t
    assert sqrt(eps2t / t0) * sqrt(D) <= YMAX              # eps sqrt(D) <= YMAX at t0, and eps decreases in t
    delta2t = eps2t * D / N1B ** 2                          # delta^2 t
    cells_t = D * (pi / 2) ** 2 / (eps2t * s0 ** 2)        # Cells / t
    eu = exp(-u)                                            # t0 / t
    # b_t = sqrt(D T_tan) + G t delta with T_tan = 2 Cells + 4 delta^2 R + 4 Tang
    Ttan_t = 2 * cells_t + 4 * delta2t * R * eu ** 2 / t0 ** 2 + 4 * Tang * eu / t0      # T_tan / t
    b_exact = sqrt(D * Ttan_t) + G * sqrt(delta2t)
    b_bound = 2 * sqrt(A * Bt) + 2 * sqrt(D * Tang * eu / t0)
    assert b_exact <= b_bound * (1 + 1e-12)
    # X tau^2 = 2 (R + Tang + Cells) tau^2 + 2 KAPPA^2 D (t/t0)^2; log computed with (t/t0)^2 = e^{2u} factored out
    rest = 2 * (R + Tang) * tau ** 2 * eu ** 2 + 2 * cells_t * t0 * tau ** 2 * eu
    logX = 2 * u + log(rest + 2 * KAPPA ** 2 * D)
    brk = exp((log(2 * pi * N1A ** 2 / e) - logX) / D)
    return b_bound, brk


def per_cells(D, u):
    """Cells tau^2 at t = t0 e^u, computed as in per_time."""
    t0, tau, s0, R, Tang = params(D)
    A = D * pi / (sqrt(2) * s0)
    Bt = sqrt(D) / N1B * G * (2 + 2 * pi / KAPPA)
    return D * (pi / 2) ** 2 / (A / Bt * s0 ** 2) * t0 * exp(u) * tau ** 2


def constant(D, beta2, brk, s0, tau, t0):
    c = 8 * G ** 2 / s0
    q2 = s0 * D ** 3 * brk / (32 * e ** 2 * (s0 + tau) ** 2)
    K = 2 * sqrt(c / q2) + beta2 / q2 + c / (beta2 * t0)
    return min(1 / (2 * K), beta2 / (2 * c)) / D ** 1.5, q2   # R >= constant * D^{3/2} ln(t1 / t0)


def theorem(D, verbose=False):
    t0, tau, s0, R, Tang = params(D)
    W = D / 2                                 # window t1 = t0 e^W
    us = [W * i / 200 for i in range(201)]
    vals = [per_time(D, u) for u in us]
    # b_t / sqrt(t) decreases in t (b = a sqrt(t) + const), so its maximum is at t0; brk_t decreases in t
    beta2 = 2 * vals[0][0] ** 2
    assert all(2 * b * b <= beta2 * (1 + 1e-12) for b, _ in vals)
    brk = vals[-1][1]
    assert all(v[1] >= brk * (1 - 1e-12) for v in vals)
    c_lb, q2 = constant(D, beta2, brk, s0, tau, t0)
    if verbose:
        print(f"D={D:6d} t0={t0:.3g} tau={tau:.2e} brk={brk:.3f} beta^2/D^1.5={beta2 / D ** 1.5:8.2f} "
              f"q^2/D^3={q2 / D ** 3:.5f}  R >= {c_lb:.3e} D^1.5 ln(t1/t0)")
    return c_lb


def large_D(Ds):
    """lower bound on the constant, uniform over all D >= Ds, from the closed forms (NOTES.md, Sec. 6):
    with tau = tau1 / D, s0 = 1/2 - tau1 / D increases in D, and
      beta^2 / D^1.5 = 2 (2 sqrt(pi b1 / (sqrt2 C s0)) + 2 sqrt((8 pi^2 + Y^2/(2 n^3 D^2)) / (C s0^2 n1a)))^2   (decreasing in D),
      X tau^2 at t1 = 2 D e^D (1 + eps_D), eps_D = [2 (R + Tang) tau^2 + 2 Cells tau^2] / (2 D e^D)          (decreasing in D),
      log brk = -1 + (log(pi n1a^2 / (e D)) - log(1 + eps_D)) / D, and log(a D) / D decreases for a D > e."""
    tau1 = KAPPA / (G * C)
    s0lo = 0.5 - tau1 / Ds
    b1 = C * G * (2 + 2 * pi / KAPPA) / N1B                  # B_t = b1 D^2 e^u
    bh = lambda s0, Yterm: 2 * (2 * sqrt(pi * b1 / (sqrt(2) * C * s0)) + 2 * sqrt((8 * pi ** 2 + Yterm) / (C * s0 ** 2 * N1A))) ** 2
    bmax = bh(s0lo, YMAX ** 2 / (2 * N1A ** 3 * Ds ** 2))
    bmin = bh(0.5, 0.0)
    # check the closed form against the direct computation at Ds
    t0, tau, s0, R, Tang = params(Ds)
    assert abs(bmax - 2 * per_time(Ds, 0)[0] ** 2 / Ds ** 1.5) < 1e-9 * bmax
    # (R + Tang) tau^2 <= pi^2 + tau1^2/(4 s0^2) + (8 pi^2 + 1) tau1^2/(s0^2 n1a), Cells tau^2 = pi sqrt2 b1 tau1^2 e^u/(4 s0)
    cells_c = pi * sqrt(2) * b1 * tau1 ** 2 / (4 * s0lo)
    t0, tau, s0, R, Tang = params(Ds)
    ct = per_cells(Ds, 1.0)
    assert ct <= cells_c * exp(1.0) * (1 + 1e-12) and (R + Tang) * tau ** 2 <= pi ** 2 + tau1 ** 2 / (4 * s0lo ** 2) + (8 * pi ** 2 + 1) * tau1 ** 2 / (s0lo ** 2 * N1A)
    rest = 2 * (pi ** 2 + tau1 ** 2 / (4 * s0lo ** 2) + (8 * pi ** 2 + 1) * tau1 ** 2 / (s0lo ** 2 * N1A))
    epsD = rest * exp(-Ds) / (2 * Ds) + 2 * cells_c * exp(-Ds / 2) / (2 * Ds)   # bound on eps_D for all D >= Ds
    assert pi * N1A ** 2 / e * Ds > e
    brk_min = exp(-1 + (log(pi * N1A ** 2 / (e * Ds)) - log(1 + epsD)) / Ds)
    assert brk_min <= per_time(Ds, Ds / 2)[1] * (1 + 1e-12)
    cmax = 8 * G ** 2 / s0lo
    q2min = s0lo * brk_min / (8 * e ** 2)                    # q^2 / D^3, using s0 + tau = 1/2
    Kmax = 2 * sqrt(cmax / q2min) + bmax / q2min + cmax / (C * bmin * Ds ** 1.5)   # K D^{3/2}
    lb = min(1 / (2 * Kmax), bmin / (2 * cmax))
    print(f"all D >= {Ds}: beta^2/D^1.5 in [{bmin:.2f}, {bmax:.2f}], brk >= {brk_min:.4f}, constant >= {lb:.4e}")
    return lb


if __name__ == "__main__":
    worst = min(theorem(D, verbose=D in (2, 3, 5, 10, 30, 100, 600, 4999)) for D in range(2, DSTAR))
    print(f"worst constant over D = 2 .. {DSTAR - 1}:", worst)
    assert worst >= CONST
    assert large_D(DSTAR) >= CONST
    print(f"lower bound constants: ok (c >= {CONST}, every D >= 2, t0 = 1000 D^(3/2), window t0 .. t0 e^(D/2))")
