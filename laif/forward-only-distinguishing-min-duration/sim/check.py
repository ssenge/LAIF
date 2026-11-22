"""Checks for the echo algorithm under a minimum evolution duration.
Step: apply exp(-iHs), project onto P = span{|0>,|1>} (Kraus A = P U P), apply X on P.
Cycle C = X A X A. YES (H|0> = 0): C = a11 * I, so the final outcome |1> never occurs.
NO (H|0> = eps|1>): <1|C^m|0> = 2 alpha beta ((p+q)^m - (p-q)^m)/(2q), p = alpha delta + beta^2,
q = 2 beta sqrt(alpha delta), and |<1|C^m|0>| >= LB(eps, s, m) from the bounds on alpha, beta, delta."""
import numpy as np
from scipy.linalg import expm
rng = np.random.default_rng(1)

def ham(d, eps, yes, kind):
    K = np.zeros((d, d), complex)
    B = rng.normal(size=(d - 1, d - 1)) + 1j * rng.normal(size=(d - 1, d - 1))
    B = B + B.conj().T
    if kind == "detuned":            # |1> strongly detuned and coupled to the rest
        B[0, 0] += 5 * np.abs(B).max()
    K[1:, 1:] = B
    K *= (1 - eps) / np.linalg.norm(K, 2)
    H = K.copy()
    if not yes:
        H[0, 1] += eps; H[1, 0] += eps
    assert np.linalg.norm(H, 2) <= 1 + 1e-12
    return H

X = np.array([[0, 1], [1, 0]])
def amp(H, s, m):
    A = expm(-1j * H * s)[:2, :2]
    C = X @ A @ X @ A
    return np.linalg.matrix_power(C, m), A

def lb(eps, s, m):
    beta = 0.958 * eps * s if s <= 0.5 else None
    alpha = 1 - eps**2 * s**2 / 2
    pmin = 1 - 2 * s**2
    x = 2 * eps * s / pmin
    y = m * x
    assert y <= 1
    F = m * (2 - np.sinh(y) / y) if y > 0 else m
    return 2 * alpha * beta * pmin ** (m - 1) * F

worst = np.inf; count = 0
for trial in range(400):
    d = int(rng.integers(3, 9)); eps = float(10 ** rng.uniform(-2.5, -0.3))
    s = float(rng.uniform(0.01, 0.5)); kind = ["rand", "detuned"][trial % 2]
    T = min(1 / (2 * eps), 1 / (4 * s)); m = max(1, int(T / (2 * s)))
    if m * 2 * eps * s / (1 - 2 * s * s) > 1:
        continue
    # YES: exact one-sidedness
    Cm, A = amp(ham(d, eps, True, kind), s, m)
    assert abs(A[0, 1]) < 1e-12 and abs(A[1, 0]) < 1e-12 and abs(A[0, 0] - 1) < 1e-12
    assert abs(Cm[1, 0]) < 1e-12
    # NO: exact formula and lower bound
    Cm, A = amp(ham(d, eps, False, kind), s, m)
    al, be, de = A[0, 0], A[1, 0], A[1, 1]
    assert abs(A[0, 1] - A[1, 0]) < 1e-12              # symmetric off-diagonal
    assert abs(be) >= 0.958 * eps * s - 1e-15 and abs(be) <= eps * s + 1e-15
    assert abs(al - 1) <= eps**2 * s**2 / 2 + 1e-15 and abs(de) >= 1 - s**2 / 2 - 1e-15
    p = al * de + be**2; q = 2 * be * np.sqrt(al * de)
    exact = 2 * al * be * ((p + q) ** m - (p - q) ** m) / (2 * q)
    assert abs(exact - Cm[1, 0]) <= 1e-9 * max(1, abs(exact))
    r = abs(Cm[1, 0]) / lb(eps, s, m)
    assert r >= 1 - 1e-9, (eps, s, m, r)
    worst = min(worst, r); count += 1
print(count, "instances: YES one-sided, NO formula exact, lower bound holds; min ratio", round(worst, 4))

# ---- Theorem constants: per-run detection bound P(eps, s) and time per run, for the stated m.
def m_of(eps, s): return max(1, int(np.floor(min(1 / (4 * eps * s), 1 / (8 * s * s)))))
def p_lb(eps, s):
    m = m_of(eps, s)
    alpha = 1 - eps**2 * s**2 / 2; beta = eps * np.sin(s); pmin = 1 - 2 * s * s
    if m == 1:
        a = 2 * alpha * beta
    else:
        y = 2 * m * eps * s / pmin; assert y <= 1 + 1e-12, (eps, s, y)
        a = 2 * alpha * beta * pmin ** (m - 1) * m * (2 - np.sinh(y) / y)
    return a * a, 2 * m * s
def escape_lb(eps, s): return 2 * (1 - np.cos(2)) / 4 * eps**2 * s**2, s      # one call of length s, s <= 1

worst = 0
for eps in np.geomspace(1e-4, 1, 300):
    for tau in np.geomspace(1e-5, 1, 300):
        P, t = p_lb(eps, tau) if tau <= 0.5 else escape_lb(eps, tau)
        worst = max(worst, t / P / max(1 / eps, tau / eps**2))
print("max over grid of (run time / detection probability) / max(1/eps, tau/eps^2):", round(worst, 2))
assert worst <= 100

# ---- exact detection probability on instances, compared with the bound
for kind in ["rand", "detuned"]:
    for eps, s in [(0.05, 0.01), (0.05, 0.2), (0.01, 0.3), (0.2, 0.5)]:
        H = ham(8, eps, False, kind); m = m_of(eps, s)
        P = abs(amp(H, s, m)[0][1, 0]) ** 2
        Pl, t = p_lb(eps, s)
        assert P >= Pl * (1 - 1e-9)
        print(f"{kind:8s} eps={eps} tau={s} m={m} P={P:.3e} bound={Pl:.3e} time/P={t/P:.1f} max(1/eps,tau/eps^2)={max(1/eps, s/eps**2):.1f}")
