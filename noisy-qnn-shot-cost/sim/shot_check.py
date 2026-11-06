"""Checks for the shot cost of the affine noise correction.

Noisy state rho~ = a rho + (1 - a) I/D, readout {Pi_o}, output f = tr(O rho) with
O = R(I - 2 Pi_12). Corrected estimator f^ = (mean(Y) - (1 - a) tr(O)/D) / a, Y = +-R per shot.
"""
import numpy as np
from math import comb, log, log2, ceil, sqrt
from scipy.linalg import sqrtm


def corrected_mse(rng, a, R, P, u, N, reps=20000):
    """Empirical mean square error of the corrected estimator; P, u over outcomes (0,1,2,3)."""
    Pt = a * P + (1 - a) * u
    s = Pt[1] + Pt[2]                       # probability of Y = -R
    f = R * (1 - 2 * (P[1] + P[2]))
    c0 = R * (1 - 2 * (u[1] + u[2]))
    k = rng.binomial(N, s, size=reps)
    fh = (R * (1 - 2 * k / N) - (1 - a) * c0) / a
    return np.mean((fh - f) ** 2), np.mean(fh) - f


def check_upper(rng):
    R = 1.0
    worst = 0.0
    for _ in range(30):
        a = rng.uniform(0.05, 1)
        P = rng.dirichlet(np.ones(4))
        u = np.full(4, 0.25)
        N = int(rng.integers(50, 2000))
        mse, bias = corrected_mse(rng, a, R, P, u, N)
        worst = max(worst, mse / (R ** 2 / (a ** 2 * N)))
        assert abs(bias) < 6 * R / (a * sqrt(N * 20000))
    assert worst <= 1.0 + 0.05
    print(f"corrected estimator: unbiased, E|f^ - f|^2 <= R^2/(a^2 N) on 30 cases "
          f"(largest ratio {worst:.3f})")


def tv_two_point(N, pa, pb, d):
    """Exact TV between N-sample laws of Mult(pa, pb, rest) and Mult(pa + d, pb - d, rest)."""
    tv = 0.0
    qa, qb = pa + d, pb - d
    r = 1 - pa - pb
    for na in range(N + 1):
        for nb in range(N + 1 - na):
            nr = N - na - nb
            c = comb(N, na) * comb(N - na, nb)
            tv += abs(c * (pa ** na * pb ** nb - qa ** na * qb ** nb) * r ** nr)
    return tv / 2


def check_lower_readout():
    """Theorem 1(b): below N = R^2/(72 a^2 eps^2) no test separates the two settings at 2/3."""
    R = 1.0
    for a, eps in [(0.5, 0.1), (0.3, 0.1), (0.8, 0.05)]:
        u = 0.25
        Pa, Pb = 0.3, 0.3                    # ideal P-_a, P-_b >= 1/8
        pa, pb = a * Pa + (1 - a) * u, a * Pb + (1 - a) * u
        d = a * eps / R
        Nlow = int(R ** 2 / (72 * a ** 2 * eps ** 2))
        tv = tv_two_point(Nlow, pa, pb, d)
        assert tv < 1 / 3, tv
        print(f"a = {a}, eps = {eps}: at N = {Nlow}, TV of the two shot records = {tv:.4f} < 1/3")


def root_fid(r, s):
    q = sqrtm(r)
    return np.real(np.trace(sqrtm(q @ s @ q)))


def rand_state(rng, D, rank):
    G = rng.normal(size=(D, rank)) + 1j * rng.normal(size=(D, rank))
    r = G @ G.conj().T
    return r / np.trace(r)


def check_fidelity(rng):
    """Lemma: F(a r + (1-a) I/D, a s + (1-a) I/D) >= a F(r, s) + 1 - a."""
    worst = np.inf
    for _ in range(200):
        D = int(rng.integers(2, 9))
        r, s = rand_state(rng, D, int(rng.integers(1, D + 1))), rand_state(rng, D, int(rng.integers(1, D + 1)))
        a = rng.uniform()
        mix = lambda x: a * x + (1 - a) * np.eye(D) / D
        gap = root_fid(mix(r), mix(s)) - (a * root_fid(r, s) + 1 - a)
        worst = min(worst, gap)
    assert worst >= -1e-9
    print(f"fidelity lemma on 200 random pairs: min slack = {worst:.2e} >= 0")


def check_lower_general():
    """Theorem 1(c): pure pair with f = +-eps; at N = R^2/(23 a eps^2), F~^(2N) >= 8/9."""
    R = 1.0
    for a, eps in [(0.5, 0.1), (0.1, 0.2), (0.9, 0.01)]:
        D = 4
        eta = 0.5 * np.arcsin(eps / R)
        def psi(phi):
            v = np.zeros(D)
            v[0], v[1] = np.cos(phi), np.sin(phi)  # |0> in the +R space, |1> in the -R space
            return np.outer(v, v)
        O = R * np.diag([1, -1, 1, -1])
        rp, rm = psi(np.pi / 4 - eta), psi(np.pi / 4 + eta)
        assert abs(np.trace(O @ (rp - rm)) - 2 * eps) < 1e-12
        mix = lambda x: a * x + (1 - a) * np.eye(D) / D
        Ft = root_fid(mix(rp), mix(rm))
        N = int(R ** 2 / (23 * a * eps ** 2))
        assert Ft ** (2 * N) >= 8 / 9
        print(f"a = {a}, eps = {eps}: at N = {N}, F~^(2N) = {Ft ** (2 * N):.4f} >= 8/9")


def alpha_bounds(m, e1, e2, t2q=None, T1=None, T2=None, m0=0):
    q = ceil(log2(4 * m + m0))
    n2q = m * q / 15
    hi = (1 - e2) ** n2q
    lo = (1 - e1) ** (q - 2) * hi
    if t2q is not None:
        t = n2q * t2q
        lo *= np.exp(-t / (2 * T1)) * np.exp(-t / (2 * T2))
    return q, n2q, lo, hi


def budget_table():
    """Theorem 2 for the calibration values of [1, Table S1.1], B = R = 1."""
    B = R = 1.0
    devices = {
        "ibm_fez": dict(e1=2.761e-4, e2=2.548e-3, t2q=68e-9, T1=144.97e-6, T2=99.9e-6),
        "H2 (gate errors)": dict(e1=3e-5, e2=1e-3),
    }
    for name, p in devices.items():
        for eps in (0.1, 0.05, 0.02):
            m = ceil(4 * B ** 2 / eps ** 2)
            q, n2q, lo, hi = alpha_bounds(m, **p)
            Nup = ceil(4 * R ** 2 / (lo ** 2 * eps ** 2))
            Nlo = R ** 2 / (72 * hi ** 2 * eps ** 2)
            print(f"{name}, eps = {eps}: m = {m}, q = {q}, N2Q = {n2q:.0f}, alpha in "
                  f"[{lo:.3g}, {hi:.3g}], shots per point: suffice {Nup:.3g}, "
                  f"needed at this m >= {Nlo:.3g}")
    # largest useful m at the 8192 shots of [1]: alpha(m) >= R/(eps sqrt(72 N)) is necessary
    N = 8192
    for eps in (0.1, 0.05):
        m = 1
        while alpha_bounds(m + 1, **devices["ibm_fez"])[3] >= R / (eps * sqrt(72 * N)):
            m += 1
        print(f"ibm_fez, N = {N}, eps = {eps}: the fixed readout cannot reach eps "
              f"pointwise beyond m = {m} blocks (B/sqrt(m) = {B / sqrt(m):.3f})")


if __name__ == "__main__":
    rng = np.random.default_rng(12)
    check_upper(rng)
    check_lower_readout()
    check_fidelity(rng)
    check_lower_general()
    budget_table()
    print("shot cost checks pass")
