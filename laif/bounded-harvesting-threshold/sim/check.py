"""Numerical checks for the unique optimal threshold under a bounded harvesting rate.

Model: dX = X(mu - kappa X - h) dt + sigma X dB, h in [0, M]; threshold policy h = M 1{X > eta}.
With s = 2/sigma^2, m(y) = y^(s mu - 2) e^(-s kappa y), m0(y) = y^(s(mu - M) - 2) e^(-s kappa y),
lam = eta^(s M), the stationary density is proportional to m on (0, eta] and lam m0 on (eta, inf), and
  H(eta) = M lam int_eta^inf y m0 / (A + lam B),  A = int_0^eta m,  B = int_eta^inf m0.
Checks: (1) H agrees with the closed form in incomplete gamma functions, and (1') with eq. (4.4) as printed; (2) drift identity
H = (P + lam Q)/(A + lam B) with f(y) = y(mu - kappa y); (3) sign H' = sign(Q/B - P/A);
(4) at the zero of D = Q/B - P/A the common value is below f; (5) H has exactly one critical point
on random parameter sets in both cases mu - M > sigma^2/2 and mu - M <= sigma^2/2, and at Fig. 1 of
arXiv:1710.01221 (mu = M = kappa = sigma^2 = 1).
Run: python check.py  (about 3 minutes, 1 core)
"""
import mpmath as mp
import numpy as np

mp.mp.dps = 40


def H_closed(eta, mu, M, k, s2):
    a1, a2, c = 2 * mu / s2, 2 * (mu - M) / s2, 2 * k / s2
    x = c * mp.mpf(eta)
    num = x ** (-a2) * mp.gammainc(a2, x, mp.inf)
    den = x ** (-a1) * c * mp.gammainc(a1 - 1, 0, x) + x ** (-a2) * c * mp.gammainc(a2 - 1, x, mp.inf)
    return M * num / den


def parts(eta, mu, M, k, s2):
    s = 2 / mp.mpf(s2)
    m = lambda y: y ** (s * mu - 2) * mp.e ** (-s * k * y)
    m0 = lambda y: y ** (s * (mu - M) - 2) * mp.e ** (-s * k * y)
    f = lambda y: y * (mu - k * y)
    lam = mp.mpf(eta) ** (s * M)
    a, c, x = s * mu, s * k, s * k * mp.mpf(eta)
    # closed forms on (0, eta]: the integrand y^(s mu - 2) is singular at 0 when s mu is near 1
    A = c ** (1 - a) * mp.gammainc(a - 1, 0, x)
    P = mu * c ** (-a) * mp.gammainc(a, 0, x) - k * c ** (-a - 1) * mp.gammainc(a + 1, 0, x)
    B = mp.quad(m0, [eta, mp.inf]); Q = mp.quad(lambda y: f(y) * m0(y), [eta, mp.inf])
    Hdef = M * lam * mp.quad(lambda y: y * m0(y), [eta, mp.inf]) / (A + lam * B)
    return dict(A=A, B=B, P=P, Q=Q, lam=lam, H=Hdef, Hdrift=(P + lam * Q) / (A + lam * B), D=Q / B - P / A, f=f(eta))


def H_paper(eta, mu, M, k, s2):
    """Eq. (4.4) of arXiv:1710.01221 as printed, with the density (4.3) and its normalizing constant."""
    eta = mp.mpf(eta); a1, a2, c = 2 * mu / s2, 2 * (mu - M) / s2, 2 * k / s2
    lo = lambda y: 1 / (s2 * y ** 2) * (y / eta) ** a1 * mp.e ** (-c * (y - eta))
    hi = lambda y: 1 / (s2 * y ** 2) * (y / eta) ** a2 * mp.e ** (-c * (y - eta))
    inv_C1 = mp.quad(lo, [0, eta]) + mp.quad(hi, [eta, mp.inf])
    return mp.quad(lambda y: y * M * hi(y), [eta, mp.inf]) / inv_C1


def critical_points(p, n=150):
    """Number of sign changes of the discrete derivative of H on a log grid, ignoring rounding-level steps."""
    xs = np.geomspace(1e-4, 20 * p[0] / p[2], n)
    hs = [H_closed(x, *p) for x in xs]
    d = []
    for i in range(n - 1):
        r = (hs[i + 1] - hs[i]) / hs[i]
        if abs(r) > mp.mpf(10) ** (-30):
            d.append(mp.sign(r))
    return sum(1 for i in range(len(d) - 1) if d[i] != d[i + 1]), xs, hs


def main():
    rng = np.random.default_rng(3)
    # (1)-(3) on 30 parameter sets x 4 thresholds
    for _ in range(30):
        s2 = rng.uniform(0.1, 2); mu = rng.uniform(s2 / 2 + 0.005, s2 / 2 + 2)
        M = rng.uniform(0.1, 3); k = rng.uniform(0.2, 2); p = (mu, M, k, s2)
        for eta in (0.05, 0.3, 1.0, 2.5):
            q = parts(eta, *p)
            Hc = H_closed(eta, *p)
            assert abs(q["H"] - Hc) < 1e-5 * Hc, (p, eta)
            assert abs(q["H"] - q["Hdrift"]) < 1e-5 * Hc, (p, eta)
            dH = H_closed(eta * 1.0001, *p) - H_closed(eta * 0.9999, *p)
            assert abs(q["D"]) < 1e-8 or mp.sign(dH) == mp.sign(q["D"]), (p, eta)
    print("(1)-(3) ok")
    # (1') the closed form against eq. (4.4) as printed, away from s mu near 1 where quadrature at 0 is poor
    rng = np.random.default_rng(11)
    for _ in range(20):
        s2 = rng.uniform(0.1, 2); mu = rng.uniform(0.75 * s2 + 0.05, s2 / 2 + 2)
        M = rng.uniform(0.1, 3); k = rng.uniform(0.2, 2)
        for eta in (0.1, 0.8, 2.0):
            Hc = H_closed(eta, mu, M, k, s2)
            assert abs(H_paper(eta, mu, M, k, s2) - Hc) < 1e-8 * Hc, (mu, M, k, s2, eta)
    print("(1') closed form = eq. (4.4) as printed")
    # (5) unimodality, both cases
    rng = np.random.default_rng(7); nA = nB = 0
    for _ in range(400):
        s2 = rng.uniform(0.02, 3); mu = rng.uniform(s2 / 2 + 0.005, s2 / 2 + 4)
        M = rng.uniform(0.02, 4); k = rng.uniform(0.05, 3); p = (mu, M, k, s2)
        if mu - M > s2 / 2: nA += 1
        else: nB += 1
        c, _, _ = critical_points(p, 120)
        assert c == 1, p
    print("(5) unimodal on 400 sets:", nA, "with mu-M > s2/2,", nB, "without")
    # Fig. 1 parameters and (4) at the maximizer
    p = (1, 1, 1, 1)
    c, xs, hs = critical_points(p, 400)
    assert c == 1
    i = int(np.argmax([float(h) for h in hs]))
    eta = mp.findroot(lambda e: parts(e, *p)["D"], xs[i])
    q = parts(eta, *p)
    assert q["P"] / q["A"] < q["f"]
    Hmax = H_closed(eta, *p)
    assert (1 - 0.5) ** 2 / 4 <= Hmax <= 1 / 4  # bounds (2.7) of [1]: (mu - s2/2)^2/(4k) <= rho* <= mu^2/(4k)
    print("Fig. 1: one critical point, threshold", mp.nstr(eta, 8), "yield", mp.nstr(H_closed(eta, *p), 8))


if __name__ == "__main__":
    main()
