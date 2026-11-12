"""Checks for the shell estimator of heavy-tailed mean estimation (Theorem 1).

b = p/(2(p-1)), a = (3p-4)/(4(p-1)). Claimed cost (sigma/eps)^b * max{1, min{d^a, (sigma/eps)^(2-b)}}.
"""
from fractions import Fraction as Fr
from math import ceil, log2, sqrt
import numpy as np


def exponents(p):
    return p / (2 * (p - 1)), (3 * p - 4) / (4 * (p - 1))


def check_identities():
    for k in range(1, 41):
        p = 1 + Fr(k, 40)
        b, a = exponents(p)
        assert Fr(1, 2) - (2 - p) / (4 * (p - 1)) == a
        assert 1 + (2 - p) / (2 * (p - 1)) == b
        assert 2 + (2 - Fr(3, 2) * p) / (p - 1) == b
        assert 2 + 2 * b == (3 * p - 2) / (p - 1)
        if p < 2:
            assert max(b, 2) < 2 * b
    print("exponent identities hold exactly for p = 1 + k/40, k = 1..40")


def cost_terms(p, d, sigma, eps):
    """Per-part costs of the algorithm with all constants set to 1."""
    S = 2 ** p * sigma ** p
    tau = (3 * S / eps) ** (1 / (p - 1))
    rstar = (S / (sqrt(d) * eps)) ** (1 / (p - 1))
    r0 = min(max(rstar, sigma), tau)
    J = max(1, ceil(log2(tau / r0)))
    e1 = eps / (3 * J)
    inner = min(sqrt(d * S * r0 ** (2 - p)) / eps, S * r0 ** (2 - p) / eps ** 2)
    shells = ae = 0.0
    for j in range(J):
        r = r0 * 2 ** j
        pi = min(1.0, S / r ** p)
        shells += r ** 2 * pi ** 1.5 / e1 ** 2
        ae += sqrt(pi) * r / e1 + sqrt(r / e1)
    return inner + shells + ae, J


def closed_form(p, d, sigma, eps):
    b, a = exponents(p)
    x = sigma / eps
    return x ** b * max(1.0, min(d ** a, x ** (2 - b)))


def check_costs():
    """At fixed d, cost / (closed form * J^3) must not grow with sigma/eps (polylog overhead only)."""
    for p in (1.1, 1.25, 4 / 3, 1.5, 1.75, 2.0):
        worst, hi = -np.inf, 0.0
        for d in (1, 10, 10 ** 3, 10 ** 6, 10 ** 9, 10 ** 12):
            xs, ys = [], []
            for e in range(2, 9):
                eps = 10.0 ** (-e)
                c, J = cost_terms(p, d, 1.0, eps)
                xs.append(e)
                ys.append(np.log10(c / closed_form(p, d, 1.0, eps) / J ** 3))
            worst = max(worst, np.polyfit(xs, ys, 1)[0])
            hi = max(hi, 10 ** max(ys))
        assert worst < 0.05, (p, worst)
        print(f"p = {p:.3f}: slope of log(cost / (closed form * J^3)) in log(sigma/eps) <= {worst:+.4f}, "
              f"ratio <= {hi:.3g}, over d = 1 .. 1e12")


def geometric_median(P, iters=200):
    z = P.mean(axis=0)
    for _ in range(iters):
        w = 1 / np.maximum(np.linalg.norm(P - z, axis=1), 1e-12)
        z = (w[:, None] * P).sum(axis=0) / w.sum()
    return z


def gmom_law(rng, Y, w, n, k=9):
    """Geometric median of k block means of n i.i.d. draws from the atoms Y with weights w."""
    sizes = [len(c) for c in np.array_split(np.arange(n), min(k, n))]
    means = np.array([rng.multinomial(m, w) @ Y / m for m in sizes])
    return geometric_median(means)


def heavy_law(rng, d, p):
    """Finite-valued law: a light cloud and heavy atoms at radii 2^k with mass ~ 2^(-kp)/k^2."""
    light = rng.normal(size=(500, d)) / sqrt(d)
    radii = 2.0 ** np.arange(1, 40)
    q = radii ** (-p) / np.arange(1, 40) ** 2
    q = 0.6 * q / q.sum()
    u = rng.normal(size=(len(radii), d))
    u[:, 0] += 2.0  # a common direction, so the heavy atoms move the mean
    u /= np.linalg.norm(u, axis=1, keepdims=True)
    atoms = np.vstack([light, radii[:, None] * u])
    probs = np.concatenate([np.full(len(light), 0.4 / len(light)), q])
    mu = probs @ atoms
    sigma = (probs @ np.linalg.norm(atoms - mu, axis=1) ** p) ** (1 / p)
    return atoms, probs, mu, sigma


def run_estimator(rng, atoms, probs, mu, sigma, p, eps):
    d = atoms.shape[1]
    v = rng.normal(size=d)
    zeta = mu + rng.uniform() * sigma * v / np.linalg.norm(v)  # rough centre, ||zeta - mu|| <= sigma
    Y = atoms - zeta
    nr = np.linalg.norm(Y, axis=1)
    S = 2 ** p * sigma ** p
    tau = (3 * S / eps) ** (1 / (p - 1))
    rstar = (S / (sqrt(d) * eps)) ** (1 / (p - 1))
    r0 = min(max(rstar, sigma), tau)
    J = max(1, ceil(log2(tau / r0)))
    e1 = eps / (3 * J)
    # inner part: bounded-variance estimator, emulated at its worst-case error eps/3
    EW = probs[nr <= r0] @ Y[nr <= r0]
    g = rng.normal(size=d)
    inj = (eps / 3) * g / np.linalg.norm(g)
    est = zeta + EW + inj
    cost, active, shell_sum = 0.0, 0, np.zeros(d)
    for j in range(J):
        r = r0 * 2 ** j
        sel = (nr > r) & (nr <= 2 * r)
        pi = probs[sel].sum()
        Dj = e1 / (8 * r)
        sgn = rng.choice([-1, 1]) if abs(pi - e1 / (4 * r)) > Dj else (1 if rng.random() < 0.5 else -1)
        pih = min(1.0, max(0.0, pi + sgn * Dj))  # amplitude estimate at an end of its error bar
        cost += sqrt(pi) / Dj + 1 / sqrt(Dj)
        if pih < e1 / (4 * r):
            continue
        n = ceil(64 * (r * pih / e1) ** 2)
        est = est + pih * gmom_law(rng, Y[sel], probs[sel] / pi, n)  # exact conditional samples
        shell_sum += probs[sel] @ Y[sel]
        active += 1
        cost += n / sqrt(pih / 2)
    return np.linalg.norm(est - mu), active, np.linalg.norm(shell_sum), np.linalg.norm(est - mu - inj)


def check_emulation(rng):
    for d in (50, 1000, 5000):
        for p in (1.2, 1.5, 1.8):
            atoms, probs, mu, sigma = heavy_law(rng, d, p)
            for eps_rel in (0.3, 0.1):
                eps = eps_rel * sigma
                runs = [run_estimator(rng, atoms, probs, mu, sigma, p, eps) for _ in range(20)]
                worst = max(r[0] for r in runs)
                rest = max(r[3] for r in runs)
                assert rest <= 2 * eps / 3
                act = min(r[1] for r in runs)
                mass = min(r[2] for r in runs)
                assert worst <= eps and act >= 1, (d, p, eps_rel, worst / eps, act)
                print(f"d = {d}, p = {p}, eps = {eps_rel} sigma: max error over 20 runs = "
                      f"{worst / eps:.3f} eps (shells and tail {rest / eps:.3f} eps), sampled shells >= {act}, "
                      f"their mean contribution >= {mass / eps:.2f} eps")


if __name__ == "__main__":
    rng = np.random.default_rng(17)
    check_identities()
    check_costs()
    check_emulation(rng)
    print("heavy-tailed shell estimator checks pass")
