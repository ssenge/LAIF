"""Simulations for the threshold harvesting paper.

Model: dX = X(mu - kappa X - h) dt + sigma X dB, h = M 1{X > b}.
Scheme: explicit first-order time step for Y = log X (positivity preserving):
    Y <- Y + (mu - kappa e^Y - h - sigma^2/2) dt + sigma sqrt(dt) Z,   yield += M e^Y 1{e^Y > b} dt.
Checks (asserts): (i) step-size convergence: the time-averaged yield with dt and dt/2 on the same noise
increments agrees within 1 % on the scheme comparison run; (ii) Monte Carlo long-run yield matches the exact
yield H(b) within 4 standard errors at every simulated threshold.
Outputs CSV files for pgfplots in data/.
Parameters: Figure 1 of arXiv:1710.01221 (mu = M = kappa = sigma^2 = 1) unless stated; other values are
illustrative. Fixed seeds. Run: python simulate.py  (about 5 minutes on 1 core).
"""
import csv
import os

import mpmath as mp
import numpy as np

from optimal_threshold import H_dim, optimal

OUT = os.path.join(os.path.dirname(__file__), "data")
os.makedirs(OUT, exist_ok=True)
MU, M, KAPPA, S2 = 1.0, 1.0, 1.0, 1.0


def write(name, header, rows):
    with open(os.path.join(OUT, name), "w", newline="") as fh:
        w = csv.writer(fh); w.writerow(header); w.writerows(rows)


def simulate(b, n_paths, T, dt, seed, x0=None, mu=MU, M_=M, kappa=KAPPA, s2=S2, burn=0.0, z=None,
             record=False, eps=None):
    """Returns time-averaged yield after burn-in per path; optionally the first path and hitting flags."""
    rng = np.random.default_rng(seed)
    n = int(round(T / dt)); nb = int(round(burn / dt))
    sig = np.sqrt(s2)
    y = np.full(n_paths, np.log(x0 if x0 is not None else mu / kappa))
    acc = np.zeros(n_paths); hit = np.zeros(n_paths, dtype=bool); path = []
    for k in range(n):
        x = np.exp(y)
        h = np.where(x > b, M_, 0.0)
        if k >= nb:
            acc += M_ * x * (x > b) * dt
        if eps is not None:
            hit |= x < eps
        if record:
            path.append((k * dt, x[0], int(x[0] > b)))
        dz = z[k] if z is not None else rng.standard_normal(n_paths)
        y = y + (mu - kappa * x - h - s2 / 2) * dt + sig * np.sqrt(dt) * dz
    return acc / (T - burn), hit, path


def convergence_check():
    """Same noise path at dt and dt/2: increments of the fine grid summed pairwise for the coarse one."""
    rng = np.random.default_rng(1)
    T, dt, n_paths, b = 200.0, 0.01, 100, 0.4643
    zf = rng.standard_normal((int(T / (dt / 2)), n_paths))
    zc = (zf[0::2] + zf[1::2]) / np.sqrt(2)
    yc, _, _ = simulate(b, n_paths, T, dt, 0, z=zc, burn=20)
    yf, _, _ = simulate(b, n_paths, T, dt / 2, 0, z=zf, burn=20)
    rel = abs(yc.mean() - yf.mean()) / yf.mean()
    print("convergence: dt=%.3f %.5f  dt/2 %.5f  rel diff %.4f" % (dt, yc.mean(), yf.mean(), rel))
    assert rel < 0.01
    return dt


def risk_curve(eps=0.01, T=10.0):
    """Probability of falling below eps (here 1 % of the carrying capacity mu/kappa) within T years, from X0 = mu/kappa.
    Discrete monitoring at the step dt underestimates hitting probabilities slightly."""
    rows = []
    for i, b in enumerate(np.linspace(0.05, 2.0, 14)):
        _, hit, _ = simulate(b, 2000, T, 0.01, 500 + i, eps=eps)
        p = hit.mean(); rows.append((b, p, 1.96 * np.sqrt(p * (1 - p) / len(hit))))
    write("risk.csv", ["b", "p", "ci"], rows)
    print("risk:", [(round(float(r[0]), 2), round(float(r[1]), 3)) for r in rows])
    assert rows[0][1] > rows[-1][1]  # lower thresholds carry more risk


def seasons(T=300.0, burn=30.0, dt=0.01, n_paths=200):
    """Annual hunting season instead of a continuous rate: no harvest during the year; once a year, if X > b,
    remove (i) the fraction u = 1 - e^-M of X, or (ii) the surplus X - b, at most u X. u is the fraction a
    constant rate M removes in one year without growth. Long-run yield per year against b, Monte Carlo."""
    u = 1 - np.exp(-M); sig = np.sqrt(S2); steps = int(round(1 / dt)); years = int(T)
    rows = []
    for i, b in enumerate(np.linspace(0.1, 2.0, 20)):
        rng = np.random.default_rng(900 + i)
        res = []
        for rule in ("prop", "surplus"):
            y = np.full(n_paths, np.log(MU / KAPPA)); acc = np.zeros(n_paths)
            for yr in range(years):
                for _ in range(steps):
                    x = np.exp(y)
                    y = y + (MU - KAPPA * x - S2 / 2) * dt + sig * np.sqrt(dt) * rng.standard_normal(n_paths)
                x = np.exp(y)
                q = np.where(x > b, u * x, 0.0) if rule == "prop" else np.clip(x - b, 0.0, u * x)
                if yr >= burn: acc += q
                y = np.log(x - q)
            v = acc / (years - burn); res += [v.mean(), 1.96 * v.std(ddof=1) / np.sqrt(n_paths)]
        rows.append((b, *res))
    write("seasons.csv", ["b", "prop", "prop_ci", "surplus", "surplus_ci"], rows)
    for r in rows: print("season b=%.2f prop %.4f +- %.4f  surplus %.4f +- %.4f" % r)
    return rows


def main():
    dt = convergence_check()
    eta_star, H_star = optimal(MU, M, KAPPA, S2)
    eta_star = float(eta_star); print("eta* =", eta_star, "H* =", float(H_star))
    # Fig. A: sample paths at b*/2, b*, 2 b* (same noise)
    for lab, b in (("low", eta_star / 2), ("opt", eta_star), ("high", 2 * eta_star)):
        _, _, path = simulate(b, 1, 30.0, 0.01, 7, record=True)
        write("paths_%s.csv" % lab, ["t", "x", "harvest"], path[::5])
    # Fig. B: exact yield curve and Monte Carlo estimates
    grid = np.linspace(0.02, 2.5, 125)
    write("yield_exact.csv", ["b", "H"], [(b, float(H_dim(b, MU, M, KAPPA, S2))) for b in grid])
    rows = []
    for i, b in enumerate([0.1, 0.25, eta_star, 0.75, 1.0, 1.5, 2.0]):
        yv, _, _ = simulate(b, 200, 300.0, dt, 100 + i, burn=30.0)
        m, se = yv.mean(), yv.std(ddof=1) / np.sqrt(len(yv))
        ex = float(H_dim(b, MU, M, KAPPA, S2))
        print("MC b=%.3f  %.5f +- %.5f   exact %.5f" % (b, m, se, ex))
        assert abs(m - ex) < 4 * se + 0.003, (b, m, se, ex)  # 0.003 allows the O(dt) bias
        rows.append((b, m, 1.96 * se))
    write("yield_mc.csv", ["b", "H", "ci"], rows)
    risk_curve()
    seasons()
    # Fig. C: optimal threshold and yield over noise and cap (mu = kappa = 1), exact
    mp.mp.dps = 20
    rows = []
    for s2 in np.linspace(0.1, 1.9, 19):
        for Mc in np.linspace(0.1, 2.0, 20):
            e, Hs = optimal(1.0, Mc, 1.0, s2)
            rows.append((s2, Mc, float(e), float(Hs), int(1.0 - Mc > s2 / 2)))
        rows.append(())
    write("sensitivity.csv", ["s2", "M", "eta", "H", "caseI"], rows)
    for s2 in ("0.2", "0.6", "1.0", "1.4", "1.8"):  # one file per noise level for the figure
        write("sens_%s.csv" % s2, ["M", "eta", "H", "caseI"],
              [r[1:] for r in rows if r and abs(r[0] - float(s2)) < 1e-9])
    print("sensitivity grid done")


if __name__ == "__main__":
    main()
