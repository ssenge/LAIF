"""Certified upper bound on sin(theta) * E[queries] for Grover search with an unknown number of solutions.

Algorithm (parameters lam, al, c, h0, k0, M): draw u uniform in {0..M-1}, U = (u + 1/2) / M. First k0 rounds
with k = 0 (a classical sample). Then rounds i = 0, 1, ...: m = c lam^(i+U), a = floor(al m),
h = max(h0, ceil(m) - a), k uniform in {a..a+h-1}; apply k Grover iterations to the uniform state, measure,
check the item. Cost k + 1 oracle queries per round. Stop at the first marked item. sin^2 theta = t/N.

A round fails with probability q = mean_k cos^2((2k+1) theta)
  = 1/2 + (sin(4(a+h) theta) - sin(4a theta)) / (4h sin 2theta)
  = 1/2 - (sin(4(a+h) d) - sin(4a d)) / (4h sin 2d),  d = pi/2 - theta.

Regions: (B) theta <= TL by the lattice argument; (A) cells in theta on [TL, pi/4]; (A') cells in d on
[DL, pi/4]; (C) d <= DL crude. All interval bounds in double precision, widened by MARG.
"""
import json
import sys
import numpy as np

MARG = 1e-12
RHO = 0.58            # tail: once q <= RHO for all later rounds, the rest is a geometric series (needs lam * RHO < 1)


def sin_hull(lo, hi):
    """Elementwise [min, max] of sin over [lo, hi] (lo <= hi)."""
    slo, shi = np.sin(lo), np.sin(hi)
    mn, mx = np.minimum(slo, shi), np.maximum(slo, shi)
    # a maximum at pi/2 + 2 pi n or a minimum at -pi/2 + 2 pi n inside the interval
    has_max = np.floor((hi - np.pi / 2) / (2 * np.pi)) >= np.ceil((lo - np.pi / 2) / (2 * np.pi))
    has_min = np.floor((hi + np.pi / 2) / (2 * np.pi)) >= np.ceil((lo + np.pi / 2) / (2 * np.pi))
    return np.where(has_min, -1.0, mn) - MARG, np.where(has_max, 1.0, mx) + MARG


def div_hi(nlo, nhi, dlo, dhi):
    """Upper bound of n / d for n in [nlo, nhi], d in [dlo, dhi], d > 0."""
    return np.where(nhi >= 0, nhi / dlo, nhi / dhi)


def div_lo(nlo, nhi, dlo, dhi):
    return np.where(nlo >= 0, nlo / dhi, nlo / dlo)


def rounds(p, u):
    """(a, h, m) of the geometric rounds of offset u, as a generator."""
    lam, al, c, h0, k0, M = p
    U = (u + 0.5) / M
    i = 0
    while True:
        m = c * lam ** (i + U)
        a = int(np.floor(al * m)); h = max(h0, int(np.ceil(m)) - a)
        yield a, h, m
        i += 1


def q_hi_cells(a, h, x1, x2, near_top):
    """Upper bound of the failure probability on cells x in [x1, x2] (x = theta, or d if near_top)."""
    Blo, Bhi = 4 * (a + h) * x1, 4 * (a + h) * x2
    Alo, Ahi = 4 * a * x1, 4 * a * x2
    sb, SB = sin_hull(Blo, Bhi); sa, SA = sin_hull(Alo, Ahi)
    nlo, nhi = sb - SA, SB - sa
    dlo, dhi = 4 * h * np.sin(2 * x1) * (1 - 1e-15), 4 * h * np.sin(2 * x2) * (1 + 1e-15)   # x <= pi/4
    if near_top:
        q = 0.5 - div_lo(nlo, nhi, dlo, dhi)
    else:
        q = 0.5 + div_hi(nlo, nhi, dlo, dhi)
    return np.minimum(1.0, q + MARG)


def q_crude(h, x1):
    return 0.5 + 1.0 / (2 * h * np.sin(2 * x1))


def cells_bound(p, x1, x2, near_top):
    """Upper bound of E on each cell, averaged over the offsets."""
    lam, al, c, h0, k0, M = p
    tot = np.zeros_like(x1)
    # failure of a classical sample: cos^2 theta = sin^2 d
    f0 = np.sin(x2) ** 2 if near_top else np.cos(x1) ** 2
    for u in range(M):
        surv = np.ones_like(x1); e = np.zeros_like(x1)
        for _ in range(k0):
            e += surv; surv = surv * np.minimum(1.0, f0 + MARG)
        for a, h, m in rounds(p, u):
            w = a + (h - 1) / 2 + 1
            # tail: every later round has h >= ceil(m') - floor(al m') >= (1 - al) m' >= (1 - al) m
            if (1 - al) * m >= h0 and np.all(q_crude((1 - al) * m, x1) <= RHO):
                # later rounds: w_i <= m_i + 1, m_i = m lam^n
                e += surv * (m / (1 - lam * RHO) + 1 / (1 - RHO))
                break
            e += surv * w
            surv = surv * q_hi_cells(a, h, x1, x2, near_top)
        tot += e
    return tot / M * (1 + 1e-9)


def lattice_bound(p, TL, cells=2000, YT=400.0):
    """Region B: sup over theta <= TL of theta * E, by the periodic lattice in y = m theta."""
    lam, al, c, h0, k0, M = p
    mstar = 60.0                                    # rounds with m >= mstar have h = ceil(m) - floor(al m)
    assert mstar * (1 - al) - 1 >= h0
    # small rounds (m < mstar) and the k0 samples: cost times theta <= TL * Wsmall
    Wsmall = 0.0
    for u in range(M):
        W = k0
        for a, h, m in rounds(p, u):
            if m >= mstar: break
            W += a + (h - 1) / 2 + 1
        Wsmall = max(Wsmall, W)
    yc = mstar * TL
    nlarge = np.log(YT / yc) / np.log(lam) + 2      # large rounds below the tail, each adds theta
    extra = TL * Wsmall + TL * (nlarge + 1 / (1 - RHO))
    below = yc * lam / (lam - 1)                    # sum of lattice y below yc
    rhoT = 0.5 + (1 + TL ** 2) / (4 * (1 - al) * YT - 4 * TL)
    assert lam * rhoT < 1
    r = lam ** (1 / M)
    psi = r ** (np.arange(cells + 1) / cells)       # cells [psi_j, psi_{j+1}] cover one period
    p1, p2 = psi[:-1], psi[1:]
    G = np.zeros(cells)
    for u in range(M):
        # lattice y = psi * r^u * lam^n >= yc, start at the smallest n with y >= yc on the whole cell
        n = int(np.floor(np.log(yc / r ** u) / np.log(lam)))
        surv = np.ones(cells); e = np.zeros(cells) + below
        while True:
            y1, y2 = p1 * r ** u * lam ** n, p2 * r ** u * lam ** n
            if y1.min() < yc:                       # not fully a large round on this cell: count y only
                e += y2; n += 1; continue
            if y1.min() >= YT:
                e += surv * y2 / (1 - lam * rhoT); break
            e += surv * y2
            Alo, Ahi = 4 * al * y1 - 4 * TL, 4 * al * y2
            Blo, Bhi = 4 * y1, 4 * y2 + 4 * TL
            sb, SB = sin_hull(Blo, Bhi); sa, SA = sin_hull(Alo, Ahi)
            g = div_hi(sb - SA, SB - sa, Blo - Ahi, Bhi - Alo)
            q = np.where(g >= 0, 0.5 + g * (1 + TL ** 2) / 2, 0.5 + g / 2)
            surv = surv * np.minimum(1.0, q + MARG)
            n += 1
        G += e
    G /= M
    return float(((1 + al) / 2 * G.max() + extra) * (1 + 1e-9)), float((1 + al) / 2 * G.max())


def region_C(p, DL):
    """d <= DL (t close to N), k0 >= 1. Returns an upper bound of sin(theta) E <= E.
    E = 1 + f (1 + f E_rest) for k0 = 2 (E = 1 + f E_rest for k0 = 1), f = sin^2 d <= d^2. In E_rest, rounds
    before the tail cost w <= m + h0 each; the tail starts at the first round with
    (1 - al) m sin 2d >= 1 / (2 (RHO - 1/2)), so its m is at most mT = lam / (2 (RHO - 1/2) (1 - al) (4/pi) d)."""
    lam, al, c, h0, k0, M = p
    assert k0 >= 1
    K = lam / (2 * (RHO - 0.5) * (1 - al) * (4 / np.pi))
    mT = K / DL
    nT = np.log(mT / c) / np.log(lam) + 2
    # E_rest <= mT / (lam - 1) + mT / (1 - lam RHO) + (h0 + 1) nT + 1 / (1 - RHO), and mT d = K is fixed
    def Erest_times(d):                              # d * E_rest, increasing in d for these terms
        return K / (lam - 1) + K / (1 - lam * RHO) + d * ((h0 + 1) * nT + 1 / (1 - RHO))
    if k0 >= 2:
        return float(1 + DL ** 2 + DL ** 3 * Erest_times(DL))
    return float(1 + DL * Erest_times(DL))


def certify(p, tmax, TL=1e-8, DL=1e-3, ratio=1 + 1e-4):
    out = {"params": dict(zip(["lam", "alpha", "c", "h0", "k0", "M"], p)), "TL": TL}
    out["B_small_theta"], out["B_main_term"] = lattice_bound(p, TL, cells=4000)
    hiA = min(tmax, np.pi / 4)
    n = int(np.ceil(np.log(hiA / TL) / np.log(ratio)))
    x = TL * ratio ** np.arange(n + 1); x[-1] = hiA
    EA = cells_bound(p, x[:-1], x[1:], False)
    vA = np.sin(x[1:]) * EA
    out["A_cells"] = len(vA)
    edges = {"t/N<=1e-4": np.arcsin(1e-2), "t/N<=1e-2": np.arcsin(0.1), "t/N<=1/4": np.pi / 6}
    for k, b in edges.items():
        s = x[:-1] < b
        out["A_sup_" + k] = float(vA[s].max()) if s.any() else None
    out["A_sup"] = float(vA.max())
    if tmax > np.pi / 4:
        dlo = max(DL, np.pi / 2 - tmax)
        n = int(np.ceil(np.log((np.pi / 4) / dlo) / np.log(ratio)))
        d = dlo * ratio ** np.arange(n + 1); d[-1] = np.pi / 4
        EA2 = cells_bound(p, d[:-1], d[1:], True)
        out["A2_cells"] = len(EA2)
        out["A2_sup"] = float((np.cos(d[:-1]) * EA2).max())          # sin(theta) = cos(d)
        out["C_sup"] = float(region_C(p, DL))
    return out


if __name__ == "__main__":
    which = sys.argv[1]
    P = {"S": ((1.59, 0.95, 1.0, 1, 0, 64), np.pi / 6), "U": ((1.59, 0.95, 0.2, 2, 2, 64), np.pi / 2)}
    p, tmax = P[which]
    print(json.dumps(certify(p, tmax)), flush=True)
