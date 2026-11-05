#!/usr/bin/env python3
"""Checks Theorem 1 of ../README.md: the explicit window construction for a tunable upload gate.

P(x) = sum_j e^{iw(x+2j)} R(x+2j), with R a Gaussian-smoothed rectangle on [-1/4, 5/4]. Its Fourier coefficients at
e^{i pi k x} are c_k = R^(pi k - w) / 2, and R^(xi) = 1_I^(xi) exp(-xi^2 s^2 / 4). Truncate to |k - k0| <= N', then
rescale so that |T| <= 1 on the whole circle. Verifies, on a fine grid, all bounds claimed in the proof and the final
Frobenius error of the gate, for a range of w and eps.
"""
from math import ceil, log, pi, sqrt
import numpy as np
from scipy.special import erf

X = np.linspace(-1, 1, 20001)
ARC = (X >= 0) & (X <= 1)


def build(w, eps):
    delta = eps ** 2 / 2
    lam = log(1 / delta) + 2
    s = 1 / (4 * sqrt(lam))
    np_ = ceil(8 * lam / pi)
    k0 = round(w / pi)
    k = np.arange(k0 - np_, k0 + np_ + 1)
    xi = pi * k - w
    # Fourier transform of the rectangle on [-1/4, 5/4]: exp(-i xi / 2) * 2 sin(3 xi / 4) / xi, and 3/2 at xi = 0
    safe = np.where(np.abs(xi) < 1e-12, 1.0, xi)
    rect = np.where(np.abs(xi) < 1e-12, 1.5, 2 * np.sin(0.75 * xi) / safe) * np.exp(-0.5j * xi)
    c = 0.5 * rect * np.exp(-xi ** 2 * s ** 2 / 4)
    t = np.exp(1j * pi * np.outer(X, k)) @ c
    p = sum(
        np.exp(1j * w * (X + 2 * j)) * 0.5 * (erf((X + 2 * j + 0.25) / s) - erf((X + 2 * j - 1.25) / s))
        for j in range(-4, 5)
    )
    return t, p, delta, lam, np_, k0


def main():
    for w in [0.0, 0.5, 1.0, pi / 2, 3.3, 40.7, 400.1]:
        for eps in [0.3, 1e-1, 1e-2, 1e-3, 1e-4, 1e-5, 1e-6]:
            t, p, delta, lam, np_, k0 = build(w, eps)
            g = np.exp(1j * w * X)
            assert np.abs(p).max() <= 1 + 1e-12  # the periodization of the window is at most 1
            assert np.abs(p - g)[ARC].max() <= 2 * np.exp(-lam) + 1e-13  # window error on [0, 1]
            assert np.abs(t - p).max() <= 0.022 * delta + 1e-12  # truncation error, plus float noise of the grid sum
            scale = 1 + 0.022 * delta
            f = t / scale
            assert np.abs(f).max() <= 1 + 1e-13
            q2 = np.maximum(1 - np.abs(f[ARC]) ** 2, 0)
            frob = np.sqrt(2 * (np.abs(f[ARC] - g[ARC]) ** 2 + q2)).max()
            assert frob <= eps, (w, eps, frob)
            n_total = abs(k0) + np_
            bound = abs(w) / pi + 1.5 + (16 / pi) * log(1 / eps) + (8 / pi) * (log(2) + 2)
            assert n_total <= bound, (n_total, bound)
    print("all bounds hold on the grid")
    for eps in [1e-1, 1e-2, 1e-3, 1e-4, 1e-5, 1e-6]:
        t, p, delta, lam, np_, k0 = build(0.5, eps)
        f = t / (1 + 0.022 * delta)
        q2 = np.maximum(1 - np.abs(f[ARC]) ** 2, 0)
        frob = np.sqrt(2 * (np.abs(f[ARC] - np.exp(0.5j * X[ARC])) ** 2 + q2)).max()
        print(f"eps={eps:.0e}  fixed gates D={2 * (abs(k0) + np_):4d}  Frobenius error={frob:.2e}")


if __name__ == "__main__":
    main()
