#!/usr/bin/env python3
"""Evaluates the union-style sum in the proof of Theorem 1 of ../README.md.

Take m random inputs s_j in {0,1}^T, the rows of A. Let h be a triangular bump of half-width w supported where
cos(2 pi x) >= gamma, and g_p the product of h or its half-period shift according to the sign pattern p. Then
  E_theta g_p(A theta) = sum over integer k with A^T k = 0 of hat g_p(k),
and every |hat g_p(k)| <= mu^m prod_i rho(k_i), with rho(k) = sinc^2(k w) and sum_{k != 0} rho(k) = 1/w - 1 =: tau.
If the k != 0 terms sum to less than 1, every sign pattern has positive measure, so the m inputs are shattered at
margin gamma. Over random A, a k with support size v survives with probability at most q(v)^T, where
q(v) = binom(v, v//2) / 2^v (anti-concentration of sums of signed bits), hence
  E_A[sum] <= sum_{v=1}^m binom(m, v) tau^v q(v)^T.
This script finds the largest m with right side < 1, so it gives a shattered set by the probabilistic method.
"""
from math import acos, ceil, cos, lgamma, log, log2, pi, sin, sqrt
import numpy as np


def lbinom(n, k):
    return lgamma(n + 1) - lgamma(k + 1) - lgamma(n - k + 1)


def bound_ok(T, m, tau):
    v = np.arange(1, m + 1)
    lq = np.array([lbinom(int(x), int(x) // 2) - x * log(2) for x in v])
    lb = np.array([lbinom(m, int(x)) for x in v])
    terms = lb + v * log(tau) + T * lq
    top = terms.max()
    return top + log(np.exp(terms - top).sum()) < 0


def largest_m(T, tau):
    lo, hi = 0, 2
    while bound_ok(T, hi, tau):
        lo, hi = hi, hi * 2
    while hi - lo > 1:
        mid = (lo + hi) // 2
        lo, hi = (mid, hi) if bound_ok(T, mid, tau) else (lo, mid)
    return lo


def check_fourier_identity():
    """random sampling against the frequency sum, for A with rows 10, 01, 11, whose kernel is (-c, -c, c)."""
    w = 1 / 6
    rho = lambda k: 1.0 if k == 0 else (sin(pi * k * w) / (pi * k * w)) ** 2
    mu = w  # the bump with peak 1 and half-width w has mean w
    h = lambda x: np.maximum(1 - np.abs(((x + 0.5) % 1) - 0.5) / w, 0)
    rng = np.random.default_rng(0)
    th = rng.uniform(0, 1, (4000000, 2))
    for p in [(1, 1, 1), (1, 1, -1), (-1, 1, 1), (-1, -1, -1)]:
        shift = [0 if s > 0 else 0.5 for s in p]
        x = np.stack([th[:, 0], th[:, 1], th.sum(axis=1)], axis=1)
        mc = np.prod([h(x[:, i] - shift[i]) for i in range(3)], axis=0).mean()
        fs = sum(
            mu ** 3 * rho(c) ** 3 * cos(2 * pi * c * (-shift[0] - shift[1] + shift[2]))
            for c in range(-400, 401)
        )
        assert abs(mc - fs) < 3e-4, (p, mc, fs)


def main():
    check_fourier_identity()
    print("frequency identity agrees with random sampling on the 3-row example")
    for gamma in [0.5, 0.0]:
        w = acos(gamma) / (2 * pi)
        tau = 1 / w - 1
        print(f"margin gamma = {gamma}, half-width w = {w:.4f}, tau = {tau:.3f}, heuristic limit of m/(T log2 T): {1 / (2 * log2(1 + tau)):.3f}")
        for T in [10, 30, 100, 300, 1000, 3000, 10000, 30000, 100000, 300000]:
            m = largest_m(T, tau)
            print(f"  T={T:7d}  m={m:8d}  m/T={m / T:6.2f}  m/(T log2 T)={m / (T * log2(T)):.3f}")
    assert largest_m(3000, 5) > 3000
    # explicit choice of Theorem 1 at gamma = 1/2: tau = 5, ell = log2 6, m = floor(T log2 T / (4 ell))
    ell = log2(6)
    for T in range(200, 10001):
        m = int(T * log2(T) / (4 * ell))
        u = ceil(4 / pi * sqrt(T))
        assert log2(u) + u * log2(5 * m) <= T - 1, T  # analytic split of the proof
        if T <= 2000 and T % 10 == 0:
            assert bound_ok(T, m, 5.0), T  # the exact sum, as a second check
    # from T = 10^4 on, (2 log2 T)(1.28 sqrt T + 1) + log2(1.28 sqrt T + 1) <= T - 1, and T - 1 minus the left side increases
    for T in [10 ** 4, 10 ** 5, 10 ** 6, 10 ** 8]:
        a = 1.28 * sqrt(T) + 1
        assert 2 * log2(T) * a + log2(a) <= T - 1
    print("explicit m of Theorem 1 passes for 200 <= T <= 10^4, and the crude bound covers larger T")


if __name__ == "__main__":
    main()
