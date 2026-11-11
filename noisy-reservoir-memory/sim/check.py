"""Checks for the note on the compressing memory reservoir (README.md).

Model of [1]: each step resets k input qubits, applies a fixed unitary, then depolarises every qubit (keep probability q).
The reservoir here is classical reversible logic: r memory copies of one bit, k = kp + 2 input qubits (two control
qubits and kp fresh zeros). Each step it decodes by majority and maps the error pattern class of weight w to the class
of weight f(w), writing kp garbage bits into the fresh qubits, which are discarded at the next reset.

1. The class map: capacities, f(w) <= w, and an explicit injective map on bit strings for small r.
2. Exact simulation of the full bit system for small r: its flip rate equals that of the weight chain.
3. The flip rate lam from the stationary distribution (elimination with nonnegative sums), against 50-digit arithmetic.
4. Table: for each k the best r, ln(1/lam), and the memory depth bound W(eps) >= ceil((1 - eps)/(2 lam)) - 1, with the
   two bounds of [1, Theorem 1] for comparison (* marks the formula of Theorem 1(ii) outside its range e^(alpha(k-3)) >= 4).
5. Index compression: the bound with F*, and the limit gamma_q of the exponent.
"""
import itertools
import sys
from math import comb, log, ceil, exp

import numpy as np
from scipy.special import logsumexp
from scipy.stats import binom


def fmap(r, kp):
    """Greedy class map: class w (size C(r, w)) goes to the smallest class v whose remaining capacity C(r, v) 2^kp fits it."""
    h = (r - 1) // 2
    cap = [comb(r, v) << kp for v in range(h + 1)]
    f = []
    for w in range(h + 1):
        v = next(v for v in range(w + 1) if cap[v] >= comb(r, w))
        cap[v] -= comb(r, w)
        f.append(v)
    return f


def gth(P):
    """Stationary distribution by elimination using only sums of nonnegative numbers (small entries stay accurate)."""
    A = P.copy(); n = len(A)
    for k in range(n - 1, 0, -1):
        s = A[k, :k].sum()
        A[:k, k] /= s
        A[:k, :k] += np.outer(A[:k, k], A[k, :k])
    lp = np.full(n, -np.inf); lp[0] = 0.0  # back substitution in logarithms: the ratios can exceed the float range
    with np.errstate(divide="ignore"):
        for k in range(1, n):
            lp[k] = logsumexp(lp[:k] + np.log(A[:k, k]))
    return np.exp(lp - logsumexp(lp))


def weight_chain(r, kp, p):
    """Folded chain on the error weight w <= h relative to the majority; F[w] = probability that a step flips the majority."""
    h = (r - 1) // 2; f = np.array(fmap(r, kp))
    K = np.zeros((h + 1, h + 1)); F = np.zeros(h + 1)
    E2 = np.arange(r + 1); low = E2 <= h
    tgt = np.where(low, f[np.minimum(E2, h)], f[np.minimum(r - E2, h)])
    for w in range(h + 1):  # E2 = errors after noise, relative to the old majority
        dist = np.convolve(binom.pmf(np.arange(r - w + 1), r - w, p), binom.pmf(np.arange(w + 1), w, p)[::-1])
        np.add.at(K[w], tgt, dist)
        F[w] = dist[~low].sum()
    return K, F


def flip_rate(r, kp, p):
    K, F = weight_chain(r, kp, p)
    return float(gth(K) @ F)


def explicit_map(r, kp):
    """Injective map pattern e (weight <= h) -> (pattern e', garbage g in [0, 2^kp)) realising the class map."""
    h = (r - 1) // 2; f = fmap(r, kp)
    by_w = {w: [e for e in range(1 << r) if bin(e).count("1") == w] for w in range(h + 1)}
    pool = {v: [(e, g) for e in by_w[v] for g in range(1 << kp)] for v in range(h + 1)}
    used = {v: 0 for v in range(h + 1)}; M = {}
    for w in range(h + 1):
        v = f[w]
        for e in by_w[w]:
            M[e] = pool[v][used[v]]; used[v] += 1
    assert len(set(M.values())) == len(M)  # injective
    return M


def check_map():
    for r in range(3, 41, 2):
        for kp in range(1, r + 2):
            h = (r - 1) // 2; f = fmap(r, kp)
            assert all(f[w] <= w for w in range(h + 1))
            for v in range(h + 1):
                assert sum(comb(r, w) for w in range(h + 1) if f[w] == v) <= comb(r, v) << kp
    for r, kp in [(5, 1), (7, 2), (9, 3), (11, 3)]:
        M = explicit_map(r, kp)
        assert all(bin(M[e][0]).count("1") == fmap(r, kp)[bin(e).count("1")] for e in M)
    print("1. class map: capacities hold and f(w) <= w for r <= 39; explicit injective maps built for r <= 11", flush=True)


def check_simulation():
    for r, kp, q in [(5, 1, 0.5), (7, 2, 0.9), (9, 3, 0.7), (11, 3, 0.9)]:
        p = (1 - q) / 2; h = (r - 1) // 2; M = explicit_map(r, kp); N = 1 << r; full = N - 1
        # state: memory string x; one step = noise then decode (majority m, error e) and replace e by e'
        P = np.zeros((N, N)); Fl = np.zeros(N)
        d = np.array([[bin(a ^ b).count("1") for b in range(N)] for a in range(N)])
        noise = p ** d * (1 - p) ** (r - d)
        for x in range(N):
            for y in range(N):
                m = bin(y).count("1") > h; e = y ^ (full if m else 0)
                z = M[e][0] ^ (full if m else 0)
                P[x, z] += noise[x, y]
                if m != (bin(x).count("1") > h): Fl[x] += noise[x, y]
        lam_full = float(gth(P) @ Fl)
        lam_w = flip_rate(r, kp, p)
        assert abs(lam_full - lam_w) <= 1e-12 * lam_w, (lam_full, lam_w)
    print("2. full bit-level simulation (r <= 11) gives the same flip rate as the weight chain", flush=True)


def check_precision():
    """Exact rational arithmetic for one chain (p = 1/20, i.e. q = 0.9)."""
    from fractions import Fraction as Fr
    r, kp = 41, 8; p = Fr(1, 20); h = (r - 1) // 2; f = fmap(r, kp); n = h + 1
    pm = lambda m, j: comb(m, j) * p ** j * (1 - p) ** (m - j)
    K = [[Fr(0)] * n for _ in range(n)]; F = [Fr(0)] * n
    for w in range(n):
        for x in range(w + 1):
            for y in range(r - w + 1):
                pr = pm(w, x) * pm(r - w, y); E2 = w - x + y
                if E2 <= h: K[w][f[E2]] += pr
                else: K[w][f[r - E2]] += pr; F[w] += pr
    A = [row[:] for row in K]
    for k in range(n - 1, 0, -1):
        s = sum(A[k][:k])
        for i in range(k): A[i][k] /= s
        for i in range(k):
            for j in range(k): A[i][j] += A[i][k] * A[k][j]
    pi = [Fr(1)] + [Fr(0)] * (n - 1)
    for k in range(1, n): pi[k] = sum(pi[i] * A[i][k] for i in range(k))
    lam = sum(pi[i] * F[i] for i in range(n)) / sum(pi)
    lam_d = flip_rate(r, kp, 0.05)
    assert abs(lam_d - float(lam)) <= 1e-9 * float(lam)
    print(f"3. r = 41, kp = 8, q = 0.9: lam = {float(lam):.11e} (exact rationals) and {lam_d:.11e} (floating point)", flush=True)


def v_index(r, kp):
    """Largest weight after index compression: patterns of weight <= h in weight order, index i -> floor(i / 2^kp)."""
    need, tot = 1 << (r - 1 - kp), 0
    for v in range(r + 1):
        tot += comb(r, v)
        if tot >= need:
            return v


def log_f_star(r, kp, p):
    """ln of the one-step flip probability bound P(v - X + Y > h) at v = v_index (it increases with v), in logarithms."""
    h = (r - 1) // 2; v = v_index(r, kp); n = r - v
    ly = binom.logpmf(np.arange(n + 1), n, p)
    tail = np.array([logsumexp(ly[m:]) for m in range(n + 2)] + [-np.inf])  # tail[m] = ln P(Y >= m)
    x = np.arange(v + 1); m = np.minimum(h + 1 - v + x, n + 1)
    return float(logsumexp(binom.logpmf(x, v, p) + tail[m])), v


def psi(s, p):
    """One-step exponent from fraction s to 1/2: sup_th [th (1/2 - s) - (1 - s) ln(1 - p + p e^th) - s ln(1 - p + p e^-th)]."""
    from scipy.optimize import minimize_scalar
    g = lambda th: -(th * (0.5 - s) - (1 - s) * np.log(1 - p + p * np.exp(th)) - s * np.log(1 - p + p * np.exp(-th)))
    return -minimize_scalar(g, bounds=(0, 60), method="bounded").fun


def check_index_bound():
    from scipy.optimize import brentq
    h2 = lambda t: -(t * np.log2(t) + (1 - t) * np.log2(1 - t))
    print("5. index compression: W(eps) >= ceil((1 - eps)/(2 F*)) - 1 for every r; per input qubit, ln(1/F*)/k with r = k'/kappa,")
    print("   against the limit gamma_q = ln 2 q^2/(1 - q^2):")
    for q in (0.5, 0.9):
        p = (1 - q) / 2; gam = log(2) * q * q / (1 - q * q); alpha = 0.5 * log(1 / (1 - q * q))
        for kappa in (0.2, 0.05):
            row = []
            for k in (50, 200, 400):
                kp = k - 2; r = int(kp / kappa) | 1
                lF, v = log_f_star(r, kp, p)
                row.append(f"k={k}: {-lF / k:.4f}")
            s = brentq(lambda t: h2(t) - (1 - kappa), 1e-12, 0.5)
            print(f"   q = {q}, kappa = {kappa}: " + ", ".join(row) + f";  limit psi(s)/kappa = {psi(s, p) / kappa:.4f}", flush=True)
        lim = [psi(brentq(lambda t: h2(t) - (1 - kap), 1e-12, 0.5), p) / kap for kap in (1e-3, 1e-4, 1e-5)]
        assert abs(lim[-1] - gam) < 1e-2 * gam and gam > 2 * log(2) * alpha * 0.999
        print(f"   q = {q}: psi/kappa at kappa = 1e-3, 1e-4, 1e-5: " + ", ".join(f"{x:.4f}" for x in lim)
              + f";  gamma_q = {gam:.4f}, alpha_q = {alpha:.4f}", flush=True)


def best_r(kp, p, rmax=2400):
    """Best odd r <= rmax on the grid r = 2^j kp + 1 (stopping once it gets worse), refined near small optima.
    Every r gives a valid reservoir, so the cap only weakens the bound."""
    cand = []
    for j in range(0, 12):
        r = (kp << j) + 1
        if r > rmax:
            break
        cand.append((flip_rate(r, kp, p), r))
        if len(cand) > 1 and cand[-1][0] > cand[-2][0]:
            break
    lam, r0 = min(cand)
    if r0 <= 600:
        step = max(2, (r0 // 20) * 2)
        cand += [(flip_rate(r, kp, p), r) for r in range(max(3, int(r0 * 0.6)) | 1, min(rmax, int(r0 * 1.6)) + 2, step)]
    return min(cand)


def table(q, ks, eps=0.01):
    p = (1 - q) / 2; alpha = 0.5 * log(1 / (1 - q * q)); beta = q * (1 + q * q) / ((1 - q) * (1 - q * q))
    print(f"4. q = {q}: alpha_q = {alpha:.4f} nats; the upper bound of [1] grows by 2^beta_q = e^{beta * log(2):.3f} per input qubit")
    print("   k   r (best, r <= 2400)   ln(1/lam)   ln W(0.01): here    [1, Thm 1(ii)]   upper bound [1, Thm 1(i)]")
    prev = None
    for k in ks:
        kp = k - 2
        lam, r = best_r(kp, p)
        lnW = log(ceil((1 - eps) / (2 * lam)) - 1)  # t + 1 noise layers after the write
        lnW1 = alpha * (k - 3) + log(log(q / eps) / 4)
        lnU = ((1 + 4 * q) / (1 - q) + beta * k) * log(2) + log(log(1 / eps))  # W <= ceil(delta^-1 ln(1/eps)), [1, Eq. (3)]
        inrange = exp(alpha * (k - 3)) >= 4  # range of [1, Theorem 1(ii)]
        assert lnW > lnW1 and lnW < lnU
        slope = "" if prev is None else f"   slope {(log(1 / lam) - prev[1]) / (k - prev[0]):.3f} per qubit"
        print(f"   {k:2d}  {r:6d}   {log(1 / lam):9.2f}   {lnW:14.2f}   {lnW1:14.2f}{'' if inrange else '*'}   {lnU:14.2f}{slope}", flush=True)
        prev = (k, log(1 / lam))


if __name__ == "__main__":
    check_map()
    check_simulation()
    check_precision()
    check_index_bound()
    table(0.9, [5, 10, 15, 20, 30])
    table(0.5, [5, 10, 15, 20, 30, 40])
    print("all checks passed")
