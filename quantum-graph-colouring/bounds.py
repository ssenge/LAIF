"""Upper bounds on the exponents d_k(1) of Theorem 9 of Shimizu and Mori (arXiv:1907.00529), for a given exponent f3
of polynomial-space quantum 3-colouring: time O*(2^{d_k(1) n}) for k-colouring.

    d_k(mu) = min( max_{s=1..k} log2(s)/(2s) + (1 - 1/s) d_{k-1}(1),
                   min_{2 <= k' <= k/2} max_{delta in [k'/k, min(1, mu k')]} h(delta)/2
                        + max(delta d_{k'}(min(1, mu/delta)), (1 - delta) d_{k-k'}(min(1, delta/(k'(1 - delta))))) )

with d_3 = f3 and d_1 = d_2 = 0. The maximum over delta is bounded from above on each piece [a, b] of a partition by
max h/2 + max(b d_{k'}(mu/a), (1 - a) d_{k-k'}(b/(k'(1 - b)))), and every mu is rounded up to the grid j/M. The
algorithm may call each subproblem with these larger size limits u, since that only weakens its promise, so the
values are upper bounds for the algorithm with those calls, not only approximations. A margin of 1e-9 covers the
floating point error, which is below 1e-12 here."""
import numpy as np

M, P = 4000, 4000                                     # mu grid, delta pieces per range


def h(x):
    x = np.clip(x, 1e-300, 1)
    return -(x * np.log2(x) + np.where(x < 1, (1 - x) * np.log2(np.clip(1 - x, 1e-300, 1)), 0))


def table(f3, kmax=20):
    D = {1: np.zeros(M + 1), 2: np.zeros(M + 1), 3: np.full(M + 1, f3)}
    up = lambda mu: np.minimum(np.ceil(np.minimum(mu, 1) * M - 1e-9).astype(int), M)
    out = {3: (f3, 0)}
    for k in range(4, kmax + 1):
        r1 = max(np.log2(s) / (2 * s) + (1 - 1 / s) * D[k - 1][M] for s in range(1, k + 1))
        best, arg = np.full(M + 1, r1), np.zeros(M + 1, dtype=int)
        for kp in range(2, k // 2 + 1):
            for j in range(M + 1):
                mu = j / M
                lo, hi = kp / k, min(1.0, mu * kp)
                if mu < 1 / k or hi < lo:
                    continue
                e = np.linspace(lo, hi, P + 1)
                a, b = e[:-1], e[1:]
                hmax = h(np.clip(0.5, a, b))
                A = b * D[kp][up(mu / a)]
                B = (1 - a) * D[k - kp][up(np.where(b < 1, b / (kp * np.maximum(1 - b, 1e-300)), 1))]   # limit 1 at b = 1
                v = np.max(hmax / 2 + np.maximum(A, B))
                if v < best[j]:
                    best[j], arg[j] = v, kp
        D[k] = best
        out[k] = (best[M] + 1e-9, arg[M])
    return out


if __name__ == "__main__":
    Lam = np.roots([1, 0, 0, 0, -2, -2])
    Lam = max(r.real for r in Lam if abs(r.imag) < 1e-12)
    f_be = (3 + 4 * np.log2(3) + 24 * np.log2(Lam)) / 98            # Beigel-Eppstein, used in [SM]
    f_me = np.log2(1.3217) / 2                                       # Meijer, stated bound O*(1.3217^n)
    sm = [1.1528, 1.3231, 1.4695, 1.5261, 1.6511, 1.6585, 1.7460, 1.7775, 1.7775, 1.8246, 1.8499, 1.8580,
          1.9303, 1.9303, 1.9303, 1.9366, 1.9575, 1.9575]            # Table 1 of [SM], k = 3..20
    tb, tm = table(f_be), table(f_me)
    print("k   [SM] Table 1   recomputed with BE   with Meijer   k'")
    for k in range(3, 21):
        print(f"{k:2d}   {sm[k - 3]:.4f}         {2 ** tb[k][0]:.6f}          {2 ** tm[k][0]:.6f}      {tm[k][1]}")
