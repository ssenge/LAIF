# Checks for the Clifford commutant facts used in the lower bound, with asserts:
#  (1) enumeration of the stochastic Lagrangian subspaces Sigma_{t,t} for t = 2..5: the count is prod_{k=0}^{t-2} (2^k + 1)
#      and at most 2^{(t^2 + 5t)/2};
#  (2) distinct T, T' in Sigma_{t,t} meet in at most 2^{t-1} vectors, so the Gram matrix of the R(T) = r(T)^{(x) n} is
#      G = 2^{nt} (I + E) with |E_{T,T'}| <= 2^{-n};
#  (3) whenever w = |Sigma_{t,t}| 2^{-n} <= 1/2, the inverse Gram matrix W = G^{-1} satisfies
#      |W_{T,T'} - 2^{-nt} delta_{T,T'}| <= 2^{-nt} 2^{-n} / (1 - w)  (Lemma 1);
#  (4) the three sums of the proof of the total variation bound, with these entries, total at most 2^{-n} + 2w (Lemma 2).
# python -I commutant.py
import itertools
import numpy as np


def stochastic_lagrangians(t):
    m = 2 * t
    good = [v for v in range(1 << m)
            if (bin(v >> t).count("1") - bin(v & ((1 << t) - 1)).count("1")) % 4 == 0]
    goodset = set(good)
    ones = (1 << m) - 1
    found = set()

    def span_add(S, v):
        return S | {s ^ v for s in S}

    def rec(S, dim, start):
        if dim == t:
            found.add(frozenset(S)); return
        for i in range(start, len(good)):
            v = good[i]
            if v in S:
                continue
            S2 = span_add(S, v)
            if all(s in goodset for s in S2):
                rec(S2, dim + 1, i + 1)

    rec({0, ones}, 1, 0)
    return sorted(found, key=lambda s: sorted(s))


def check(t):
    sig = stochastic_lagrangians(t)
    N = len(sig)
    expect = int(np.prod([2**k + 1 for k in range(t - 1)]))
    assert N == expect, (t, N, expect)
    assert N <= 2 ** ((t * t + 5 * t) / 2)
    inter = np.array([[len(a & b) for b in sig] for a in sig], dtype=float)
    off = inter[~np.eye(N, dtype=bool)]
    assert np.all(np.diag(inter) == 2**t) and (N == 1 or off.max() <= 2 ** (t - 1)), t
    rows = []
    for n in range(1, 40):
        w = N * 2.0**-n
        if w > 0.5:
            continue
        E = (inter / 2**t) ** n - np.eye(N)          # G / 2^{nt} - I
        assert np.abs(E).max() <= 2.0**-n * (1 + 1e-12)
        Winv = np.linalg.inv(np.eye(N) + E)           # 2^{nt} W
        dev = np.abs(Winv - np.eye(N)).max()
        bound = 2.0**-n / (1 - w)
        assert dev <= bound * (1 + 1e-9), (t, n, dev, bound)
        # the three sums, with tr M = 2^{nt}, |tr R(T')^dag rho| <= 1, sum_l |tr R(T) M_l| <= 2^{n(t-1)}
        e = 0                                          # index of the identity subspace {(x, x)}
        diag_id = frozenset(((x << t) | x) for x in range(1 << t))
        e = sig.index(diag_id)
        first = abs(1 - Winv[e, e]) / 2
        second = sum(abs(Winv[e, j]) for j in range(N) if j != e) / 2
        third = sum(abs(Winv[i, j]) for i in range(N) if i != e for j in range(N)) * 2.0**-n / 2
        assert first + second + third <= 2.0**-n + 2 * w + 1e-12, (t, n)
        rows.append((n, w, dev, bound, first + second + third))
    print(f"t = {t}: |Sigma| = {N}, max |T cap T'| = {int(off.max()) if N > 1 else '-'}; "
          f"n = {rows[0][0]}..{rows[-1][0]} checked; at n = {rows[0][0]}: dev {rows[0][2]:.3e} <= {rows[0][3]:.3e}, "
          f"three sums {rows[0][4]:.3e} <= {2.0**-rows[0][0] + 2 * rows[0][1]:.3e}", flush=True)


if __name__ == "__main__":
    for t in (2, 3, 4, 5):
        check(t)
    # the threshold of the theorem: t^2 + 5t <= 2n - 6 gives 2^{-n} + 2w <= 2^{-n} + 1/4
    for n in (10, 100, 1000, 10**6):
        t = int((np.sqrt(8 * n + 1) - 5) // 2)
        assert t * t + 5 * t <= 2 * n - 6 and (t + 1) ** 2 + 5 * (t + 1) > 2 * n - 6
        print(f"n = {n}: largest t with t^2 + 5t <= 2n - 6 is {t} (sqrt(2n) = {np.sqrt(2 * n):.1f})")
    print("commutant checks: ok")
