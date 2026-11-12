"""Checks for the quantum monotonicity tester (non-increasing distributions on [n]).
(1) partition P_m: singletons 1..m, then ceil(m/k) buckets of length k for k = 2..m-1, then lengths growing by a
    factor at most 1 + 2/m; asserts K = O(m log n) and, for non-increasing p, the shifted flattening s (bucket j gets
    the average of bucket j-1, singletons keep their value) satisfies p <= s and sum(s) - 1 <= 4/(m-1);
(2) with upper estimates w_hat >= w of total excess Delta: p <= s_hat, Z = sum(s_hat) <= 1 + 4/(m-1) + 3 Delta,
    chi^2(p || s_hat/Z) <= Z - 1;
(3) the kernel F_q: F_q((q+u)/2) = uniform on [6n], TV contraction >= 1/3 after mixing, sup-norm <= max ratio / (6n),
    chi^2 data processing;
(4) the amplitude-estimation upper estimate: E <= 2 pi sqrt(w)/M + pi^2/M^2 implies E <= 4 pi sqrt(w_tilde)/M + 6 pi^2/M^2;
(5) hard instances: uniform on a random half is at least 0.4-far from monotone (matching bound, exact LP for small n),
    and the bucket-level LP gives the exact distance to monotone for a bucket-constant q."""
import numpy as np
from scipy.optimize import linprog

rng = np.random.default_rng(3)


def partition(n, m):
    """list of bucket lengths covering [n]."""
    L = [1] * min(m, n)
    pos = len(L)
    k = 2
    while pos < n and k < m:
        for _ in range(-(-m // k)):
            if pos >= n:
                break
            L.append(min(k, n - pos)); pos += L[-1]
        k += 1
    ell = m
    while pos < n:
        L.append(min(ell, n - pos)); pos += L[-1]
        ell = int(np.ceil(ell * (1 + 1 / m)))
    return L


def bucket_masses(p, L):
    idx = np.cumsum([0] + L)
    return np.array([p[idx[j]:idx[j + 1]].sum() for j in range(len(L))]), idx


def shifted(w, L, m):
    """element-wise s: singletons j < m keep w_j, bucket j >= m gets w_{j-1}/ell_{j-1}."""
    vals = [w[j] if j < m else w[j - 1] / L[j - 1] for j in range(len(L))]
    return np.repeat(vals, L)


def rand_monotone(n):
    kind = rng.integers(0, 5)
    if kind == 0:
        x = np.sort(rng.exponential(size=n))[::-1]
    elif kind == 1:
        x = np.arange(1, n + 1, dtype=float) ** (-rng.uniform(0.2, 2.5))
    elif kind == 2:                                    # steps with sharp drops
        cuts = np.sort(rng.integers(1, n, size=rng.integers(1, 8)))
        x = np.zeros(n); lev = 1.0; prev = 0
        for c in list(cuts) + [n]:
            x[prev:c] = lev; lev *= rng.uniform(0, 0.3); prev = c
    elif kind == 3:                                    # uniform on a prefix
        x = np.zeros(n); x[:rng.integers(1, n + 1)] = 1.0
    else:                                              # point mass plus tail
        x = np.full(n, 1e-6); x[0] = 1.0
    return x / x.sum()


def tv_to_monotone(q):
    """exact LP: min 1/2 sum |q - f| over non-increasing distributions f."""
    n = len(q)
    # variables f (n), t (n); minimize sum t, t >= q - f, t >= f - q, f_i >= f_{i+1}, sum f = 1, f >= 0
    c = np.r_[np.zeros(n), np.ones(n)]
    A, b = [], []
    for i in range(n):
        r = np.zeros(2 * n); r[i] = -1; r[n + i] = -1; A.append(r); b.append(-q[i])
        r = np.zeros(2 * n); r[i] = 1; r[n + i] = -1; A.append(r); b.append(q[i])
    for i in range(n - 1):
        r = np.zeros(2 * n); r[i + 1] = 1; r[i] = -1; A.append(r); b.append(0)
    Aeq = [np.r_[np.ones(n), np.zeros(n)]]
    res = linprog(c, A_ub=np.array(A), b_ub=np.array(b), A_eq=np.array(Aeq), b_eq=[1], bounds=[(0, None)] * (2 * n))
    return res.fun / 2


def tv_to_monotone_buckets(qv, L):
    """same LP over bucket values (q constant on buckets, weights = lengths)."""
    K = len(L); Lw = np.array(L, float)
    c = np.r_[np.zeros(K), Lw]
    A, b = [], []
    for j in range(K):
        r = np.zeros(2 * K); r[j] = -1; r[K + j] = -1; A.append(r); b.append(-qv[j])
        r = np.zeros(2 * K); r[j] = 1; r[K + j] = -1; A.append(r); b.append(qv[j])
    for j in range(K - 1):
        r = np.zeros(2 * K); r[j + 1] = 1; r[j] = -1; A.append(r); b.append(0)
    res = linprog(c, A_ub=np.array(A), b_ub=np.array(b), A_eq=[np.r_[Lw, np.zeros(K)]], b_eq=[1],
                  bounds=[(0, None)] * (2 * K))
    return res.fun / 2


def kernel(q):
    """matrix of F_q on [n] -> [6n], applied to the mixed distribution (x + u)/2."""
    n = len(q); qq = (q + 1 / n) / 2
    mcop = np.floor(6 * n * qq).astype(int)
    assert (mcop >= 3).all()
    R = 6 * n - mcop.sum()
    Fm = np.zeros((n, 6 * n)); start = 0
    for i in range(n):
        keep = mcop[i] / (6 * n * qq[i])
        Fm[i, start:start + mcop[i]] = keep / mcop[i]
        if R > 0:
            Fm[i, mcop.sum():] = (1 - keep) / R
        start += mcop[i]
    return Fm, qq


def main():
    # (1) partition and shifted flattening
    worst = 0
    for n in [50, 1000, 30000, 10 ** 6]:
        for m in [5, 20, 100]:
            if m > n:
                continue
            L = partition(n, m)
            assert sum(L) == n and min(L) >= 1
            K = len(L)
            assert K <= m * (np.log(n) + 3), (n, m, K)
            for _ in range(40 if n < 10 ** 6 else 8):
                p = rand_monotone(n)
                w, idx = bucket_masses(p, L)
                s = shifted(w, L, m)
                assert (p <= s * (1 + 1e-9) + 1e-15).all()
                D = s.sum() - 1
                assert D <= 4 / (m - 1) + 1e-12, (n, m, D)
                worst = max(worst, D * (m - 1))
                # (2) upper estimates
                e = rng.exponential(size=K) * rng.uniform(0, 0.05) / K
                what = w + e; Delta = e.sum()
                sh = shifted(what, L, m); Z = sh.sum()
                assert (p <= sh * (1 + 1e-9) + 1e-15).all()
                assert Z <= 1 + 4 / (m - 1) + 3 * Delta + 1e-12
                qn = sh / Z
                chi2 = np.sum(p ** 2 / qn) - 1
                assert chi2 <= Z - 1 + 1e-12 and (p / qn).max() <= Z * (1 + 1e-9)
    print(f"partition: max (sum s - 1)(m - 1) = {worst:.3f} <= 4; domination, Z and chi^2 bounds hold")
    # (3) kernel
    for n in [5, 17, 40]:
        for _ in range(50):
            q = rng.dirichlet(np.ones(n) * rng.uniform(0.2, 3)); p = rng.dirichlet(np.ones(n) * rng.uniform(0.2, 3))
            Fm, qq = kernel(q)
            assert np.allclose(Fm.sum(axis=1), 1) and (Fm >= -1e-15).all()
            assert np.allclose(qq @ Fm, 1 / (6 * n))
            pp = (p + 1 / n) / 2; Fp = pp @ Fm
            tv_pq = 0.5 * np.abs(p - q).sum(); tv_F = 0.5 * np.abs(Fp - 1 / (6 * n)).sum()
            assert tv_F >= tv_pq / 3 - 1e-12
            assert Fp.max() <= (pp / qq).max() / (6 * n) * (1 + 1e-9)
            chi_F = np.sum(Fp ** 2 * 6 * n) - 1; chi_pq = np.sum(p ** 2 / q) - 1
            assert chi_F <= chi_pq / 2 + 1e-9
    print("kernel: F_q(q) uniform on [6n], TV >= TV(p, q)/3, sup norm <= max ratio/(6n), chi^2 <= chi^2(p||q)/2")
    # (4) amplitude-estimation upper estimate
    for _ in range(20000):
        M = rng.integers(1, 10 ** 4); w = rng.uniform(0, 1) ** rng.uniform(1, 8)
        E = rng.uniform(0, 1) * (2 * np.pi * np.sqrt(w) / M + np.pi ** 2 / M ** 2)
        wt = max(0.0, w + rng.choice([-1, 1]) * E)
        assert abs(wt - w) <= 4 * np.pi * np.sqrt(wt) / M + 6 * np.pi ** 2 / M ** 2 + 1e-15
    print("upper estimate: |w~ - w| <= 4 pi sqrt(w~)/M + 6 pi^2/M^2 on 20000 cases")
    # (5) hard instances and bucket LP
    for n in [20, 60, 120]:
        for _ in range(5):
            T = rng.choice(n, n // 2, replace=False); q = np.zeros(n); q[T] = 2 / n
            ind = np.zeros(n); ind[T] = 1
            dev = np.max(np.maximum(np.cumsum(ind) - np.cumsum(1 - ind), 0))
            match = n // 2 - dev
            d = tv_to_monotone(q)
            assert d >= match / n - 1e-9, (n, d, match / n)
    fails = 0
    for _ in range(1000):
        n = 4000
        ind = np.zeros(n); ind[rng.choice(n, n // 2, replace=False)] = 1
        dev = np.max(np.maximum(np.cumsum(ind) - np.cumsum(1 - ind), 0))
        fails += (n // 2 - dev) / n < 0.4
    assert fails <= 10
    print(f"random half sets: TV to monotone >= matching bound (LP, n <= 120); n = 4000: matching bound < 0.4 in {fails}/1000")
    for _ in range(30):
        n = 60; m = 4; L = partition(n, m)
        qv = rng.dirichlet(np.ones(len(L))) / np.array(L)
        q = np.repeat(qv, L)
        assert abs(tv_to_monotone(q) - tv_to_monotone_buckets(qv, L)) < 1e-7
    print("bucket-level LP equals the full LP for bucket-constant q")
    print("check: all asserts passed")


if __name__ == "__main__":
    main()
