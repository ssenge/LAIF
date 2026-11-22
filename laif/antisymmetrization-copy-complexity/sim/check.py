"""Checks for the optimal fidelity of anti-symmetrization from n copies of a rank-r state rho on C^d
with eigenvalues lam_1..lam_r.  L_n = number of rows of the irrep label of weak symmetric-group sampling.
1. P(L_n = r) = P(G_1 + ... + G_r <= n) for independent geometric G_i with parameters lam_i (exact, by
   enumerating all words: L_n = longest strictly decreasing subsequence).
2. The law of L_n from the words equals the weights of the isotypic components of rho^{(x)n} (d = 3, n <= 5),
   with the components found as eigenspaces of the sum of all transpositions.
3. Averaging and completion: E_{V'} |A_{W+V'}><A_{W+V'}| has norm 1/C(d-k, r-k); the completion channel
   X -> Pi_anti (X (x) I) Pi_anti / c_k has c_k = C(d,r)/C(d,k) and fidelity exactly 1/C(d-k, r-k) for every
   state X on Lambda^k(V).
4. Constants of the copy bounds."""
import itertools, math
from fractions import Fraction as F
import numpy as np
rng = np.random.default_rng(3)
def lds(w):                          # longest strictly decreasing subsequence (patience on negated letters)
    tails = []
    for x in w:
        x = -x; lo, hi = 0, len(tails)
        while lo < hi:
            m = (lo + hi) // 2
            if tails[m] < x: lo = m + 1
            else: hi = m
        tails[lo:lo + 1] = [x]
    return len(tails)
def word_law(lam, n):
    r = len(lam); out = [F(0)] * (r + 1)
    for w in itertools.product(range(r), repeat=n):
        p = F(1)
        for x in w: p *= lam[x]
        out[lds(w)] += p
    return out
def geo_sum_cdf(lam, n):             # P(G_1 + ... + G_r <= n), exact
    dist = {0: F(1)}
    for l in lam:
        new = {}
        for s, p in dist.items():
            for g in range(1, n - s + 1): new[s + g] = new.get(s + g, F(0)) + p * l * (1 - l) ** (g - 1)
        dist = new
    return sum(dist.values(), F(0))
# 1.
for lam in ([F(1, 2), F(1, 2)], [F(4, 5), F(1, 5)], [F(1, 3)] * 3, [F(1, 2), F(1, 3), F(1, 6)], [F(1, 4)] * 4, [F(2, 5), F(3, 10), F(1, 5), F(1, 10)]):
    for n in range(1, 9 if len(lam) < 4 else 8):
        assert word_law(lam, n)[len(lam)] == geo_sum_cdf(lam, n)
print("1. P(L_n = r) = P(sum of geometrics <= n) exactly")
# 2. quantum check of the law of L_n
def swap(d, n, i, j):
    D = d ** n; M = np.zeros((D, D))
    for idx in itertools.product(range(d), repeat=n):
        t = list(idx); t[i], t[j] = t[j], t[i]
        M[np.ravel_multi_index(tuple(t), (d,) * n), np.ravel_multi_index(idx, (d,) * n)] = 1
    return M
def partitions(n, maxpart=None):
    maxpart = maxpart or n
    if n == 0: yield (); return
    for k in range(min(n, maxpart), 0, -1):
        for p in partitions(n - k, k): yield (k,) + p
content = lambda lab: sum(j - i for i, row in enumerate(lab) for j in range(row))
d = 3
for n in (2, 3, 4, 5):
    T = sum(swap(d, n, i, j) for i in range(n) for j in range(i + 1, n)); ev, V = np.linalg.eigh(T)
    for lam in ((0.7, 0.3), (0.5, 0.3, 0.2)):
        Q = np.linalg.qr(rng.standard_normal((d, d)) + 1j * rng.standard_normal((d, d)))[0]
        rho = sum(l * np.outer(Q[:, i], Q[:, i].conj()) for i, l in enumerate(lam)); R = rho
        for _ in range(n - 1): R = np.kron(R, rho)
        qlaw = [0.0] * (len(lam) + 1)
        for lab in partitions(n):
            if len(lab) > d: continue
            sel = np.abs(ev - content(lab)) < 1e-6; P = V[:, sel] @ V[:, sel].conj().T
            w = np.trace(P @ R).real
            if len(lab) > len(lam): assert abs(w) < 1e-10
            else: qlaw[len(lab)] += w
        wl = word_law([F(x).limit_denominator(100) for x in lam], n)
        assert max(abs(qlaw[k] - float(wl[k])) for k in range(1, len(lam) + 1)) < 1e-9
print("2. law of L_n equals the isotypic weights of rho^(x)n (d = 3, n <= 5)")
# 3. averaging and completion
def antisym_vec(vs):                 # normalized anti-symmetrization of orthonormal vectors
    r = len(vs); d = len(vs[0]); out = np.zeros(d ** r, complex)
    for perm in itertools.permutations(range(r)):
        sgn = np.linalg.det(np.eye(r)[list(perm)]); t = np.array([1.0 + 0j])
        for i in perm: t = np.kron(t, vs[i])
        out += sgn * t
    return out / math.sqrt(math.factorial(r))
def pi_anti(d, r):
    P = 0
    for perm in itertools.permutations(range(r)):
        sgn = np.linalg.det(np.eye(r)[list(perm)]); M = np.zeros((d ** r, d ** r))
        for idx in itertools.product(range(d), repeat=r):
            M[np.ravel_multi_index(tuple(idx[perm[j]] for j in range(r)), (d,) * r), np.ravel_multi_index(idx, (d,) * r)] = 1
        P = P + sgn * M
    return P / math.factorial(r)
for d, r in ((4, 2), (4, 3), (5, 3)):
    Pr = pi_anti(d, r)
    for k in range(1, r):
        U = np.linalg.qr(rng.standard_normal((d, d)) + 1j * rng.standard_normal((d, d)))[0]; W = [U[:, i] for i in range(k)]
        S = 6000; avg = np.zeros((d ** r, d ** r), complex); comp = U[:, k:]
        for _ in range(S):
            Z = np.linalg.qr(rng.standard_normal((d - k, r - k)) + 1j * rng.standard_normal((d - k, r - k)))[0]
            a = antisym_vec(W + [comp @ Z[:, j] for j in range(r - k)]); avg += np.outer(a, a.conj())
        nrm = np.linalg.eigvalsh(avg / S).max(); assert abs(nrm - 1 / math.comb(d - k, r - k)) < 0.03, (d, r, k, nrm)
        # completion: X a random state on Lambda^k(V), V = span of the first r columns of U
        Vb = [U[:, i] for i in range(r)]; basis = [antisym_vec([Vb[i] for i in c]) for c in itertools.combinations(range(r), k)]
        B = np.array(basis).T; g = rng.standard_normal((len(basis), 3)) + 1j * rng.standard_normal((len(basis), 3))
        X = B @ (g @ g.conj().T) @ B.conj().T; X /= np.trace(X).real
        Y = Pr @ np.kron(X, np.eye(d ** (r - k))) @ Pr; ck = np.trace(Y).real
        assert abs(ck - math.comb(d, r) / math.comb(d, k)) < 1e-9
        A = antisym_vec(Vb); fid = (A.conj() @ Y @ A).real / ck
        assert abs(fid - 1 / math.comb(d - k, r - k)) < 1e-9
print("3. averaging norm 1/C(d-k, r-k); completion constant and fidelity exact")
# 4. constants
f = lambda t: t - 1 - math.log(t)
assert f(2) >= 2 / 7 and all(f(t) >= t / 7 for t in np.linspace(2, 200, 5000))
assert math.exp(-f(0.5)) < 1 - 2 / 12
assert all(-math.log(1 - x) <= 2 * x for x in np.linspace(1e-6, 0.5, 2000))
def geo_sum_cdf_float(lam, n):        # P(G_1 + ... + G_r <= n) in floating point, by convolution
    dist = np.zeros(n + 1); dist[0] = 1.0
    for l in lam:
        pmf = np.zeros(n + 1); k = np.arange(1, n + 1); pmf[1:] = l * (1 - l) ** (k - 1)
        dist = np.convolve(dist, pmf)[:n + 1]
    return dist.sum()
for _ in range(300):                 # the minimal n with P(S <= n) >= 1 - 2 delta against the bounds
    r = int(rng.integers(2, 7)); lam = rng.dirichlet(np.ones(r) * rng.choice([0.3, 1, 5]))
    if lam.min() < 1e-3: continue
    M = (1 / lam).sum(); delta = 1 / 12; nup = math.ceil(max(2 * M, 7 * math.log(2 / delta) / lam.min()))
    n = 1
    while geo_sum_cdf_float(lam, n) < 1 - 2 * delta: n += 1
    assert n > M / 2 and n >= math.log(1 / (2 * delta)) / (2 * lam.min())
    assert geo_sum_cdf_float(lam, nup) >= 1 - delta / 2 - 1e-9
print("4. constants and copy bounds hold; all checks passed")
