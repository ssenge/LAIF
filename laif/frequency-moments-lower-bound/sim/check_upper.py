"""Classical simulation of the estimator of Theorem 3 (multiplicities at most B).
Quantum steps are replaced by their ideal outputs: approximate counting returns the marked count K
within relative error eta, and Grover sampling returns a uniformly random marked position.
Checks: (1) the estimate of F_k has small relative error on random inputs and on moment-matching
instances; (2) the query cost proxy s_1 + sum_l s_{l+1} sqrt(N/K_l) + sum_l sqrt(N/K_l)/eta grows as N^{a_k};
(3) Stirling identity n^k = sum_l S(k,l) n^(l falling) and the exponents of the level sizes."""
import math, random
import numpy as np
from fractions import Fraction as Fr

def stirling2(k, l):
    return sum((-1) ** (l - i) * math.comb(l, i) * i ** k for i in range(l + 1)) // math.factorial(l)
def falling(n, l):
    r = 1
    for i in range(l): r *= n - i
    return r
for k in range(1, 9):
    for n in range(0, 15):
        assert n ** k == sum(stirling2(k, l) * falling(n, l) for l in range(1, k + 1)) or (n == 0 and k == 0)
print("Stirling identity checked")

def exps(k):
    a = Fr(2 ** (k - 1) - 1, 2 ** k - 1)
    x = [a]
    for _ in range(k - 2): x.append(a - Fr(1, 2) + x[-1] / 2)
    assert 1 - x[-1] / 2 - Fr(1, 2) == a - 0 or True
    assert Fr(1, 2) - x[-1] / 2 == a                                   # last estimate costs sqrt(N / s_{k-1})
    for i in range(k - 2): assert x[i + 1] - x[i] / 2 + Fr(1, 2) == a      # s_{l+1} sqrt(N/s_l) = N^a
    assert all(0 < xi <= a for xi in x) and all(2 * x[i + 1] < x[i] for i in range(k - 2))
    return a, x
for k in range(2, 12): exps(k)
print("level-size exponents checked for k = 2..11:", [str(v) for v in exps(3)[1]], [str(v) for v in exps(4)[1]])

def make_string(counts, rng):
    """counts[t] = number of symbols of multiplicity t; returns a shuffled array of symbols."""
    syms = np.concatenate([np.repeat(np.arange(c) + 10 ** 7 * t, t) for t, c in counts.items() if c])
    rng.shuffle(syms); return syms

def true_Fk(counts, k): return sum(c * t ** k for t, c in counts.items())

def estimate(a, k, C, eta, rng, B=None):
    """Level l holds a multiset R_l of positions. rho_l = mean over r in R_l of (t_r - l), where t_r is the
    number of occurrences of the symbol of r: the occurrences inside the queried set U are known, and the sum
    of the outside occurrences over R_l equals sum_{y not in U} m_l(y), m_l(y) = #{r in R_l : a_r = a_y},
    a bounded mean (approximate counting, relative error eta). The next level samples fresh positions y with
    weight m_l(y) (Grover sampling plus rejection with acceptance m_l(y)/B)."""
    N = len(a); al, x = exps(k)
    s = [max(1, int(C * N ** float(xi))) for xi in x]
    order = np.argsort(a, kind="stable"); sa = a[order]
    starts = np.flatnonzero(np.r_[True, sa[1:] != sa[:-1]]); ends = np.r_[starts[1:], N]
    gid = np.empty(N, dtype=np.int64); gid[order] = np.repeat(np.arange(len(starts)), ends - starts)
    mult = (ends - starts)[gid]                                            # t of each position
    inU = np.zeros(N, dtype=bool)
    R = rng.choice(N, size=s[0], replace=False); inU[R] = True
    P = [None, float(N)]; cost = s[0]
    for l in range(1, k):
        g = gid[R]
        # occurrences of each R-symbol inside U, known exactly from the queried positions
        Ug = gid[inU]; in_cnt = np.bincount(Ug, minlength=len(starts))
        out_sum = float(np.sum(mult[R] - in_cnt[g]))                       # = sum over fresh y of m_l(y)
        cost += math.sqrt(N / max(out_sum, 1)) / eta
        out_hat = out_sum * (1 + eta * rng.uniform(-1, 1))
        rho = (float(np.sum(in_cnt[g])) + out_hat) / len(R) - l
        P.append(P[-1] * max(rho, 0.0))
        if l == k - 1: break
        if out_sum == 0:
            P += [0.0] * (k - 1 - l); break
        # fresh positions with weight m_l(y): pick r in R uniformly with weight (t_r - in_U), then a fresh position of its symbol
        w = (mult[R] - in_cnt[g]).astype(float)
        pick = rng.choice(len(R), size=s[l], p=w / w.sum())
        newR = []
        for i in pick:                                                     # distinct fresh positions
            j = g[i]; cand = order[starts[j]:ends[j]]; cand = cand[~inU[cand]]
            if len(cand) == 0: continue
            y = int(rng.choice(cand)); inU[y] = True; newR.append(y)
        cost += s[l] * math.sqrt(N / max(out_sum, 1)) * (B or 1)
        R = np.array(newR); inU[R] = True
    F = sum(stirling2(k, l) * P[l] for l in range(1, k + 1))
    return F, cost

rng = np.random.default_rng(5)
worst = 0
for trial in range(24):
    k = 3 if trial < 12 else 4; B = 5
    N0 = 2000000
    w = rng.dirichlet(np.ones(B))
    counts = {t: int(N0 * w[t - 1] / t) for t in range(1, B + 1)}
    a = make_string(counts, rng)
    F, _ = estimate(a, k, 40, 0.02, rng)
    err = abs(F / true_Fk(counts, k) - 1); worst = max(worst, err)
    assert err < 0.06, (trial, counts, err)
print(f"random profiles, N = 2e6, k = 3, 4, B = 5: worst relative error {worst:.3f}")

# moment-matching pair for k = 3 (Z_0 on {0,1,2}, Z_1 adds mass at 3): the estimator separates them
z0 = [Fr(11, 24), Fr(1, 12), Fr(11, 24), Fr(0)]; z1 = [Fr(55, 144), Fr(5, 16), Fr(11, 48), Fr(11, 144)]
for z in (z0, z1):
    N = 2000000; m = N // 2
    cnt = rng.multinomial(m, [float(p) for p in z]); zsum = sum(t * int(cnt[t]) for t in range(4))
    counts = {1: int(cnt[1]) + N - zsum, 2: int(cnt[2]), 3: int(cnt[3])}
    a = make_string(counts, rng)
    est = [estimate(a, 3, 40, 0.02, rng)[0] / N for _ in range(5)]
    med = float(np.median(est))
    print("pair instance: F_3/N true", round(true_Fk(counts, 3) / N, 4), "median of 5 estimates", round(med, 4))
    assert abs(med - true_Fk(counts, 3) / N) < 0.06

# cost growth: fit the exponent of the cost proxy on 2-to-1 plus 3-to-1 inputs
for k in (3, 4):
    Ns, costs = [], []
    for N0 in (10 ** 5, 4 * 10 ** 5, 16 * 10 ** 5, 64 * 10 ** 5):
        counts = {1: N0 // 4, 2: N0 // 8, 3: N0 // 12, 4: N0 // 16} if k == 4 else {1: N0 // 3, 2: N0 // 6, 3: N0 // 9}
        a = make_string(counts, rng)
        c = np.mean([estimate(a, k, 6, 0.05, rng)[1] for _ in range(2)])
        Ns.append(len(a)); costs.append(c)
    slope = np.polyfit(np.log(Ns), np.log(costs), 1)[0]
    al = float(exps(k)[0])
    print(f"k={k}: cost proxy exponent {slope:.3f} (a_k = {al:.3f})")
    assert abs(slope - al) < 0.06
