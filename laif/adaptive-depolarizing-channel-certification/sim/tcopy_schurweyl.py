# Schur-Weyl moments: E[sum lambda_i^2] and E[lambda_1] for the RSK shape of a uniform word in [d]^t (Monte Carlo),
# exact values for small cases via hook-content formulas, and the bound E[lambda_1] <= e sqrt(t) + e^2 t/d + 2 (check).
import numpy as np, math, bisect
from itertools import combinations
rng = np.random.default_rng(5)
def rsk_shape(w):
    rows = []
    for x in w:
        for r in rows:
            j = bisect.bisect_right(r, x)
            if j == len(r): r.append(x); x = None; break
            r[j], x = x, r[j]
        if x is not None: rows.append([x])
    return [len(r) for r in rows]
def partitions(n, maxpart=None):
    if maxpart is None: maxpart = n
    if n == 0: yield []; return
    for k in range(min(n, maxpart), 0, -1):
        for p in partitions(n - k, k): yield [k] + p
def dims(lam, d):   # (dim of U(d) irrep, dim of S_t irrep) via hook-content and hook length formulas
    t = sum(lam); conj = [sum(1 for l in lam if l > j) for j in range(lam[0])] if lam else []
    hooks = [lam[i] - j + conj[j] - i - 1 for i in range(len(lam)) for j in range(lam[i])]
    num = 1.0
    for i in range(len(lam)):
        for j in range(lam[i]): num *= (d + j - i)
    H = math.prod(hooks); return num / H, math.factorial(t) / H
for d, t in ((2, 2), (3, 2), (2, 3), (4, 2), (2, 4), (5, 6), (20, 12)):
    E2 = E1 = tot = 0.0
    for lam in partitions(t):
        if len(lam) > d: continue
        a, b = dims(lam, d); p = a * b / d ** t; tot += p; E2 += p * sum(l * l for l in lam); E1 += p * lam[0]
    assert abs(tot - 1) < 1e-9
    print(f"exact d={d} t={t}: purity bound E[sum l^2]/t^2 = {E2/t**2:.4f}, E[l1] = {E1:.3f}")
for d, t in ((10, 100), (100, 100), (1000, 100), (30, 900), (1000, 1000), (100, 10000)):
    s1 = s2 = 0.0; R = 400
    for _ in range(R):
        sh = rsk_shape(rng.integers(0, d, size=t)); s1 += sh[0]; s2 += sum(l * l for l in sh)
    b = math.e * math.sqrt(t) + math.e ** 2 * t / d + 2
    assert s1 / R <= b
    print(f"MC d={d} t={t}: E[l1] ~ {s1/R:.1f}  (2 sqrt t + t/d = {2*math.sqrt(t)+t/d:.1f}, bound {b:.1f}); E[sum l^2]/t ~ {s2/R/t:.1f}")
