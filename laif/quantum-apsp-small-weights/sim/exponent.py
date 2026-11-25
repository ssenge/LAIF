"""Exponent tau of the quantum APSP algorithm for directed graphs with integer weights in {-M..M} (README, Theorem 1).
Bridging-set iteration of [2], scale s = n^l, bridging set of n^{1-l} vertices, entries at most M s. Per scale the cheaper of
  bounded min-plus product by the encoding of [3] and rectangular multiplication: n^{l + w(1, 1-l, 1)},
  quantum minimum finding [4] over the bridging set for each pair: n^{2 + (1-l)/2},
so tau = max over l in [0, 1] of the minimum. w(1, k, 1) is convex in k and at least 2, so the lower convex
hull of published points is an upper bound for it.
Asserts: tau = 2.413455 with the bounds of [5, Table 1]; tau = 19/8 on the segment from (1/2, 2) to (1, 9/4), so tau <= 19/8 if w <= 9/4 and w(1, 1/2, 1) = 2 [6, 7, 8]; tau = 7/3 if w = 2;
tau below the quantum bound (5 + w)/3 implied by [1] and below the classical 2 + mu of [2].
Run: python exponent.py
"""
import numpy as np
def hull(points):
    pts = sorted(points)
    def w(k):
        best = np.inf
        for (a, fa) in pts:                      # best convex combination of two points around k
            for (b, fb) in pts:
                if a <= k <= b and b > a:
                    best = min(best, fa + (fb - fa) * (k - a) / (b - a))
                elif a == b == k:
                    best = min(best, fa)
        return max(best, 2.0)
    return w
def tau(w, grid=200001):
    ls = np.linspace(0, 1, grid)
    costs = [min(l + w(1 - l), 2.5 - l / 2) for l in ls]
    i = int(np.argmax(costs))
    return costs[i], ls[i]
def mu_of(w):
    lo, hi = 0.0, 1.0
    for _ in range(100):
        mid = (lo + hi) / 2
        lo, hi = (mid, hi) if w(mid) > 1 + 2 * mid else (lo, mid)
    return hi
cases = {
    # published: [5, Table 1], with w < 2.371177 as stated there; w(1, 0, 1) = 2
    "published": [(0.0, 2.0), (0.33, 2.000092), (0.34, 2.000520), (0.35, 2.001243), (0.40, 2.009280),
                  (0.50, 2.042776), (0.5275, 2.054999), (0.60, 2.092351), (0.70, 2.152770), (0.80, 2.220639),
                  (0.90, 2.293941), (1.0, 2.371177)],
    # condition: w <= 9/4 and w(1, 1/2, 1) = 2 [6, 7, 8]; by convexity w(1, k, 1) lies on or below this segment
    "omega 9/4": [(0.0, 2.0), (0.5, 2.0), (1.0, 2.25)],
    "omega 2": [(0.0, 2.0), (1.0, 2.0)],
}
for name, pts in cases.items():
    w = hull(pts)
    t, l = tau(w)
    om = w(1.0)
    print(f"{name:10s}: tau = {t:.6f} at l = {l:.4f};  (5+w)/3 = {(5 + om) / 3:.6f};  classical 2+mu = {2 + mu_of(w):.6f}")
w94 = hull(cases["omega 9/4"])
t94, _ = tau(w94)
assert abs(t94 - 19 / 8) < 1e-5
assert abs(tau(hull(cases["omega 2"]))[0] - 7 / 3) < 1e-5
tp, _ = tau(hull(cases["published"]))
assert abs(tp - 2.413455) < 2e-6 and tp < (5 + 2.371177) / 3 and tp < 2 + 0.5275
print("checks passed")
