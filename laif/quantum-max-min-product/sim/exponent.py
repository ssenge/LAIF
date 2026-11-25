"""Exponents for quantum (max, min)-product (README, Theorem 1).
This work: AE-MonoEq triangle in n^{(5 + w)/3}, hence (max, min)-product in that time up to polylog factors.
Previous: n^{(5 - g)/2}, g the solution of g + 2 w(1 + g, 1 + g, 1) = 5 [1, Theorem 4.1], where
w(1 + g, 1 + g, 1) = (1 + g) w(1, 1/(1 + g), 1). w(1, k, 1) is convex in k and at least 2, so the lower
convex hull of published points bounds it from above; the previous bound is evaluated with the same hull.
Asserts: ours < previous for the published bounds of [3, Table 1], under w <= 9/4 with w(1, 1/2, 1) = 2, and for w = 2.
Run: python exponent.py
"""
def hull(points):
    pts = sorted(points)
    def w(k):
        best = min(fa + (fb - fa) * (k - a) / (b - a) for (a, fa) in pts for (b, fb) in pts if a <= k <= b and b > a)
        return max(best, 2.0)
    return w
def previous(w):
    lo, hi = 0.0, 1.0                      # f(g) = g + 2(1 + g) w(1/(1 + g)) - 5 is increasing in g
    for _ in range(200):
        g = (lo + hi) / 2
        lo, hi = (g, hi) if g + 2 * (1 + g) * w(1 / (1 + g)) < 5 else (lo, g)
    return (5 - hi) / 2
cases = {
    # [3, Table 1], points with k <= 1; w < 2.371177 is the entry of [3, Table 1] obtained in [6]
    "published": [(0.0, 2.0), (0.33, 2.000092), (0.34, 2.000520), (0.35, 2.001243), (0.40, 2.009280),
                  (0.50, 2.042776), (0.5275, 2.054999), (0.60, 2.092351), (0.70, 2.152770), (0.80, 2.220639),
                  (0.90, 2.293941), (1.0, 2.371177)],
    "omega 9/4": [(0.0, 2.0), (0.5, 2.0), (1.0, 2.25)],
    "omega 2": [(0.0, 2.0), (1.0, 2.0)],
}
res = {}
for name, pts in cases.items():
    w = hull(pts)
    ours, prev = (5 + w(1.0)) / 3, previous(w)
    res[name] = (ours, prev)
    print(f"{name:10s}: ours (5+w)/3 = {ours:.6f}   previous [1] = {prev:.6f}   classical (3+w)/2 = {(3 + w(1.0)) / 2:.6f}")
# the 2013 value of [1]: alpha = 0.302, w = 2.3727 gives at most 2.473
w13 = hull([(0.0, 2.0), (0.302, 2.0), (1.0, 2.3727)])
assert previous(w13) < 2.473
o, p = res["published"]
assert abs(o - 2.457059) < 1e-6 and o < p
assert res["omega 9/4"][0] < res["omega 9/4"][1] and abs(res["omega 2"][0] - 7 / 3) < 1e-9 and abs(res["omega 2"][1] - 2.4) < 1e-6
print("checks passed")
