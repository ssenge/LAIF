"""Cost exponent of nested quantum minimum finding over the levels of recursive contraction (README, Theorem 1).
Level l contracts n_l -> n_{l+1} vertices at gate cost n_l^c (c = 2 for oblivious Boruvka with sorting networks);
a fixed minimum k-cut survives with probability (n_l/n_{l+1})^{-k} (times k^{-O(k^2)}, ignored here), so minimum
finding over seeds repeats it (n_l/n_{l+1})^{k/2} times. Unrolled, the cost is sum_l (n/n_{l+1})^{k/2} n_l^c
(exponents of n, constants per level ignored). With n_{l+1} = n_l^{2c/k} every level costs n^{k/2} (needs k > 2c).
Asserts: that schedule gives exponent k/2 for k > 2c; the schedule n_{l+1} = n_l^{2/k} of the classical recursion gives
k/2 + c - 1 at the top level; for k <= 2c the exponent tends to c as the first step shrinks.
"""
def cost_exponent(k, c, sched):
    """exponents e_l with n_l = n^{e_l}; returns max over levels of (1 - e_{l+1}) k/2 + e_l c"""
    return max((1 - b) * k / 2 + a * c for a, b in zip(sched, sched[1:]))
def schedule(q, depth=400):
    e = [1.0]
    for _ in range(depth):
        e.append(e[-1] * q)
    return e + [0.0]
for c in (2.0, 2.371177):
    for k in range(5, 11):
        if k > 2 * c:
            ex = cost_exponent(k, c, schedule(2 * c / k))
            assert abs(ex - k / 2) < 1e-6, (k, c, ex)
            ex_cl = cost_exponent(k, c, schedule(2 / k))
            assert abs(ex_cl - (k / 2 + c - 1)) < 1e-6, (k, c, ex_cl)
            print(f"c={c:.6f} k={k}: tuned schedule {ex:.4f}, classical schedule {ex_cl:.4f}")
for k in (3, 4):
    c = 2.0
    for eps in (0.1, 0.01, 0.001):
        ex = cost_exponent(k, c, schedule(1 - eps, depth=int(40 / eps)))
        assert ex <= c + k * eps / 2 + 1e-9, (k, eps, ex)
        print(f"c=2 k={k} eps={eps}: exponent {ex:.4f}")
print("checks passed")
