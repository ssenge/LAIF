"""Parameter check for Theorem A (long blocks), all model constants set to 1 (shapes only, not constants).

For M (precision scale), D, even p > D: step tau = M log2 M, record width w = ceil(log2 ell), degree threshold Q = M + 2,
K0 = Q // (p + 1) insertion slots, r = ceil(tau (ell^D tau)^(1/p)) formula steps, N = r + K0 slots.
Block side ell is the least integer with ell >= max(N w, tau + M, Q w) (size hypothesis of Lemmas 12 / 26 of
arXiv:2610.01839 and the Lieb-Robinson buffer), found by a monotone search.
Asserts: every hypothesis holds at the chosen ell; the coefficient-sum proxy ell^D tau^(p+1) / r^p <= 1; h = tau / r <= 1;
the log-log slope of depth-per-unit-time ell / tau against tau approaches delta = (D+1)/(p-D) up to the log factors."""
import math

def side(M, D, p):
    tau = M * math.log2(M); Q = M + 2; K0 = Q // (p + 1)
    def ok(ell):
        w = math.ceil(math.log2(ell)); r = math.ceil(tau * (ell ** D * tau) ** (1 / p)); N = r + K0
        return ell >= max(N * w, tau + M, Q * w), r, N, w
    lo, hi = 2, 2
    while not ok(hi)[0]: hi *= 2
    while lo < hi:                       # ok is monotone in ell: ell grows faster than N w ~ ell^{D/p} log ell
        mid = (lo + hi) // 2
        if ok(mid)[0]: hi = mid
        else: lo = mid + 1
    _, r, N, w = ok(lo)
    return lo, tau, r, N, w, Q

for D in (1, 2, 3):
    for p in [q for q in (4, 6, 8, 10, 12) if q > 2 * D + 1]:
        delta = (D + 1) / (p - D); rows = []
        for M in (10**3, 10**5, 10**7, 10**9):
            ell, tau, r, N, w, Q = side(M, D, p)
            assert N * w <= ell and Q * w <= ell and ell >= tau + M and r >= tau
            assert ell ** D * tau ** (p + 1) / r ** p <= 1.0 + 1e-9
            rows.append((M, ell / tau, w, tau))
        # slope of log(ell/tau) - log factor (w^{p/(p-D)}) against log tau
        (M1, q1, w1, t1), (M2, q2, w2, t2) = rows[-2], rows[-1]
        slope = (math.log(q2 / w2 ** (p / (p - D))) - math.log(q1 / w1 ** (p / (p - D)))) / (math.log(t2) - math.log(t1))
        assert abs(slope - delta) < 0.03, (D, p, slope, delta)
        print(f"D {D} p {p:2d}: delta {delta:.3f}, slope {slope:.3f}; depth/time at M = 1e3..1e9: "
              + ", ".join(f"{q:.3g}" for _, q, _, _ in rows) + "  (baseline M: 1e3..1e9)")
print("ok: size hypotheses hold, coefficient proxy <= 1, h <= 1, exponent (D+1)/(p-D)")
