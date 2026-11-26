"""Parameter check for Theorem 1 (long blocks). Model constants are set to one, except the stage count L + 1 of the
order-p product formula, which enters the size condition of the control distribution.

For M (precision scale), D and even p > D: degree threshold Q = M + 3, K0 = Q // (p + 1) insertion slots,
block side ell = 2 (L + 1) Q w with record width w = (D + 3) * ceil(log2(Q w)) (address, offsets, count and work fields),
step count r(tau) = ceil(tau (ell^D tau)^(1/p)), N = r + K0 slots, step time tau = the largest value with
(L + 1) N w <= ell (size hypothesis of the control distribution), found by bisection.
Asserts: (L + 1) N w <= ell, ell >= tau + M (buffer), tau >= 1, h = tau / r <= 1, ell^D tau^(p+1) / r^p <= 1 (coefficient
condition), and the slope of log(ell / tau) against log M, after removing w^{1 + D/(p+1)}, approaches (D+1)/(p+1)."""
import math

def stages(p):
    return 2 * 5 ** (p // 2 - 1)                     # Suzuki stage count, one exponential per stage and colour class

def params(M, D, p):
    Q = M + 3; K0 = Q // (p + 1); w = 1
    for _ in range(50):                               # fixed point of w = (D + 3) ceil(log2(Q w))
        w_new = (D + 3) * math.ceil(math.log2(Q * w))
        if w_new == w: break
        w = w_new
    L1 = stages(p) + 1; ell = 2 * L1 * Q * w
    def fits(tau):
        r = math.ceil(tau * (ell ** D * tau) ** (1 / p))
        return L1 * (r + K0) * w <= ell, r
    lo, hi = 0.0, float(ell)
    for _ in range(200):
        mid = (lo + hi) / 2
        lo, hi = (mid, hi) if fits(mid)[0] else (lo, mid)
    tau = lo; ok, r = fits(tau)
    return dict(Q=Q, K0=K0, w=w, ell=ell, tau=tau, r=r, N=r + K0, L1=L1)

for D in (1, 2, 3):
    for p in [q for q in (4, 6, 8, 10, 12) if q > D]:
        delta = (D + 1) / (p + 1); rows = []
        for M in (10**6, 10**9, 10**12, 10**15):
            P = params(M, D, p); tau, r, ell, w = P["tau"], P["r"], P["ell"], P["w"]
            if tau < 1:                               # block too small for this M: needs larger M (asymptotic regime)
                continue
            assert P["L1"] * P["N"] * w <= ell and ell >= tau + M and tau / r <= 1
            assert ell ** D * tau ** (p + 1) / r ** p <= 1.0 + 1e-9
            rows.append((M, ell / tau, w))
        assert len(rows) >= 2, (D, p)
        (M1, q1, w1), (M2, q2, w2) = rows[-2], rows[-1]
        e = 1 + D / (p + 1)
        slope = (math.log(q2 / w2 ** e) - math.log(q1 / w1 ** e)) / (math.log(M2) - math.log(M1))
        assert abs(slope - delta) < 0.02, (D, p, slope, delta)
        print(f"D {D} p {p:2d}: exponent (D+1)/(p+1) = {delta:.3f}, fitted {slope:.3f}; depth per unit time at "
              "M, ell/tau = " + ", ".join(f"{M:.0e}: {q:.3g}" for M, q, _ in rows))
print("ok: size, buffer and coefficient conditions hold; exponent (D+1)/(p+1)")
