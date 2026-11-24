"""Log-space evaluation of every failure bound of the proof of Theorem 1 (constants k = 2048, c_0 = 1/256).
Each line is the natural log of (failure probability) x (2 e^{d^2} for the conditioning on E) x (union counts);
all must be negative. Lemma 3 (ii) reports the least margin of R(s), which must be positive.
Grid: ln n in {520, 600, 700}, d from ceil(ln n) to the top of the range d^3 ln n <= n."""
import math, numpy as np
k, c0 = 2048, 1 / 256

def bounds(lnn, d):
    lnm = lnn - math.log(2); m = math.exp(lnm)
    L = lnm - math.log(2 * d * d); g = c0 * k / math.log(k * d); s1 = float(math.floor(g * m / d))
    mu = (64 / (3 * k)) * d * (math.log(math.e * k * d) + 2); ub = float(math.ceil(3 * d / L))
    cond = 2 * math.log(2) + d * d                    # 2 e^{d^2}, both sides
    out = {"B1": -(d * d / 2 - d) * (math.log(2) + lnm - 2 * math.log(d)) + d * d / 2 + lnn + cond}
    us = np.unique(np.concatenate([ub + np.arange(min(300, ub)), np.exp(np.linspace(math.log(ub), math.log(s1), 600))]).astype(float))
    us = us[(us >= ub) & (us <= s1)]
    b2a = b2b = -math.inf
    for u in us:
        cnt = u * (1 + lnm - math.log(u))            # ln C(m, u)
        b2a = max(b2a, -d * u * (0.9 * (lnm - math.log(d * u / 10)) - 0.1) + cnt + cond)
        M = mu * u; lmM = math.log(m - u) - math.log(M)
        b2b = max(b2b, M * (1 + lmM) - d * (d * u / 10 - u) * lmM + cnt + cond)
    out["B2 first"], out["B2 second"] = b2a, b2b
    cnt = 2 * s1 * (1 + lnm - math.log(s1))           # C(m, s1)^2
    y = g * m / 4; ds1 = d * s1
    t1 = y * (1 + lnm - math.log(y)) - ds1 * (lnm - math.log(y))
    t2 = -(y - s1) * ds1 / m
    out["B3"] = cnt + cond + max(t1, t2) + math.log(2)
    worst = math.inf
    for s in np.unique(np.concatenate([np.arange(1, min(ub + 3000, 10**5)), np.exp(np.linspace(0, math.log(s1), 800))])):
        f = d * d / 2 - s
        if s >= ub:
            f = max(f, (mu - 1) * s, 0.5 * (d * d / 2 - s) + 0.5 * (mu - 1) * s)
        worst = min(worst, 3 * k * f / (32 * d) - (s * (math.log(math.e * k * d / 4) + 1) + 2 * lnn + k))
    out["Lemma 3 margin"] = worst
    out["Lemma 4"] = k * math.log(2) - 3 * k * d / 64 + lnn
    for name, ok in [("mu s1 <= m/4", mu * s1 <= m / 4), ("mu <= d^2/40", mu <= d * d / 40), ("kp <= 1", k / (4 * d) <= 1),
                     ("km/(32d) >= 2 s1", k * m / (32 * d) >= 2 * s1), ("gamma < 2/e", g < 2 / math.e)]:
        assert ok, name
    return out

for lnn in [520, 600, 700]:   # d >= ln n >= 512 so that kp <= 1
    top = int(math.exp((lnn - math.log(lnn)) / 3))
    for d in sorted({math.ceil(lnn), 2 * math.ceil(lnn), int(math.sqrt(lnn * top)), top}):
        o = bounds(lnn, d)
        print(f"ln n = {lnn}, d = {d}: " + ", ".join(f"{a} {b:.3g}" for a, b in o.items()))
        assert all(v < 0 for a, v in o.items() if a != "Lemma 3 margin") and o["Lemma 3 margin"] > 0
print("all bounds hold on the grid")
