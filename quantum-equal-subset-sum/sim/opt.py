"""Exponents (base 2, per n) for Equal Subset Sum as a function of the zero density p
of a minimum-support balanced solution. Heuristic exploration, not a proof."""
import math

def H(*q):
    s = sum(q)
    return -sum(x/s*math.log2(x/s) for x in q if x > 0) if s > 0 else 0.0

def seven_sum(p):           # 7 blocks of typed vectors, M^2
    return (H(p, 1-p) + 1 - p) * 2 / 7

def inner(u, l):            # table l+sigma vs sqrt(s) * claw on bins of size u-l-sigma
    sigma = max(0.0, (4*u - 10*l) / 7)
    return max(l + sigma, sigma/2 + 2*(u - l - sigma)/3)

def collide(p):             # X, Y all of {0,1}^n, l = p
    return inner(1.0, p)

def scheme(p, a1, a0, t=0.5):
    """Labels A ({0,1},{0,1}), B ({0,1,2},{1}), C ({1},{0,1,2}), symmetric under B<->C, +<->-.
    Returns (assignment cost a, u, l), or None if the array is not a distribution."""
    b1, b0 = ((1-p) - 2*a1) / 4, (p - a0) / 2
    if min(a1, a0, b1, b0) < 0:
        return None
    ca, cb = 2*a1 + a0, 2*b1 + b0
    cols = [ca, cb, cb]
    HL = H(*cols)
    rows = {-1: [a1, b1, b1], 0: [a0, b0, b0], 1: [a1, b1, b1]}
    HLgivenD = sum(sum(r) * H(*r) for r in rows.values())
    a = max(0.0, HL - HLgivenD)
    x1 = a1 + t*a0
    u = ca * H(x1, ca - x1) + cb * H(b1, b0, b1)
    l = a0 * H(t, 1-t)
    return a, u, l

def best(p, cost, steps=120):
    v = (math.inf, None)
    for i in range(steps+1):
        for j in range(steps+1):
            a1, a0 = i/steps*(1-p)/2, j/steps*p
            r = scheme(p, a1, a0)
            if r:
                c = cost(*r)
                if c < v[0]:
                    v = (c, (a1, a0))
    return v

classical = lambda a, u, l: a + u - l
quantum = lambda a, u, l: a/2 + inner(u, l)

if __name__ == "__main__":
    # check against the published classical exponent, log2(5/3) at p = 1/5
    c, arg = best(0.2, classical, 240)
    print(f"classical at p=0.2: {c:.5f} (log2(5/3) = {math.log2(5/3):.5f}) at a1,a0={arg}")
    print(" p     7sum    collide labels  best")
    worst = (0, None)
    for k in range(5, 96):
        p = k/200
        s, co = seven_sum(p), collide(p)
        la, _ = best(p, quantum)
        m = min(s, co, la)
        if m > worst[0]:
            worst = (m, p)
        if k % 5 == 0:
            print(f"{p:.3f} {s:.4f} {co:.4f} {la:.4f} {m:.4f}")
    print("max over p of best exponent:", worst, " baseline 3^(2n/7):", 2/7*math.log2(3))
    print("max over p, without labels :", max(min(seven_sum(k/2000), collide(k/2000)) for k in range(1, 1000)))
