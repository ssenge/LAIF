"""Does any recursion u -> prod_m sigma_m(u) beat Yehuda's tribonacci growth on SU(2)?

A word u in the conjugate-pair normal form has imaginary components with weighted valuations
(A, B, C). The available images of u flip signs of components: the half-turns tau, rho, tau*rho
flip two, and taking an inverse flips all three, so all 8 sign patterns are available.
u is proportional to 1 + xi + yj + zk with x = X/r etc., and r is a unit, so valuations are kept
and the product of M images is an exact integer polynomial map in x, y, z.

The valuation of a component is at least the min over its monomials of aA + bB + cC. This is a
lower bound (rigorous), since x, y, z are not really independent. A map is one sign sequence.
Score: growth of min(A, B, C) against word length. Yehuda: x0 = 1.8393 per doubling.
"""
import math
import sys

import numpy as np

PATTERNS = [(sx, sy, sz) for sx in (1, -1) for sy in (1, -1) for sz in (1, -1)]
X0 = 1.8392867552141612  # real root of x^3 = x^2 + x + 1
DELTA = math.log2(X0)


def step(q, s, D):
    """q = (a0, a1, a2, a3) arrays indexed by powers of x, y, z; multiply by 1 + s.x i + s.y j + s.z k."""
    def sh(a, axis):
        out = np.zeros_like(a)
        idx = [slice(None)] * 3
        idx2 = [slice(None)] * 3
        idx[axis], idx2[axis] = slice(1, None), slice(None, -1)
        out[tuple(idx)] = a[tuple(idx2)]
        return out
    a, b, c, d = q
    sx, sy, sz = s
    return (a - sx * sh(b, 0) - sy * sh(c, 1) - sz * sh(d, 2),
            b + sx * sh(a, 0) + sz * sh(c, 2) - sy * sh(d, 1),
            c + sy * sh(a, 1) - sz * sh(b, 2) + sx * sh(d, 0),
            d + sz * sh(a, 2) + sy * sh(b, 1) - sx * sh(c, 0))


def pareto(a):
    """Minimal monomials (exponent vectors) of a polynomial array."""
    pts = [tuple(int(v) for v in p) for p in np.argwhere(a != 0)]
    return tuple(sorted(p for p in pts if not any(q != p and all(u <= v for u, v in zip(q, p)) for q in pts)))


def start(D):
    one = np.zeros((D, D, D), dtype=np.int64)
    one[0, 0, 0] = 1
    z = np.zeros((D, D, D), dtype=np.int64)
    return one, z, z.copy(), z.copy()


def key_of(q):
    return pareto(q[1]), pareto(q[2]), pareto(q[3])


def maps_of(M):
    """All distinct monomial maps from sign sequences of length M, first factor the identity."""
    D = M + 1
    out = {}
    def rec(q, seq):
        if len(seq) == M:
            out.setdefault(key_of(q), tuple(seq))
            return
        for s in PATTERNS:
            rec(step(q, s, D), seq + [s])
    rec(step(start(D), (1, 1, 1), D), [(1, 1, 1)])
    return out


def apply_map(key, v):
    def val(mons):
        return min((sum(e * w for e, w in zip(m, v) if e) for m in mons), default=math.inf)
    return tuple(val(mons) for mons in key)


def useful(maps):
    """Drop the maps that give the identity word, and duplicates on a set of test states."""
    tests = [(1, 1, 1), (1, 2, 3), (3, 1, 2), (2, 3, 1), (1, 3, 9), (9, 3, 1), (3, 9, 1), (5, 2, 3), (1, 5, 25), (25, 1, 5)]
    table = {}
    for k in maps:
        if any(k):
            table.setdefault(tuple(apply_map(k, t) for t in tests), k)
    return list(table.values())


def beam(library, seeds, horizon, width=3000):
    """library: list of (M, key). Maximise min(A,B,C) by word length (log2), keeping diverse states."""
    best = {}
    states = {0.0: set(tuple(v) for v in seeds)}
    while states:
        L = min(states)
        shaped = {}
        for v in states.pop(L):
            m = min(v)
            shape = tuple(round(x / m, 2) if math.isfinite(x) else -1 for x in v)
            if shape not in shaped or m > min(shaped[shape]):
                shaped[shape] = v
        top = sorted(shaped.values(), key=lambda v: -min(v))[:width]
        best[L] = max(min(v) for v in top)
        for M, k in library:
            nL = round(L + math.log2(M), 9)
            if nL <= horizon:
                for v in top:
                    w = apply_map(k, v)
                    if math.isfinite(min(w)):
                        states.setdefault(nL, set()).add(w)
    return best


if __name__ == "__main__":
    def key2(p):
        return key_of(step(step(start(3), (1, 1, 1), 3), p, 3))
    assert apply_map(key2((1, -1, -1)), (7, 11, 13)) == (7, 20, 18)  # tau
    assert apply_map(key2((-1, 1, -1)), (7, 11, 13)) == (24, 11, 18)  # rho
    print("self-check ok: Lemma 3.2 of Yehuda reproduced")

    maxM = int(sys.argv[1]) if len(sys.argv) > 1 else 6
    library = []
    for M in range(2, maxM + 1):
        raw = maps_of(M)
        kept = useful(raw)
        library += [(M, k) for k in kept]
        print(f"M={M}: {len(raw)} distinct maps, {len(kept)} kept", flush=True)
    seeds = [(5, 2, 3), (1, 2, math.inf)]
    for name, lib in (("M=2 only", [e for e in library if e[0] == 2]), ("all", library)):
        best = beam(lib, seeds, 40)
        pts = sorted(best)
        print(name)
        for L in [p for p in pts if abs(p - round(p)) < 1e-9 and round(p) in (10, 20, 30, 40)]:
            print(f"  log2 L={L:7.3f}  min val={best[L]:.4g}  log2(min val)/log2 L={math.log2(best[L]) / L:.5f}  (tribonacci {DELTA:.5f})", flush=True)
        a, b = [p for p in pts if p <= 30][-1], pts[-1]
        print(f"  local slope over last stretch: {(math.log2(best[b]) - math.log2(best[a])) / (b - a):.5f}")
