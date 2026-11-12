"""Two-dimensional blocks for a pattern that has been read in full.
Condition (star_b): the copies of P at the shifts s in [0, b)^2 are pairwise distinct on the common region
C = [b-1, m)^2 of all of them. Then a deterministic sample (cells z_t, values c_t, survivor f) exists with at most
ceil(log2 b^2) cells. In a block of b' x b' starts (b' = b // 2), every occurrence is a passer that no other passer
dominates in the order given by the side of f, so it lies on the front of the passers (learned by front_dc of the
empty rectangle scripts). A tournament with precomputed witnesses leaves one candidate, which is checked.
Checks against brute force."""
import math, random, sys
import os
HERE = os.path.dirname(os.path.abspath(__file__))
for d in ("largest-empty-rectangle-queries", "emptyrect"):     # published folder, working folder
    sys.path.insert(0, os.path.join(HERE, "..", "..", d, "sim"))
from check_window import front_dc, pareto

def star(P, b):
    m = len(P)
    S = [(i, j) for i in range(b) for j in range(b)]
    sig = {s: tuple(P[z1 - s[0]][z2 - s[1]] for z1 in range(b - 1, m) for z2 in range(b - 1, m)) for s in S}
    return len(set(sig.values())) == len(S)

def sample(P, b):
    m = len(P)
    alive, ds = [(i, j) for i in range(b) for j in range(b)], []
    while len(alive) > 1:
        s, t = alive[0], alive[-1]
        z = next((z1, z2) for z1 in range(b - 1, m) for z2 in range(b - 1, m)
                 if P[z1 - s[0]][z2 - s[1]] != P[z1 - t[0]][z2 - t[1]])
        cls = {}
        for j in alive:
            cls.setdefault(P[z[0] - j[0]][z[1] - j[1]], []).append(j)
        c = min(cls, key=lambda v: len(cls[v]))            # smallest class: at most half of the survivors
        ds.append((z, c)); alive = cls[c]
    f = alive[0]
    assert len(ds) <= math.ceil(math.log2(b * b)) if b > 1 else not ds
    for j in [(i, k) for i in range(b) for k in range(b)]:     # sample property
        if j != f:
            assert any(P[z[0] - j[0]][z[1] - j[1]] != c for z, c in ds)
    assert all(P[z[0] - f[0]][z[1] - f[1]] == c for z, c in ds)
    return f, ds

def witness(P, d):
    """A pattern cell u with P[u] != P[u - d], both inside the pattern (copies x and x + d differ at x + u)."""
    m = len(P)
    return next(((u1, u2) for u1 in range(m) for u2 in range(m)
                 if 0 <= u1 - d[0] < m and 0 <= u2 - d[1] < m and P[u1][u2] != P[u1 - d[0]][u2 - d[1]]), None)

def occurs(T, P, x):
    m = len(P)
    return all(T[x[0] + i][x[1] + j] == P[i][j] for i in range(m) for j in range(m))

LONG = [0]

def block(T, P, B, bb, f, ds, b, W):
    n, m = len(T), len(P)
    passes = lambda x: all(T[x[0] - f[0] + z[0]][x[1] - f[1] + z[1]] == c for z, c in ds)
    sg = [1 if f[i] >= b - 1 - f[i] else -1 for i in range(2)]
    starts = [(B[0] + i, B[1] + j) for i in range(bb) for j in range(bb)
              if B[0] + i <= n - m and B[1] + j <= n - m]
    Q = [x for x in starts if passes(x)]
    # map so that sigma-maximal passers become Pareto-minimal points of the front learner
    key = lambda x: (bb - 1 - sg[0] * (x[0] - B[0]) if sg[0] == 1 else x[0] - B[0],
                     bb - 1 - sg[1] * (x[1] - B[1]) if sg[1] == 1 else x[1] - B[1])
    pts = [key(x) for x in Q]
    cost = {}
    fr = front_dc(pts, 0, bb, 0, bb, cost)
    assert fr == pareto(pts)
    for lev, v in cost.items():
        assert v <= bb + 1e-9                               # sqrt(bb * bb) per depth
    inv = {key(x): x for x in Q}
    M = [inv[p] for p in fr]
    truth = {x for x in starts if occurs(T, P, x)}
    assert truth <= set(M), (truth, M)                     # every occurrence is on the front
    champ, duels = None, 0
    for y in M:
        if champ is None:
            champ = y; continue
        d = (y[0] - champ[0], y[1] - champ[1])
        u = W[d]
        v = T[champ[0] + u[0]][champ[1] + u[1]]; duels += 1
        if v != P[u[0]][u[1]]:                              # champion fails at its own cell
            champ = y
    assert duels <= max(0, len(M) - 1) and len(M) <= bb
    LONG[0] = max(LONG[0], len(M))
    got = {champ} if champ is not None and occurs(T, P, champ) else set()
    assert got == truth, (got, truth)
    return got

def run(T, P, b):
    n, m = len(T), len(P)
    f, ds = sample(P, b)
    bb = b // 2
    W = {}
    for d1 in range(-bb + 1, bb):
        for d2 in range(-bb + 1, bb):
            if (d1, d2) != (0, 0):
                W[(d1, d2)] = witness(P, (d1, d2)); assert W[(d1, d2)] is not None
    out = set()
    for B1 in range(0, n - m + 1, bb):
        for B2 in range(0, n - m + 1, bb):
            out |= block(T, P, (B1, B2), bb, f, ds, b, W)
    assert out == {(r, c) for r in range(n - m + 1) for c in range(n - m + 1) if occurs(T, P, (r, c))}
    return len(out)

if __name__ == "__main__":
    rng = random.Random(11)
    tried = held = found = 0
    while held < 400:
        m = rng.randint(6, 20); b = rng.randint(2, max(2, m // 2))
        sig = rng.choice([2, 2, 3])
        P = [[rng.randrange(sig) for _ in range(m)] for _ in range(m)]
        if rng.random() < 0.3:                              # sparse patterns, close to periodic
            P = [[1 if rng.random() < 0.08 else 0 for _ in range(m)] for _ in range(m)]
        tried += 1
        if not star(P, b):
            continue
        held += 1
        n = rng.randint(m, 3 * m)
        T = [[rng.randrange(sig) for _ in range(n)] for _ in range(n)]
        for _ in range(rng.randint(0, 8)):                  # overlapping copies make many passers
            r, c = rng.randint(0, n - m), rng.randint(0, n - m)
            for i in range(m):
                for j in range(m):
                    T[r + i][c + j] = P[i][j]
        for _ in range(rng.randint(0, 3)):
            T[rng.randrange(n)][rng.randrange(n)] = rng.randrange(sig)
        if rng.random() < 0.5:                              # force passers along chains and anti-diagonals
            f, ds = sample(P, b)
            for _ in range(rng.randint(1, 3 * b)):
                x0, y0 = rng.randint(0, n - m), rng.randint(0, n - m)
                for t in range(rng.randint(1, b)):
                    x = (min(n - m, x0 + t), max(0, y0 - t)) if rng.random() < 0.7 else (min(n - m, x0 + t), y0)
                    for z, c in ds:
                        T[x[0] - f[0] + z[0]][x[1] - f[1] + z[1]] = c
        found += run(T, P, b)
    adv = 0
    while adv < 300:                                        # incomparable passers inside one aligned block
        m = rng.randint(8, 22); b = rng.randint(4, max(4, m // 2))
        P = [[rng.randrange(2) for _ in range(m)] for _ in range(m)]
        if not star(P, b):
            continue
        adv += 1
        f, ds = sample(P, b); bb = b // 2
        n = rng.randint(m + bb, 2 * m + bb)
        T = [[rng.randrange(2) for _ in range(n)] for _ in range(n)]
        if rng.random() < 0.5:
            for i in range(m):
                for j in range(m):
                    T[i][j] = P[i][j]
        sg = [1 if f[i] >= b - 1 - f[i] else -1 for i in range(2)]
        B = (bb * rng.randint(0, (n - m) // bb), bb * rng.randint(0, (n - m) // bb))
        for t in range(bb):
            x = (B[0] + t, B[1] + (bb - 1 - t if sg[0] * sg[1] == 1 else t))
            if x[0] <= n - m and x[1] <= n - m:
                for z, c in ds:
                    T[x[0] - f[0] + z[0]][x[1] - f[1] + z[1]] = c
        found += run(T, P, b)
    print("blocks agree with brute force on", held, "pattern/text pairs with condition (star_b) (of", tried,
          "patterns drawn) and", adv, "targeted texts;", found, "occurrences; longest front", LONG[0])
