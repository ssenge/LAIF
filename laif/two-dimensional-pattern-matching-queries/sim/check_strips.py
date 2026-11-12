"""Two-dimensional pattern matching by strips. In the strip of rows r .. r+m1-1 every column is one character, and
the pattern becomes a string of m2 such characters. Within a strip the matches are found block by block:
- L is the smallest period of the column string of the pattern;
- a deterministic sample (stages z_t, values c_t, survivor f) is built from L copies of the pattern at shifts 0..L-1;
- aperiodic case (2L > m2): blocks of L starts, two extreme passers of the sample test are the only candidates;
- periodic case (2L <= m2): blocks of m2 - L starts, the L-periodic run through column B + m2 - 1 bounds the candidates,
  and one residue class mod L is found with the sample on at most L of them.
Every search and minimum finding is simulated exactly. Checks against brute force."""
import random

def smallest_period(P):
    m = len(P)
    return next(d for d in range(1, m + 1) if all(P[y] == P[y + d] for y in range(m - d)))

def sample(P, L, rng):
    """Deterministic sample of the copies j = 0..L-1 (copy j holds P at positions j..j+m-1)."""
    m = len(P)
    alive, ds = list(range(L)), []
    while len(alive) > 1:
        l, r = alive[0], alive[-1]
        diff = [z for z in range(r, l + m) if P[z - l] != P[z - r]]
        assert diff                                  # r - l < L is not a period
        z = rng.choice(diff)
        assert all(j <= z < j + m for j in alive)   # the column stabs every surviving copy
        c = rng.choice([P[z - l], P[z - r]])
        ds.append((z, c))
        alive = [j for j in alive if P[z - j] == c]
    f = alive[0]
    for j in range(L):                               # sample property
        if j != f:
            assert any(j <= z < j + m and P[z - j] != c for z, c in ds)
    return f, ds

def passes(S, x, f, ds):
    return all(S[x - f + z] == c for z, c in ds)

def match(S, P, x):
    return S[x:x + len(P)] == P

def candidates(S, lo, hi, f, ds, L):
    """At most two starts in [lo, hi) (hi - lo <= L) that can be matches, from two extreme passers."""
    assert hi - lo <= L
    pas = [x for x in range(lo, hi) if passes(S, x, f, ds)]
    if not pas:
        return []
    if 2 * f >= L:                                   # rightmost passers
        x1 = max(pas)
        rest = [x for x in pas if x < x1 - f]
    else:                                            # leftmost passers
        x1 = min(pas)
        rest = [x for x in pas if x >= x1 - f + L]
    return [x1] + ([max(rest) if 2 * f >= L else min(rest)] if rest else [])

def block_matches(S, P, B, L, f, ds):
    n, m = len(S), len(P)
    last = n - m                                     # last valid start
    if 2 * L > m:                                    # aperiodic: block of L starts
        E = min(B + L, last + 1)
        return {x for x in candidates(S, B, E, f, ds, L) if match(S, P, x)}
    K = m - L
    cs = B + m - 1                                   # every match in [B, B+K) has D = 0 on a range through cs
    cap = min(B + K - 1 + m, n)                      # matches end before cap
    D = lambda j: S[j] != S[j - L]
    g = max([j for j in range(B + L, min(cs, n - 1) + 1) if D(j)], default=B + L - 1)
    h = min([j for j in range(cs + 1, cap) if D(j)], default=cap)
    X = list(range(max(B, g - L + 1), min(B + K, h - m + 1, last + 1)))
    if not X:
        return set()
    Y = X[:L]
    star = [x for x in candidates(S, Y[0], Y[-1] + 1, f, ds, L) if match(S, P, x)]
    if not star:
        return set()
    return {x for x in X if (x - star[0]) % L == 0}

def strip_matches(S, P, rng):
    n, m = len(S), len(P)
    if m > n:
        return set()
    L = smallest_period(P)
    f, ds = sample(P, L, rng)
    step = L if 2 * L > m else m - L
    out = set()
    for B in range(0, n - m + 1, step):
        got = block_matches(S, P, B, L, f, ds)
        truth = {x for x in range(B, min(B + step, n - m + 1)) if match(S, P, x)}
        assert got == truth, (S, P, B, got, truth)
        out |= got
    return out

def matches_2d(T, P, rng):
    n1, n2, m1 = len(T), len(T[0]), len(P)
    cols = [tuple(P[i][j] for i in range(m1)) for j in range(len(P[0]))]
    res = set()
    for r in range(n1 - m1 + 1):
        S = [tuple(T[r + i][j] for i in range(m1)) for j in range(n2)]
        res |= {(r, c) for c in strip_matches(S, cols, rng)}
    return res

def brute_2d(T, P):
    n1, n2, m1, m2 = len(T), len(T[0]), len(P), len(P[0])
    return {(r, c) for r in range(n1 - m1 + 1) for c in range(n2 - m2 + 1)
            if all(T[r + i][c + j] == P[i][j] for i in range(m1) for j in range(m2))}

def periodic_string(m, rng, sigma):
    L = rng.randint(1, m)
    base = [rng.choice(sigma) for _ in range(L)]
    return [base[i % L] for i in range(m)]

if __name__ == "__main__":
    rng = random.Random(5)
    for _ in range(20000):                           # one dimension, periodic and aperiodic patterns
        m = rng.randint(1, 12); n = rng.randint(m, 40)
        sigma = "ab" if rng.random() < 0.6 else "abc"
        P = periodic_string(m, rng, sigma) if rng.random() < 0.6 else [rng.choice(sigma) for _ in range(m)]
        if rng.random() < 0.5:                       # text from shifted copies of the pattern with noise
            S = [P[(i + rng.randint(0, 2)) % m] if rng.random() < 0.95 else rng.choice(sigma) for i in range(n)]
            for _ in range(rng.randint(0, 3)):
                x = rng.randint(0, n - m); S[x:x + m] = P
        else:
            S = [rng.choice(sigma) for _ in range(n)]
        strip_matches(S, P, rng)
    cnt = 0
    for _ in range(1500):                            # two dimensions
        m1, m2 = rng.randint(1, 4), rng.randint(1, 6)
        n1, n2 = rng.randint(m1, 9), rng.randint(m2, 14)
        sigma = "ab"
        if rng.random() < 0.5:
            colpat = periodic_string(m2, rng, range(3))
            colset = [tuple(rng.choice(sigma) for _ in range(m1)) for _ in range(3)]
            P = [[colset[colpat[j]][i] for j in range(m2)] for i in range(m1)]
        else:
            P = [[rng.choice(sigma) for _ in range(m2)] for _ in range(m1)]
        T = [[rng.choice(sigma) for _ in range(n2)] for _ in range(n1)]
        for _ in range(rng.randint(0, 4)):
            r, c = rng.randint(0, n1 - m1), rng.randint(0, n2 - m2)
            for i in range(m1):
                for j in range(m2):
                    T[r + i][c + j] = P[i][j]
        assert matches_2d(T, P, rng) == brute_2d(T, P)
        cnt += 1
    print("block procedures agree with brute force on 20000 one-dimensional and", cnt, "two-dimensional instances")
