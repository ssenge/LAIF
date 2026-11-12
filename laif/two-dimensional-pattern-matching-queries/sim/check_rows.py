"""Brute-force check of Theorem 7: two-dimensional matching of a known pattern by one-dimensional matching of rows.

For a column offset c, the rows T[r][c:c+m2] form a string x over the alphabet of rows, and the pattern rows form
y. P occurs at (r, c) iff y occurs in x at r. The block decision of the one-dimensional algorithm (windows of
w = max(1, m1 // 4) starts, least period of the common part, breaks next to it) is run on x and compared with brute
force for every block and every column offset.
"""
import random

def period(s):
    return next(p for p in range(1, len(s) + 1) if all(s[k] == s[k + p] for k in range(len(s) - p)))

def decide(x, y, b):
    m = len(y); w = max(1, m // 4); s = b + w - 1; L = m - w + 1
    cands = [d for d in range(w) if 0 <= s - d <= len(x) - m]
    M = x[s:s + L]
    if len(M) < L:
        return False, 0
    D = [d for d in cands if y[d:d + L] == M]
    if not D:
        return False, 0
    if len(D) == 1:
        i = s - D[0]
        return x[i:i + m] == y, 1
    q = period(M)
    for d1, d2 in zip(D, D[1:]):
        assert (d2 - d1) % q == 0                      # differences are multiples of q
    lo, hi = D[0], D[-1] + L
    assert all(y[k] == y[k + q] for k in range(lo, hi - q))   # union of the windows is q-periodic
    l = lo
    while l > 0 and y[l - 1] == y[l - 1 + q]:
        l -= 1
    r = hi
    while r < m and y[r] == y[r - q]:
        r += 1
    lam = next((j for j in range(s - 1, max(-1, s - m - 1), -1) if j + q < len(x) and x[j] != x[j + q]), None)
    rho = next((j for j in range(s + L, min(len(x), s + L + m)) if x[j] != x[j - q]), None)
    if l > 0:
        if lam is None:
            return False, 2
        i = lam - l + 1
        return (s - i) in D and x[i:i + m] == y, 2
    if r < m:
        if rho is None:
            return False, 2
        i = rho - r
        return (s - i) in D and x[i:i + m] == y, 2
    # y is q-periodic: no verification, only the breaks
    lo_ok = -1 if lam is None else lam
    hi_ok = len(x) if rho is None else rho
    return any(lo_ok < s - d and s - d + m <= hi_ok for d in D), 3

def occurs(T, P, r, c):
    return all(T[r + i][c:c + len(P[0])] == P[i] for i in range(len(P)))

random.seed(7)
blocks = found = periodic = 0; kinds = [0, 0, 0, 0]
for _ in range(20000):
    m1, m2 = random.randint(1, 16), random.randint(1, 4); sig = random.choice([2, 2, 3])
    if random.random() < 0.5:                        # patterns with a short period of the rows
        p = random.randint(1, max(1, m1 // 2)); base = [tuple(random.randrange(sig) for _ in range(m2)) for _ in range(p)]
        P = [base[k % p] for k in range(m1)]
        if random.random() < 0.5:
            k = random.choice([0, m1 - 1, random.randrange(m1)]); P[k] = tuple(random.randrange(sig) for _ in range(m2))
        periodic += 1
    else:
        base = None
        P = [tuple(random.randrange(sig) for _ in range(m2)) for _ in range(m1)]
    n1, n2 = random.randint(m1, 4 * m1 + 6), random.randint(m2, 3 * m2 + 3)
    u = random.random()
    if base is not None and u < 0.4:                 # long periodic runs of rows, with planted copies of P
        c0 = random.randint(0, n2 - m2)
        T = [[random.randrange(sig) for _ in range(n2)] for _ in range(n1)]
        for r in range(n1):
            T[r][c0:c0 + m2] = list(base[(r + random.choice([0, 0, 0, 0, 1])) % p] if random.random() < 0.97 else
                                    tuple(random.randrange(sig) for _ in range(m2)))
        for _ in range(random.randint(0, 2)):
            r0 = random.randint(0, n1 - m1)
            for k in range(m1):
                T[r0 + k][c0:c0 + m2] = list(P[k])
    elif u < 0.7:                                    # texts built from rows and pieces of the pattern
        T = [[random.randrange(sig) for _ in range(n2)] for _ in range(n1)]
        c0 = random.randint(0, n2 - m2); r = 0
        while r < n1:
            off = random.randrange(m1)
            for k in range(off, m1):
                if r < n1:
                    T[r][c0:c0 + m2] = list(P[k]); r += 1
            r += random.random() < 0.3
        if random.random() < 0.5:
            T[random.randrange(n1)][random.randrange(n2)] = random.randrange(sig)
    else:
        T = [[random.randrange(sig) for _ in range(n2)] for _ in range(n1)]
    T = [tuple(row) for row in T]
    y = tuple(P); w = max(1, m1 // 4)
    for c in range(n2 - m2 + 1):
        x = tuple(row[c:c + m2] for row in T)
        for b in range(0, n1 - m1 + 1, w):
            got, kind = decide(x, y, b)
            want = any(occurs(T, P, i, c) for i in range(b, min(b + w, n1 - m1 + 1)))
            assert got == want, (P, T, c, b)
            blocks += 1; found += want; kinds[kind] += 1
print("patterns:", 20000, "with periodic rows:", periodic, "blocks:", blocks, "with an occurrence:", found,
      "decided by no window / one window / a break / the periodic case:", kinds)
