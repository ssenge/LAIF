"""Brute-force check of the block decision of pattern matching with a known pattern.

Block of w = max(1, m // 4) candidate starts [b, b + w). Common part M = x[s, s + L), s = b + w - 1, L = m - w + 1.
Candidate i = s - delta needs M = y[delta, delta + L). The decision uses only M's window set Delta, the least period q
of M, the q-run [l, r) of y around the windows, and the text breaks next to M; one candidate is verified at the end.
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

def brute(x, y, b):
    m = len(y); w = max(1, m // 4)
    return any(x[i:i + m] == y for i in range(b, b + w) if 0 <= i <= len(x) - m)

random.seed(1)
cases = 0; kinds = [0, 0, 0, 0]
for _ in range(60000):
    m = random.randint(1, 14); sig = random.choice([2, 2, 3])
    kind = random.random()
    if kind < 0.4:                                   # periodic or nearly periodic patterns
        p = random.randint(1, max(1, m // 2)); base = [random.randrange(sig) for _ in range(p)]
        y = [base[k % p] for k in range(m)]
        if random.random() < 0.5:
            y[random.randrange(m)] = random.randrange(sig)
    else:
        y = [random.randrange(sig) for _ in range(m)]
    n = random.randint(m, 4 * m + 6)
    if random.random() < 0.5:                        # texts built from pattern pieces
        x = []
        while len(x) < n:
            off = random.randrange(m); x += y[off:] if random.random() < 0.7 else [random.randrange(sig)]
        x = x[:n]
        if random.random() < 0.5:
            x[random.randrange(n)] = random.randrange(sig)
    else:
        x = [random.randrange(sig) for _ in range(n)]
    x, y = tuple(x), tuple(y)
    w = max(1, m // 4)
    for b in range(0, n - m + 1, w):
        got, k = decide(x, y, b)
        assert got == brute(x, y, b), (x, y, b)
        kinds[k] += 1; cases += 1
print("blocks checked:", cases, "by case (no window, one window, break, periodic):", kinds)

# Targeted: patterns with a long q-run and a break at one or both ends, texts with long q-runs.
random.seed(2)
kinds2 = [0, 0, 0, 0]
for _ in range(40000):
    sig = random.choice([2, 3]); q = random.randint(1, 3); base = [random.randrange(sig) for _ in range(q)]
    a, c = random.randint(0, 3), random.randint(0, 3); run = random.randint(4, 16)
    y = [random.randrange(sig) for _ in range(a)] + [base[k % q] for k in range(run)] + [random.randrange(sig) for _ in range(c)]
    m = len(y)
    x = [random.randrange(sig) for _ in range(random.randint(0, m))] + [base[k % q] for k in range(random.randint(run, 3 * m))]
    x += [random.randrange(sig) for _ in range(random.randint(0, m))]
    if len(x) < m:
        continue
    for _ in range(random.randint(0, 2)):
        x[random.randrange(len(x))] = random.randrange(sig)
    if random.random() < 0.5:                        # plant an occurrence
        i = random.randint(0, len(x) - m); x[i:i + m] = y
    x, y = tuple(x), tuple(y); w = max(1, m // 4)
    for b in range(0, len(x) - m + 1, w):
        got, k = decide(x, y, b)
        assert got == brute(x, y, b), (x, y, b)
        kinds2[k] += 1
print("targeted blocks by case:", kinds2)
