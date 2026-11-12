"""Brute-force check of the block decision for dictionary matching with a known dictionary D of patterns of length m.

Block of w = max(1, m // 4) starts [b, b + w), s = b + w - 1, L = m - w + 1, M = x[s, s + L).
For each pattern y: Delta_y = {delta < w : s - delta is a start, y[delta, delta + L) = M}, and the run [l_y, r_y) is the
largest interval around the windows of y on which y has the least period q of M.
The decision uses only M, the breaks lam and rho of the text next to M, the longest left part alpha* = y[0, l_y)
that ends the text at lam, and the longest right part beta* = y[r_y, m) that starts the text at rho.
"""
import random

def period(s):
    return next(p for p in range(1, len(s) + 1) if all(s[k] == s[k + p] for k in range(len(s) - p)))

def decide(x, D, b):
    m = len(D[0]); n = len(x); w = max(1, m // 4); s = b + w - 1; L = m - w + 1
    if s + L > n:
        return False
    M = x[s:s + L]
    q = period(M)
    lam = next((j for j in range(s - 1, max(-1, s - m - 1), -1) if x[j] != x[j + q]), None)
    rho = next((j for j in range(s + L, min(n, s + L + m)) if x[j] != x[j - q]), None)
    # longest left part ending at lam and longest right part starting at rho (the two trie walks)
    info = []
    for y in D:
        Dl = [d for d in range(w) if 0 <= s - d <= n - m and y[d:d + L] == M]
        if not Dl:
            continue
        lo, hi = Dl[0], Dl[-1] + L
        assert all(y[k] == y[k + q] for k in range(lo, hi - q))     # windows of y lie in one q-periodic run
        l = lo
        while l > 0 and y[l - 1] == y[l - 1 + q]:
            l -= 1
        r = hi
        while r < m and y[r] == y[r - q]:
            r += 1
        info.append((y, Dl, l, r))
    STATS['patterns with windows ≥ 2'] += len(info) >= 2
    STATS['left part'] += any(l > 0 for _, _, l, _ in info)
    STATS['right part'] += any(r < m for _, _, _, r in info)
    STATS['periodic'] += any(l == 0 and r == m for _, _, l, r in info)
    A = [] if lam is None else x[max(0, lam - m + 1):lam + 1]
    B = [] if rho is None else x[rho:rho + m]
    lefts = [y[:l] for y, Dl, l, r in info if l > 0]
    rights = [y[r:] for y, Dl, l, r in info if r < m]
    if lefts:
        walk([tuple(reversed(a)) for a in lefts], tuple(reversed(A)))
        STATS['walks'] += 1
    if rights:
        walk(rights, tuple(B))
        STATS['walks'] += 1
    a_star = max((a for a in lefts if len(a) <= len(A) and tuple(A[len(A) - len(a):]) == a), key=len, default=None)
    b_star = max((c for c in rights if len(c) <= len(B) and tuple(B[:len(c)]) == c), key=len, default=None)
    # from here on no queries: every pattern is decided by lam, rho, a_star, b_star
    for y, Dl, l, r in info:
        lo_ok = -1 if lam is None else lam
        hi_ok = n if rho is None else rho
        if l > 0:
            if lam is None:
                continue
            t = lam - l + 1
            if s - t not in Dl:
                continue
            if a_star is None or len(a_star) < l or a_star[len(a_star) - l:] != y[:l]:
                continue
        elif r < m:
            if rho is None:
                continue
            t = rho - r
            if s - t not in Dl or not lo_ok < t:
                continue
        else:                                                  # y is q-periodic: Lemma 2(3)
            if any(lo_ok < s - d and s - d + m <= hi_ok for d in Dl):
                return True
            continue
        if r < m:
            if rho != t + r:
                continue
            if b_star is None or len(b_star) < m - r or b_star[:m - r] != y[r:]:
                continue
        elif not t + m <= hi_ok:
            continue
        return True
    return False

def walk(Z, u):
    """Heavy-path walk of Lemma 2 on the trie of Z with the unknown string u. Returns pi, the rounds and the searched
    lengths; asserts the bounds of Lemma 2."""
    Z = list(set(Z)); k = len(Z)
    def weight(pre):
        return sum(1 for z in Z if z[:len(pre)] == pre)
    def heavy(pre):                                             # label of the heavy path from node pre
        while True:
            kids = {z[len(pre)] for z in Z if len(z) > len(pre) and z[:len(pre)] == pre}
            if not kids:
                return pre
            pre = max((pre + (c,) for c in kids), key=lambda v: (weight(v), v))
    v = (); rounds = 0; gaps = []
    while True:
        rounds += 1
        z = heavy(v); p0 = len(v)
        p = next((j for j in range(p0, len(z)) if j >= len(u) or u[j] != z[j]), None)
        if p is None:
            gaps.append(len(z) - p0); pi = len(z); break
        gaps.append(p - p0 + 1)
        if p >= len(u):
            pi = p; break
        child = z[:p] + (u[p],)
        if weight(child) == 0:
            pi = p; break
        assert 2 * weight(child) <= weight(z[:p])               # a light child has at most half the weight
        v = child
    assert rounds <= (k.bit_length()) + 1 and sum(gaps) <= len(u) + 1, (rounds, k, gaps)
    best = max((j for j in range(len(u) + 1) if any(z[:j] == tuple(u[:j]) for z in Z)), default=0)
    assert pi == best, (pi, best)
    return pi, rounds, gaps

def brute(x, D, b, m):
    w = max(1, m // 4)
    return any(tuple(x[i:i + m]) in D for i in range(b, b + w) if 0 <= i <= len(x) - m)

def pattern(m, sig):
    u = random.random()
    if u < 0.5:
        p = random.randint(1, max(1, m // 2)); base = [random.randrange(sig) for _ in range(p)]
        y = [base[k % p] for k in range(m)]
        for _ in range(random.choice([0, 1, 1, 2])):
            y[random.choice([0, m - 1, random.randrange(m)])] = random.randrange(sig)
        return tuple(y), base
    return tuple(random.randrange(sig) for _ in range(m)), None

STATS = {'patterns with windows ≥ 2': 0, 'left part': 0, 'right part': 0, 'periodic': 0, 'walks': 0}
random.seed(11)
blocks = found = 0
for trial in range(20000):
    m = random.randint(1, 16); sig = random.choice([2, 2, 3]); d = random.choice([1, 2, 3, 5, 8])
    first, base = pattern(m, sig)
    D = [first]
    while len(D) < d:
        if base is not None and random.random() < 0.6:          # more patterns from the same periodic run
            p = len(base); o = random.randrange(p); y = [base[(k + o) % p] for k in range(m)]
            for _ in range(random.choice([1, 1, 2])):
                y[random.choice([0, 1, m - 2, m - 1, random.randrange(m)]) % m] = random.randrange(sig)
            y = tuple(y)
        else:
            y = pattern(m, sig)[0]
        D.append(y)
    D = list(dict.fromkeys(D))
    n = random.randint(m, 4 * m + 6)
    if base is not None and random.random() < 0.6:              # long periodic runs with planted patterns
        p = len(base); x = [base[k % p] if random.random() < 0.97 else random.randrange(sig) for k in range(n)]
        for _ in range(random.randint(0, 2)):
            y = random.choice(D); i = random.randint(0, n - m); x[i:i + m] = list(y)
    else:
        x = [random.randrange(sig) for _ in range(n)]
        for _ in range(random.randint(0, 2)):
            y = random.choice(D); i = random.randint(0, n - m); x[i:i + m] = list(y)
            if random.random() < 0.3:
                x[random.randrange(n)] = random.randrange(sig)
    x = tuple(x); Dset = set(D)
    w = max(1, m // 4)
    for b in range(0, n - m + 1, w):
        got = decide(x, D, b); want = brute(x, Dset, b, m)
        assert got == want, (x, D, b, got, want)
        blocks += 1; found += want
print("dictionaries:", 20000, "blocks:", blocks, "with an occurrence:", found, "blocks with:", STATS)

# Lemma 2 on larger tries: random sets, sets of prefixes of one string, and sets close to the unknown string
random.seed(12)
maxr = 0
for trial in range(3000):
    h = random.randint(1, 24); sig = random.choice([2, 3])
    u = tuple(random.randrange(sig) for _ in range(h))
    kind = random.random(); Z = []
    for _ in range(random.randint(1, 200)):
        if kind < 0.4:
            z = list(u[:random.randint(0, h)])
            z += [random.randrange(sig) for _ in range(random.randint(0, h - len(z)))]
        elif kind < 0.7:
            z = list(u); z[random.randrange(h)] = random.randrange(sig); z = z[:random.randint(1, h)]
        else:
            z = [random.randrange(sig) for _ in range(random.randint(1, h))]
        Z.append(tuple(z))
    pi, rounds, gaps = walk(Z, u); maxr = max(maxr, rounds)
print("trie walks on larger sets: 3000, largest number of rounds:", maxr)
