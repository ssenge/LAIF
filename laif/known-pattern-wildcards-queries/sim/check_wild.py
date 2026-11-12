"""Brute-force check of the block decision for matching a known pattern with k wildcards ('?').

R = [o, o + l) is a longest run of fixed positions of P. A block holds the starts t in [b, b + w), w = max(1, l // 4).
Queries of the block: M = x[s, s + L) with s = b + o + w - 1, L = l - w + 1 (identified among the windows of R), the
breaks lam, rho of the q-periodic extension W of M, and the checks of the exposed candidates (at most 2k + 2 of them).
Everything else is computed from P, M, lam and rho alone.
"""
import random

def period(s):
    return next(p for p in range(1, len(s) + 1) if all(s[i] == s[i + p] for i in range(len(s) - p)))

def longest_run(P):
    best, i = (0, 0), 0
    while i < len(P):
        if P[i] == '?':
            i += 1; continue
        j = i
        while j < len(P) and P[j] != '?':
            j += 1
        best = max(best, (j - i, -i)); i = j
    return -best[1], best[0]

def occurs(x, P, t):
    return 0 <= t <= len(x) - len(P) and all(c == '?' or x[t + i] == c for i, c in enumerate(P))

def decide(x, P, b):
    n, m = len(x), len(P); k = P.count('?')
    o, l = longest_run(P); w = max(1, l // 4); s = b + o + w - 1; L = l - w + 1
    starts = [t for t in range(b, b + w) if t <= n - m]
    if not starts or s + L > n:
        return False, 0
    M = x[s:s + L]                                            # identification among the windows of R
    R = P[o:o + l]
    Dl = [d for d in range(w) if R[d:d + L] == M]
    if not Dl:
        return False, 0
    q = period(M)
    W = lambda j: M[(j - s) % q]
    lam = next((j for j in range(s - 1, b - 1, -1) if x[j] != W(j)), b - 1)
    hi = min(n, b + w - 1 + m)
    rho = next((j for j in range(s + L, hi) if x[j] != W(j)), hi)
    F = [i for i, c in enumerate(P) if c != '?']
    cand = [t for t in starts if all(P[i] == W(t + i) for i in F if lam < t + i < rho)]     # C(t), no queries
    assert len({(s - t - o) % q for t in cand}) <= 1           # all candidates in one class mod q
    for t in cand:
        assert s - t - o in Dl
    exposed, free = [], False
    for t in cand:
        left, right = t <= lam, t + m - 1 >= rho
        if left and P[lam - t] != '?' and P[lam - t] == W(lam):
            continue                                           # x_lam != W(lam) = P_(lam - t)
        if right and P[rho - t] != '?' and P[rho - t] == W(rho) and rho < n:
            continue
        if not left and not right:
            free = True                                        # every fixed position lies in the periodic region
        else:
            exposed.append(t)
    nl = sum(1 for t in exposed if t <= lam)
    nr = sum(1 for t in exposed if t + m - 1 >= rho)
    assert nl <= k + 1 and nr <= k + 1, (nl, nr, k)
    if free:
        return True, len(exposed)
    # the queried checks: an OR over exposed t of the ANDs over the fixed positions outside (lam, rho)
    return any(all(x[t + i] == P[i] for i in F if not lam < t + i < rho) for t in exposed), len(exposed)

def pattern(m, sig, k):
    P = [random.randrange(sig) for _ in range(m)]
    if random.random() < 0.5:                                  # periodic patterns
        p = random.randint(1, max(1, m // 3)); P = [P[i % p] for i in range(m)]
        for _ in range(random.choice([0, 1, 2])):
            P[random.randrange(m)] = random.randrange(sig)
    P = [str(c) for c in P]
    for i in random.sample(range(m), min(k, m - 1)):
        P[i] = '?'
    return ''.join(P)

random.seed(5)
blocks = found = maxexp = 0
for trial in range(40000):
    m = random.randint(3, 22); sig = random.choice([2, 2, 3]); k = random.choice([0, 1, 1, 2, 3, 5])
    P = pattern(m, sig, k)
    n = random.randint(m, 4 * m + 8)
    if random.random() < 0.6:
        base = [c for c in P if c != '?'][:random.randint(1, 4)] or ['0']
        x = [base[i % len(base)] if random.random() < 0.95 else str(random.randrange(sig)) for i in range(n)]
    else:
        x = [str(random.randrange(sig)) for _ in range(n)]
    for _ in range(random.randint(0, 2)):
        t = random.randint(0, n - m)
        for i, c in enumerate(P):
            if c != '?':
                x[t + i] = c
        if random.random() < 0.3:
            x[random.randrange(n)] = str(random.randrange(sig))
    x = ''.join(x)
    o, l = longest_run(P); w = max(1, l // 4)
    for b in range(0, n - m + 1, w):
        got, e = decide(x, P, b)
        want = any(occurs(x, P, t) for t in range(b, b + w))
        assert got == want, (x, P, b, got, want)
        blocks += 1; found += want; maxexp = max(maxexp, e)
print("patterns:", 40000, "blocks:", blocks, "with an occurrence:", found, "most exposed candidates:", maxexp)

# many wildcards in long periodic patterns, where the exposed candidates are most numerous
random.seed(6)
blocks = maxexp = 0
for trial in range(6000):
    m = random.randint(16, 48); sig = 2; p = random.randint(1, 3)
    base = [str(random.randrange(sig)) for _ in range(p)]
    P = [base[i % p] for i in range(m)]
    k = random.randint(1, m // 2)
    for i in random.sample(range(m), k):
        P[i] = '?'
    if random.random() < 0.5:
        P[random.choice([0, m - 1])] = str(1 - int(base[0]))
    P = ''.join(P); k = P.count('?')
    n = random.randint(m, 3 * m)
    x = [base[i % p] if random.random() < 0.97 else str(random.randrange(sig)) for i in range(n)]
    x = ''.join(x)
    o, l = longest_run(P); w = max(1, l // 4)
    for b in range(0, n - m + 1, w):
        got, e = decide(x, P, b)
        assert got == any(occurs(x, P, t) for t in range(b, b + w)), (x, P, b)
        blocks += 1; maxexp = max(maxexp, e)
print("long periodic patterns:", 6000, "blocks:", blocks, "most exposed candidates:", maxexp)

# families where k starts are admissible on one side
random.seed(7)
blocks = maxexp = 0
for trial in range(4000):
    k = random.randint(1, 8); l = random.randint(4, 24)
    fam = random.choice(['?k0l', '0l?k', '?k0l?k', '1?k0l?k1', '?k01'])
    P = {'?k0l': '?' * k + '0' * l, '0l?k': '0' * l + '?' * k, '?k0l?k': '?' * k + '0' * l + '?' * k,
         '1?k0l?k1': '1' + '?' * k + '0' * l + '?' * k + '1', '?k01': '?' * k + '01' * (l // 2)}[fam]
    m = len(P); kk = P.count('?')
    n = random.randint(m, 3 * m + 6); per = '0' if fam != '?k01' else '01'
    x = ''.join(per[i % len(per)] if random.random() < 0.9 else str(random.randrange(2)) for i in range(n))
    o, ll = longest_run(P); w = max(1, ll // 4)
    for b in range(0, n - m + 1, w):
        got, e = decide(x, P, b)
        assert got == any(occurs(x, P, t) for t in range(b, b + w)), (x, P, b)
        blocks += 1; maxexp = max(maxexp, e)
print("families with many admissible starts:", 4000, "blocks:", blocks, "most exposed candidates:", maxexp)
