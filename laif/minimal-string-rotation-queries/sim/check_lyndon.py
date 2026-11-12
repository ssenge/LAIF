"""Check of Theorem 3: the longest Lyndon substring with the doubling algorithm of Theorem 1 (`solve`) as the only
subroutine for minimal suffixes.

For a scale d and a window u = s[j, j + W), W = d + 2 ceil(eps d), the start i of the candidate is the least suffix of u
among the starts [0, ceil(eps d)], and its length is NSS(i) - i, where NSS(i) is the least j > i whose suffix of u is
smaller than u[i:], found by binary search with one minimal-suffix call per step. The script asserts that every
candidate is a Lyndon word, that NSS(i) - i is the longest Lyndon prefix of s[i:] for every i, and that the result
equals brute force.
"""
import math, random

LOW = '\x00'                                                  # a letter below the alphabet

def solve(s, l):
    """Doubling algorithm of Theorem 1: least start of a minimal length-l substring."""
    n = len(s); N = n - l + 1
    key = lambda e, L: (s[e:e + L], e)
    L = 1; c = min(range(N), key=lambda e: key(e, 1))
    while L < l:
        Lp = min(2 * L, l); g = max(1, L // 2); u = s[c:c + L]; best = None
        for a in range(0, N, g):
            occ = [e for e in range(a, min(a + g, N)) if s[e:e + L] == u]
            if occ:
                cand = min({occ[0], occ[-1]}, key=lambda e: key(e, Lp))
                if best is None or key(cand, Lp) < key(best, Lp):
                    best = cand
        c, L = best, Lp
    return c

def min_suffix_among(w, r):
    """Least suffix of w among the starts [0, r], via a minimal length-|w| substring of w + LOW^r."""
    return solve(w + LOW * r, len(w)) if r > 0 else 0

def lyndon_prefix_len(u, i):
    """Length of the longest Lyndon prefix of u[i:]: NSS(i) - i, with NSS(i) the least j > i whose suffix is smaller
    than u[i:] (|u| if none). NSS is found by binary search on t; the test asks whether the least suffix among the
    starts (i, t] is smaller than u[i:], with one call of `min_suffix_among` and one comparison."""
    n = len(u)
    def smaller_up_to(t):
        c = i + 1 + min_suffix_among(u[i + 1:], t - i - 1)
        return u[c:] < u[i:]
    if i + 1 >= n or not smaller_up_to(n - 1):
        return n - i
    lo, hi = i + 1, n - 1
    while lo < hi:
        mid = (lo + hi) // 2
        if smaller_up_to(mid):
            hi = mid
        else:
            lo = mid + 1
    return lo - i

def is_lyndon(w):
    return min_suffix_among(w, len(w) - 1) == 0 and all(w < w[i:] for i in range(1, len(w)))

def lyndon_in_window(s, j, W, e0):
    win = s[j:j + W]
    i = min_suffix_among(win, min(e0, len(win) - 1))       # start of the longest Lyndon factor [1, Lemma 4.13]
    L = lyndon_prefix_len(win, i)
    assert is_lyndon(win[i:i + L])
    return L, j + i

def longest_lyndon(s, eps=0.1):
    n = len(s); best = (1, -min(range(n), key=lambda i: s[i]))
    d = 1.0
    while d <= n:
        di = max(1, int(d)); e0 = math.ceil(eps * di); W = di + 2 * e0; step = max(1, e0)
        for j in range(0, max(1, n - di + 1), step):
            L, st = lyndon_in_window(s, j, W, e0)
            best = max(best, (L, -st))
        d *= 1 + eps
    return best[0]

def lyn(w):
    return all(w < w[i:] + w[:i] for i in range(1, len(w)))

def brute(s):
    return max(r - l for l in range(len(s)) for r in range(l + 1, len(s) + 1) if lyn(s[l:r]))

random.seed(9)
for trial in range(3000):
    n = random.randint(1, 30); sig = random.choice([2, 2, 3])
    if random.random() < 0.4:
        p = random.randint(1, 6); b = [random.choice('abc'[:sig]) for _ in range(p)]
        s = ''.join(b[i % p] if random.random() < 0.9 else random.choice('abc'[:sig]) for i in range(n))
    else:
        s = ''.join(random.choice('abc'[:sig]) for _ in range(n))
    assert longest_lyndon(s) == brute(s), (s, longest_lyndon(s), brute(s))
    for i in range(len(s)):
        lp = max(L for L in range(1, len(s) - i + 1) if lyn(s[i:i + L]))
        assert lyndon_prefix_len(s, i) == lp, (s, i)
print("strings:", 3000, "longest Lyndon substring agrees with brute force")

import itertools
count = 0
for n, sig in [(k, 'ab') for k in range(1, 12)] + [(k, 'abc') for k in range(1, 8)]:
    for t in itertools.product(sig, repeat=n):
        s = ''.join(t)
        assert longest_lyndon(s) == brute(s), s
        count += 1
print("exhaustive:", count, "binary strings up to length 11 and ternary up to length 7 agree")

# w = x x' with x = ababb Lyndon and x' = aba: w is a prefix of a Lyndon word, but its minimal rotation is not x' x
w = 'ababbaba'
assert lyn('ababb') and lyn(w + 'c') and min(w[r:] + w[:r] for r in range(len(w))) == 'aababbab' != 'aba' + 'ababb'
print("prefix of a Lyndon word whose minimal rotation is not x' x:", w)
