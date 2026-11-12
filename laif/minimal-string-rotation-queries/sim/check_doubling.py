"""Brute-force check of the doubling algorithm for minimal length-l substrings (and so minimal rotations).

Level L -> L' = min(2L, l): given one start c of a minimal length-L substring u_L among the starts [0, N), N = n - l + 1,
cut the starts into windows of g = max(1, L // 2) starts. In each window take the first and the last start of an
occurrence of u_L (the extremes), and return the extreme with the least (s[e, e + L'), e). Claim: this is the leftmost
start of a minimal length-L' substring. At L' = l it is the answer.
"""
import random

def solve(s, l):
    n = len(s); N = n - l + 1
    key = lambda e, L: (s[e:e + L], e)
    L = 1
    c = min(range(N), key=lambda e: key(e, 1))                  # level 1: minimum finding over letters
    levels = 0
    while L < l:
        Lp = min(2 * L, l); g = max(1, L // 2); u = s[c:c + L]
        best = None
        for a in range(0, N, g):
            occ = [e for e in range(a, min(a + g, N)) if s[e:e + L] == u]
            if not occ:
                continue
            ext = {occ[0], occ[-1]}
            # the exclusion claim: in the window, the least key over all occurrences is at an extreme
            assert min(key(e, Lp) for e in occ) == min(key(e, Lp) for e in ext)
            if len(occ) >= 2:                                    # occurrences form an arithmetic progression
                d = occ[1] - occ[0]
                assert all(occ[j + 1] - occ[j] == d for j in range(len(occ) - 1))
            cand = min(ext, key=lambda e: key(e, Lp))
            if best is None or key(cand, Lp) < key(best, Lp):
                best = cand
        c = best; L = Lp; levels += 1
    return c, levels

def brute(s, l):
    return min(range(len(s) - l + 1), key=lambda e: (s[e:e + l], e))

def word(n, sig):
    r = random.random()
    if r < 0.4:
        p = random.randint(1, max(1, n // 3)); b = [random.randrange(sig) for _ in range(p)]
        w = [b[i % p] for i in range(n)]
        for _ in range(random.choice([0, 1, 1, 2])):
            w[random.randrange(n)] = random.randrange(sig)
    elif r < 0.6:                                               # Lyndon-like and Fibonacci-like words
        a, b = [0], [0, 1]
        while len(b) < n:
            a, b = b, b + a
        w = b[:n]
    else:
        w = [random.randrange(sig) for _ in range(n)]
    return ''.join(chr(97 + c) for c in w)

random.seed(3)
for trial in range(30000):
    n = random.randint(1, 40); sig = random.choice([2, 2, 3, 4]); x = word(n, sig)
    # minimal rotation: minimal length-n substring of xx among starts [0, n)
    c, _ = solve(x + x[:-1] if n > 1 else x, n)
    assert c == brute(x + x[:-1] if n > 1 else x, n), x
    assert (x[c:] + x[:c]) == min(x[i:] + x[:i] for i in range(n))
    l = random.randint(1, n)
    assert solve(x, l)[0] == brute(x, l), (x, l)
print("strings:", 30000, "minimal rotations and minimal length-l substrings agree with brute force")

# exhaustive small strings: all binary strings up to length 12 and all ternary strings up to length 7, every l,
# and the reductions of Corollary 2
import itertools
def minsuf(x):
    return min(range(len(x)), key=lambda i: x[i:])
def maxsuf(x):
    return max(range(len(x)), key=lambda i: (x[i:], -i))
cnt = 0
for sig, top in [(2, 12), (3, 7)]:
    for n in range(1, top + 1):
        for w in itertools.product('abc'[:sig], repeat=n):
            x = ''.join(w)
            for l in range(1, n + 1):
                assert solve(x, l)[0] == brute(x, l), (x, l)
            # minimal suffix: least start of a minimal length-n substring of x + ('0' below the alphabet)^(n-1)
            assert solve(x + '0' * (n - 1), n)[0] == minsuf(x), x
            # maximal suffix: minimal suffix of the reversed-order string followed by a letter above the alphabet
            y = ''.join(chr(ord('a') + ord('c') - ord(c)) for c in x) + 'z'
            assert solve(y + '0' * n, n + 1)[0] == maxsuf(x), x
            cnt += 1
print("exhaustive strings:", cnt, "all l, minimal and maximal suffix agree with brute force")
