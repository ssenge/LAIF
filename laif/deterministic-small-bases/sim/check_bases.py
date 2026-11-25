"""Brute-force checks for small n.

(1) Lemma 1 / Theorem 1: for every odd composite n < 20000 the strong liars (units passing for
    n - 1 = 2^s m) lie in a proper subgroup; we check the stronger consequence that some base
    a <= 2 (ln n)^2 is a witness, and record the largest least witness.
(2) Theorem 2: for odd N < 3000 with two coprime factors above 2, given L = lambda(N), some base
    a <= 2 (ln N)^2 yields gcd(a, N) > 1 or a square root y of 1 with y != +-1, and gcd(y - 1, N)
    is a proper divisor.
(3) Corollary 3: for primes 3 <= p < 20000 and every prime r | p - 1, the least r-th power
    nonresidue is <= 2 (ln p)^2.
"""
import math
from sympy import isprime, factorint
from sympy.functions.combinatorial.numbers import reduced_totient


def split2(L):
    s = 0
    while L % 2 == 0:
        L //= 2; s += 1
    return s, L


def passes(a, n, s, m):
    x = pow(a, m, n)
    if x == 1: return True
    for _ in range(s):
        if x == n - 1: return True
        x = x * x % n
    return False


worst = (0, 0)
for n in range(9, 20000, 2):
    if isprime(n): continue
    s, m = split2(n - 1)
    w = next(a for a in range(1, n) if not passes(a, n, s, m))
    assert w <= 2 * math.log(n) ** 2, (n, w)
    worst = max(worst, (w, n))
print(f"(1) least strong witness <= 2 ln^2 n for odd composite n < 20000; largest {worst[0]} at n = {worst[1]}")

cnt = 0
for N in range(15, 3000, 2):
    f = factorint(N)
    if len(f) < 2: continue
    p = min(f); n1 = p ** f[p]; n2 = N // n1
    if n1 <= 2 or n2 <= 2: continue
    s, m = split2(int(reduced_totient(N)))
    found = False
    for a in range(1, int(2 * math.log(N) ** 2) + 1):
        if math.gcd(a, N) > 1:
            found = True; break
        x = pow(a, m, N)
        if x == 1: continue
        for _ in range(s):
            y, x = x, x * x % N
            if x == 1:
                if y != N - 1:
                    g = math.gcd(y - 1, N)
                    assert 1 < g < N
                    found = True
                break
        if found: break
    assert found, N
    cnt += 1
print(f"(2) a splitting base <= 2 ln^2 N found for all {cnt} odd N < 3000 with two coprime factors > 2")

worst = (0, 0, 0)
for p in range(3, 20000):
    if not isprime(p): continue
    for r in factorint(p - 1):
        e = (p - 1) // r
        a = next(a for a in range(2, p) if pow(a, e, p) != 1)
        assert a <= 2 * math.log(p) ** 2, (p, r, a)
        worst = max(worst, (a, p, r))
print(f"(3) least r-th power nonresidue <= 2 ln^2 p for primes p < 20000, prime r | p - 1; largest {worst[0]} at p = {worst[1]}, r = {worst[2]}")
