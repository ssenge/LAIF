"""Exponential congruences a f^x + b g^y = c over F_p: the randomized classical search.

For s = ord(f) >= t = ord(g): draw y uniformly in [0, t), set w = (c - b g^y)/a and test w^s = 1
(w in <f>). Each draw costs O(log p) multiplications, and it succeeds with probability exactly N/t,
N the number of solutions (x, y) in [0, s) x [0, t) (for each y at most one x). Lemma 1 of
arXiv:0804.1109 gives N = st/(p - 1) + O(p^{1/2} log p), so in the regime
st > C p^{3/2} log p the expected number of draws is about (p - 1)/s = (p - 1)/max(s, t).
Checks, by exhaustive computation on prime fields:
1. N equals the number of y with (c - b g^y)/a in <f>, i.e. the success probability is N/t.
2. |N - st/(p - 1)| stays below p^{1/2} log p (the error term of Lemma 1, constant 1 here).
3. The sampler finds a solution whenever one exists, and its mean number of draws is close to t/N.
Run: python sampling.py
"""
import math, random

random.seed(5)


def order(x, p):
    n = p - 1
    for d in sorted(d for d in range(1, n + 1) if n % d == 0):
        if pow(x, d, p) == 1:
            return d


def elem_of_order(s, p):
    while True:
        r = random.randrange(2, p)
        h = pow(r, (p - 1) // s, p)
        if order(h, p) == s:
            return h


checked = 0
for p in (101, 211, 401, 601, 1009, 2003, 4001):
    divs = [d for d in range(2, p) if (p - 1) % d == 0]
    for s in divs:
        for t in divs:
            if t > s or s * t < p:          # s >= t, and skip tiny orders
                continue
            f, g = elem_of_order(s, p), elem_of_order(t, p)
            a, b, c = (random.randrange(1, p) for _ in range(3))
            H1 = {pow(f, x, p) for x in range(s)}
            ainv = pow(a, p - 2, p)
            sol = [y for y in range(t) if (c - b * pow(g, y, p)) * ainv % p in H1]
            N = sum(1 for x in range(s) for y in range(t) if (a * pow(f, x, p) + b * pow(g, y, p)) % p == c)
            assert N == len(sol)                                            # check 1
            assert abs(N - s * t / (p - 1)) <= math.sqrt(p) * math.log(p)  # check 2
            if N:
                draws = []
                for _ in range(200):
                    k = 0
                    while True:
                        k += 1
                        y = random.randrange(t)
                        w = (c - b * pow(g, y, p)) * ainv % p
                        if pow(w, s, p) == 1:
                            break
                    draws.append(k)
                    assert y in sol                                         # check 3: a real solution
                mean = sum(draws) / len(draws)
                assert 0.6 * t / N <= mean <= 1.6 * t / N, (p, s, t, N, mean)
            checked += 1
print(f"sampler checked on {checked} (p, s, t) instances")
print("all checks passed")
