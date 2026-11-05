"""Counts and exponents for amplitude amplification over the partitions of the sieves. See the README.

Run: python check_sieve.py

Tests, by assertion:
1. The count of partitions behind the success probability for Hamiltonicity, by enumeration.
2. The count behind the success probability for k-path, by enumeration.
3. The optimized bases reproduce the published classical constants, and give the Grover constants. An unbalanced
   partition does not help for Hamiltonicity or k-path.

Limits: test 3 uses the entropy forms of the probabilities.
"""
import itertools
import math

for n in range(4, 19, 2):
    for m in range(0, n // 2):
        cnt = 0
        for V2 in itertools.combinations(range(n), n // 2):
            v2 = [0] * n
            for v in V2:
                v2[v] = 1
            if v2[0] == 0 and v2[n - 1] == 1 and sum(v2[i] == 0 and v2[(i + 1) % n] == 0 for i in range(n)) == m:
                cnt += 1
        assert cnt == math.comb(n // 2 - 1, n // 2 - m - 1) ** 2, (n, m, cnt)

for k in range(3, 15):
    counts = {}
    for bits in itertools.product((1, 2), repeat=k):
        key = (bits.count(1), sum(a == b == 2 for a, b in zip(bits, bits[1:])))
        counts[key] = counts.get(key, 0) + 1
    for (k1, l2), c in counts.items():
        assert c == math.comb(k1 + 1, k - k1 - l2) * (math.comb(k - k1 - 1, l2) if k > k1 else 1), (k, k1, l2, c)


def H(p):
    return 0 if p <= 0 or p >= 1 else -p * math.log2(p) - (1 - p) * math.log2(1 - p)


def ham(a, s, w):
    """Fraction a of vertices in V2, s runs per vertex, Grover weight w."""
    return 1 - s + w * (H(a) - a * H(s / a) - (1 - a) * H(s / (1 - a)))


def pack(q, b1, b2, w):
    t = b1 + b2
    labels = q * (1 - t) + (q - 1) * b1 + (q - 2) * b2
    logp = H(t) + t * H(b2 / t) + b1 * math.log2(q) + b2 * math.log2(q * (q - 1) / 2) - q * H((b1 + 2 * b2) / q)
    return labels - w * logp


def minimize(q, w):
    grid = [(i / 400, j / 400) for i in range(1, 400) for j in range(1, 400 - i)]
    best = min(grid, key=lambda b: pack(q, *b, w))
    for step in (1e-3, 2e-4, 4e-5):
        near = ((best[0] + a * step, best[1] + c * step) for a in range(-8, 9) for c in range(-8, 9))
        best = min((b for b in near if b[0] > 0 and b[1] > 0 and b[0] + b[1] < 1), key=lambda b: pack(q, *b, w))
    return 2 ** pack(q, *best, w), best


def best_ham(a, w):
    return 2 ** min(ham(a, i / 20000, w) for i in range(1, int(20000 * min(a, 1 - a))))


classical, quantum = best_ham(0.5, 1), best_ham(0.5, 0.5)
assert abs(classical - 4 * (math.sqrt(2) - 1)) < 1e-5 and abs(quantum - math.sqrt(8 / 3)) < 1e-5
for a in (0.3, 0.4, 0.45, 0.48):
    assert best_ham(a, 0.5) > quantum and best_ham(a, 1) > classical
for q, c, g in ((3, 3.3432, 2.8039), (4, 7.2562, 5.9753), (5, 15.072, 12.3154), (6, 30.8179, 25.0732)):
    assert abs(minimize(q, 1)[0] - c) < 2e-3 and abs(minimize(q, 0.5)[0] - g) < 2e-3, q
print(f"ok: Hamiltonicity and k-path {classical:.5f} -> {quantum:.5f}")
for q in (3, 4, 5, 6):
    g, b = minimize(q, 0.5)
    print(f"q = {q}: packing {minimize(q, 1)[0]:.4f} -> {g:.4f} at beta1 = {b[0]:.4f}, beta2 = {b[1]:.4f}")
