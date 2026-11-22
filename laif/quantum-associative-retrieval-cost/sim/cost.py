"""Cost of the retrieval algorithm of [1] (arXiv:2611.21941), evaluated from its own formulas, against classical baselines.

[1]: after b rounds of distance-dependent rotations the "good" subspace has probability
  P_good = (1/p) sum_k cos^{2b}(pi d_k / (2n))                                    [1, eqs. (13), (14), (18)]
and amplitude amplification needs 1/sqrt(P_good) repetitions of an O(b)-step oracle on n qubits [1, eqs. (14), (17)].
Given the good outcome, pattern k is returned with probability cos^{2b}(pi d_k/(2n)) / sum_j cos^{2b}(pi d_j/(2n)).

Asserts:
 1. Lemma: if the query equals one pattern and that pattern is returned with probability >= 1 - eta, then
    1/sqrt(P_good) >= sqrt((1 - eta) p), so the sequential cost n b / sqrt(P_good) >= n b sqrt((1 - eta) p).
 2. For p = n^k random patterns (bits i.i.d. uniform), the least b meeting the precision 1 - eta (expected distractor
    mass, exact binomial sum) and the resulting cost; the gain over brute force p n is at most sqrt(p / (1 - eta)) / b.
 3. Total gate count: each repetition contains a reflection about the memory state, whose preparation costs O(n p) gates
    in the circuit model [1]; so the total is at least sqrt((1 - eta) p) * n p, above brute force p n.
 4. A static classical circuit (parallel distance counts, then a minimum tree) returns the exact nearest pattern for
    every query, in depth ceil(log2(n + 1)) + ceil(log2 p) * ceil(log2(n + 1)) comparator levels; checked on random instances.
"""
import math, random
import numpy as np

random.seed(3); np.random.seed(3)
ETA = 0.1


def pgood_and_success(dists, b, n):
    w = np.cos(np.pi * np.asarray(dists) / (2 * n)) ** (2 * b)
    return w.mean(), w[0] / w.sum()           # dists[0] = 0 is the target


# 1. lemma on random instances
for _ in range(2000):
    n = random.randint(4, 40); p = random.randint(2, 300); b = random.randint(1, 60)
    d = [0] + [random.randint(1, n) for _ in range(p - 1)]
    pg, succ = pgood_and_success(d, b, n)
    assert 1 / math.sqrt(pg) >= math.sqrt(succ * p) - 1e-9          # P_good * p = 1 / succ exactly
    assert abs(pg * p * succ - 1) < 1e-9

# 2. typical case p = n^k
print(" n   k        p     b   1/sqrt(Pgood)   quantum n b/sqrt(Pgood)   brute force p n   gain   sqrt(p)   classical depth")
for k in [1, 2, 3]:
    for n in [16, 64, 256, 1024]:
        p = n ** k
        Ecos = lambda b: sum(math.comb(n, j) * 2.0 ** -n * math.cos(math.pi * j / (2 * n)) ** (2 * b) for j in range(n + 1))
        b = 1
        while (p - 1) * Ecos(b) > ETA / (1 - ETA):                    # expected distractor mass <= eta/(1-eta)
            b += 1
        pg = (1 + (p - 1) * Ecos(b)) / p
        reps = 1 / math.sqrt(pg)
        q = n * b * reps
        brute = p * n
        depth = math.ceil(math.log2(n + 1)) * (1 + math.ceil(math.log2(p)))
        assert reps >= math.sqrt((1 - ETA) * p) - 1e-9
        assert brute / q <= math.sqrt(p / (1 - ETA)) / b + 1e-9
        assert reps * n * p >= brute                                   # 3. total gates with O(np) preparation per reflection
        assert depth < q
        print(f"{n:4d} {k:2d} {p:12d} {b:4d} {reps:14.1f} {q:24.3e} {brute:17.3e} {brute / q:7.1f} {math.sqrt(p):9.1f} {depth:8d}")

# 4. static classical circuit: parallel distances, then a pairwise minimum tree
def classical_circuit(P, x):
    dist = (P != x).sum(1)                                            # one counter per pattern, all in parallel
    idx = list(range(len(P)))
    while len(idx) > 1:                                               # one tree level per loop
        idx = [i if j is None or dist[i] <= dist[j] else j for i, j in zip(idx[0::2], idx[1::2] + [None] * (len(idx) % 2))]
    return idx[0]


for _ in range(300):
    n = random.randint(3, 30); p = random.randint(1, 200)
    P = np.random.randint(0, 2, (p, n)); x = np.random.randint(0, 2, n)
    i = classical_circuit(P, x)
    assert (P[i] != x).sum() == (P != x).sum(1).min()
print("all checks passed")
