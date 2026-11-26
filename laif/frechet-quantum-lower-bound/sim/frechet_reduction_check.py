"""Reduction check: a depth-2 circuit C (CNF or DNF) on n variables, split x = (a, b) with a, b in {0,1}^{n/2}, gives two
sequences of 0/1 vectors P = (p_a), Q = (q_b) (a, b in lexicographic order) and a threshold delta such that
  hamming(p_a, q_b) <= delta  iff  C(a, b) = 1,
so the discrete Frechet distance of P and Q (Hamming metric; squared Euclidean is the same on 0/1 vectors) is <= delta iff the
truth-table matrix M(a, b) = C(a, b) has a monotone path (steps right, up, diagonal) from cell (first, first) to cell (last, last).
Asserts the pointwise identity and the Frechet / reachability equivalence on random CNFs and DNFs."""
import itertools, random

def lit_ok(assign, lits):                      # lits: list of (var index in this half, wanted value)
    return all(assign[v] == val for v, val in lits)

def clause_false(assign, lits):                # a disjunction restricted to one half is false iff every literal is false
    return all(assign[v] != val for v, val in lits)

def pad(vec, w, side, total_pad):              # append padding block: side 0 uses the first block, side 1 the second
    extra = w - sum(vec); assert 0 <= extra <= total_pad
    blk = [1] * extra + [0] * (total_pad - extra)
    return vec + (blk + [0] * total_pad if side == 0 else [0] * total_pad + blk)

def build(circuit, h):
    kind, items = circuit                      # items: list of (lits on a-half, lits on b-half)
    A = list(itertools.product((0, 1), repeat=h)); B = A
    if kind == "dnf":                          # alpha_t(a) = a satisfies the a-part of term t
        U = [[int(lit_ok(a, t[0])) for t in items] for a in A]
        V = [[int(lit_ok(b, t[1])) for t in items] for b in B]
    else:                                      # u_c(a) = a falsifies the a-part of clause c
        U = [[int(clause_false(a, c[0])) for c in items] for a in A]
        V = [[int(clause_false(b, c[1])) for c in items] for b in B]
    m = len(items); w = m
    P = [pad(u, w, 0, m) for u in U]; Q = [pad(v, w, 1, m) for v in V]
    d = len(P[0])
    if kind == "dnf":
        delta = 2 * w - 2                      # hamming = 2w - 2<u, v>
    else:
        Q = [[1 - x for x in q] for q in Q]    # complement: hamming = d - 2w + 2<u, v>
        delta = d - 2 * w
    return A, B, P, Q, delta

def evaluate(circuit, a, b):
    kind, items = circuit
    if kind == "dnf":
        return int(any(lit_ok(a, t[0]) and lit_ok(b, t[1]) for t in items))
    return int(all(not (clause_false(a, c[0]) and clause_false(b, c[1])) for c in items))

def reach(M):
    K, L = len(M), len(M[0]); R = [[False] * L for _ in range(K)]
    for i in range(K):
        for j in range(L):
            if not M[i][j]: continue
            R[i][j] = (i == 0 and j == 0) or (i > 0 and R[i - 1][j]) or (j > 0 and R[i][j - 1]) or (i > 0 and j > 0 and R[i - 1][j - 1])
    return R[K - 1][L - 1]

def frechet_le(P, Q, delta):                   # Eiter-Mannila decision DP, Hamming metric
    ham = lambda x, y: sum(u != v for u, v in zip(x, y))
    return reach([[int(ham(p, q) <= delta) for q in Q] for p in P])

def rand_circuit(rng, h):
    kind = rng.choice(("cnf", "dnf")); m = rng.randint(1, 6); items = []
    for _ in range(m):
        side = lambda: [(v, rng.randint(0, 1)) for v in rng.sample(range(h), rng.randint(0, min(2, h)))]
        items.append((side(), side()))
    return kind, items

if __name__ == "__main__":
    rng = random.Random(7); counts = {True: 0, False: 0}
    for _ in range(4000):
        h = rng.randint(1, 4); C = rand_circuit(rng, h)
        A, B, P, Q, delta = build(C, h)
        ham = lambda x, y: sum(u != v for u, v in zip(x, y))
        M = [[evaluate(C, a, b) for b in B] for a in A]
        for i, a in enumerate(A):
            for j, b in enumerate(B):
                assert (ham(P[i], Q[j]) <= delta) == bool(M[i][j]), (C, a, b)
        r = reach(M); assert frechet_le(P, Q, delta) == r; counts[r] += 1
    print(f"ok: 4000 random CNF/DNF instances, pointwise identity and Frechet <= delta iff reachability; yes {counts[True]}, no {counts[False]}")
