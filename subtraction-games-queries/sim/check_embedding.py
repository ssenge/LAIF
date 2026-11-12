"""Embedding of PARITY_k o OR_s into subtraction games.
Positions 0..s-1 form the pool (no moves, so losing). Position s is u_0 (no moves, losing).
Stage t (t = 0..k-1) uses five positions b_t < N_t < A_t < B_t < u_{t+1}:
  b_t moves to pool position i iff x[t][i] = 1, so Win(b_t) = OR_i x[t][i];
  N_t -> {u_t, b_t}, A_t -> {u_t, N_t}, B_t -> {b_t, N_t}, u_{t+1} -> {A_t, B_t}  (fixed moves).
A position wins iff some move reaches a losing position, i.e. Win is the NAND of the reached positions, and the
four NAND gates compute Win(u_{t+1}) = Win(u_t) XOR Win(b_t). With n = s + 5k, the top position u_k is n.
Checks: Win(Gamma) = PARITY of the k ORs, exhaustively for small k, s and on random inputs; every move goes down."""
import itertools, random

def build(x):
    k, s = len(x), len(x[0])
    n = s + 5 * k
    moves = {j: [] for j in range(n + 1)}
    u = s
    for t in range(k):
        b, N, A, B, u1 = u + 1, u + 2, u + 3, u + 4, u + 5
        moves[b] = [i for i in range(s) if x[t][i]]
        moves[N] = [u, b]; moves[A] = [u, N]; moves[B] = [b, N]; moves[u1] = [A, B]
        u = u1
    assert u == n
    return n, moves

def win(n, moves):
    w = []
    for j in range(n + 1):
        assert all(i < j for i in moves[j])                # a move removes at least one stone
        w.append(any(not w[i] for i in moves[j]))
    return w

def target(x):
    return sum(any(r) for r in x) % 2 == 1

if __name__ == "__main__":
    cnt = 0
    for k in range(1, 4):
        for s in range(1, 4):
            for bits in itertools.product([0, 1], repeat=k * s):
                x = [list(bits[t * s:(t + 1) * s]) for t in range(k)]
                n, mv = build(x)
                assert win(n, mv)[n] == target(x); cnt += 1
    rng = random.Random(1)
    for _ in range(3000):
        k, s = rng.randint(1, 30), rng.randint(1, 30)
        p = rng.choice([0.02, 0.1, 0.5])
        x = [[int(rng.random() < p) for _ in range(s)] for _ in range(k)]
        n, mv = build(x)
        assert win(n, mv)[n] == target(x); cnt += 1
    print("cases", cnt, "all checks passed")
