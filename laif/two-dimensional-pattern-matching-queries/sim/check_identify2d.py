"""Brute-force check of the block decision of Theorem 5 (window identification under condition (★)).

Block of starts B + F, F = [0, b1) x [0, b2), B a multiple of (b1, b2). Every start B + s covers B + C with
C = [b1 - 1, m1) x [b2 - 1, m2), where it needs the window W_s = (P[z - s])_{z in C}. Under (★) the windows are
pairwise distinct, so the text on B + C determines at most one candidate start, which is then verified.
"""
import random

def window(P, s, m1, m2, b1, b2):
    return tuple(P[i - s[0]][j - s[1]] for i in range(b1 - 1, m1) for j in range(b2 - 1, m2))

def star(P, m1, m2, b1, b2):
    W = [window(P, (a, c), m1, m2, b1, b2) for a in range(b1) for c in range(b2)]
    return len(set(W)) == len(W)

def occurs(T, P, x, m1, m2):
    return all(T[x[0] + i][x[1] + j] == P[i][j] for i in range(m1) for j in range(m2))

def decide(T, P, B, n1, n2, m1, m2, b1, b2):
    M = tuple(T[B[0] + i][B[1] + j] for i in range(b1 - 1, m1) for j in range(b2 - 1, m2))
    hits = [(a, c) for a in range(b1) for c in range(b2) if window(P, (a, c), m1, m2, b1, b2) == M]
    assert len(hits) <= 1                                   # identification is unique under (★)
    for a, c in hits:
        x = (B[0] + a, B[1] + c)
        if x[0] <= n1 - m1 and x[1] <= n2 - m2:
            return occurs(T, P, x, m1, m2)
    return False

random.seed(5)
blocks = tested = found = big = 0
while tested < 10000:
    m1, m2 = random.randint(1, 10), random.randint(1, 10); sig = random.choice([2, 3, 4])
    P = [[random.randrange(sig) for _ in range(m2)] for _ in range(m1)]
    ok = [(b1, b2) for b1 in range(1, (m1 + 1) // 2 + 1) for b2 in range(1, (m2 + 1) // 2 + 1) if star(P, m1, m2, b1, b2)]
    if random.random() < 0.7:                                # the largest b with (★) ...
        b1, b2 = max(ok, key=lambda t: (t[0] * t[1], t))
    else:                                                    # ... or any b with (★)
        b1, b2 = random.choice(ok)
    big += b1 * b2 >= 4
    tested += 1
    n1, n2 = random.randint(m1, 3 * m1 + 4), random.randint(m2, 3 * m2 + 4)
    T = [[random.randrange(sig) for _ in range(n2)] for _ in range(n1)]
    for _ in range(random.randint(0, 3)):                    # plant copies, some with one changed cell
        r, c = random.randint(0, n1 - m1), random.randint(0, n2 - m2)
        for i in range(m1):
            for j in range(m2):
                T[r + i][c + j] = P[i][j]
        if random.random() < 0.4:
            i, j = random.randrange(m1), random.randrange(m2); T[r + i][c + j] = (P[i][j] + 1) % sig
    for B0 in range(0, n1 - m1 + 1, b1):
        for B1 in range(0, n2 - m2 + 1, b2):
            got = decide(T, P, (B0, B1), n1, n2, m1, m2, b1, b2)
            want = any(occurs(T, P, (B0 + a, B1 + c), m1, m2) for a in range(b1) for c in range(b2)
                       if B0 + a <= n1 - m1 and B1 + c <= n2 - m2)
            assert got == want
            blocks += 1; found += want
print("patterns with (★):", tested, "with b1 * b2 >= 4:", big, "blocks:", blocks, "blocks with an occurrence:", found)
