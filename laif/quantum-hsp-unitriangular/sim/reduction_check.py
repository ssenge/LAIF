"""Brute-force check of the group-theoretic steps behind the O~(sqrt p) algorithm for the HSP over U_4(F_p).

Elements of U_4(F_p) are tuples g = (b1, z, c2, b2, c1, a) for the matrix
  [[1, b1, b2, a], [0, 1, z, c1], [0, 0, 1, c2], [0, 0, 0, 1]].
K = {b1 = c2 = 0} (abelian normal, order p^4); for a direction delta = (u, w) != 0 in D = F_p^2,
F_delta = {g : (b1, c2) in F_p * delta} = K x| <delta> (order p^5); sigma_r = conjugation by diag(1, 1, 1, r).
Asserts, for p in {5, 7}:
 1. the group law (matrix product) and that every non-identity element has order p;
 2. K is abelian and normal, F_delta is a subgroup of order p^5 with K normal and F_delta / K cyclic;
 3. sigma_r is an automorphism mapping F_(1, r) onto F_(1, 1) (r != 0);
 4. for every element h with z, b1, c2 all nonzero (the hard cyclic case) and every r in F_p^*:
    <h> <= F_(1, r) iff r = c2 / b1, and otherwise <h> meets F_(1, r) trivially;
 5. for the two-generator case H = <h0, h1> (h1 in U_4', commuting, h0 with b1, c2 nonzero), sampled:
    H <= F_(1, r) iff r = c2(h0) / b1(h0), otherwise H meets F_(1, r) in <h1> (known), so a run on the wrong
    direction never returns an element outside the known part."""
import itertools, random

def mul(g, h, p):
    b1, z, c2, b2, c1, a = g; B1, Z, C2, B2, C1, A = h
    return ((b1 + B1) % p, (z + Z) % p, (c2 + C2) % p, (b2 + B2 + b1 * Z) % p, (c1 + C1 + z * C2) % p,
            (a + A + b1 * C1 + b2 * C2) % p)

def mat(g, p):
    b1, z, c2, b2, c1, a = g
    return [[1, b1, b2, a], [0, 1, z, c1], [0, 0, 1, c2], [0, 0, 0, 1]]

def matmul(X, Y, p):
    return [[sum(X[i][k] * Y[k][j] for k in range(4)) % p for j in range(4)] for i in range(4)]

def from_mat(X):
    return (X[0][1], X[1][2], X[2][3], X[0][2], X[1][3], X[0][3])

E = (0, 0, 0, 0, 0, 0)

def power(g, k, p):
    out = E
    for _ in range(k): out = mul(out, g, p)
    return out

def gen(gens, p):
    S = {E}; frontier = [E]
    while frontier:
        x = frontier.pop()
        for g in gens:
            y = mul(x, g, p)
            if y not in S: S.add(y); frontier.append(y)
    return S

def inv(g, p):
    return power(g, p - 1, p)

def sigma(g, r, p):                                   # D g D^{-1}, D = diag(1, 1, 1, r)
    b1, z, c2, b2, c1, a = g; ri = pow(r, p - 2, p)
    return (b1, z, c2 * ri % p, b2, c1 * ri % p, a * ri % p)

def in_F(g, delta, p):
    u, w = delta; b1, c2 = g[0], g[2]
    return (b1 * w - c2 * u) % p == 0

def check(p, rng):
    G = list(itertools.product(range(p), repeat=6))
    for _ in range(300):                               # 1. group law = matrix product, exponent p
        g, h = rng.choice(G), rng.choice(G)
        assert from_mat(matmul(mat(g, p), mat(h, p), p)) == mul(g, h, p)
        assert power(g, p, p) == E
    K = [g for g in G if g[0] == 0 and g[2] == 0]
    for _ in range(300):                               # 2. K abelian, normal
        k, k2, g = rng.choice(K), rng.choice(K), rng.choice(G)
        assert mul(k, k2, p) == mul(k2, k, p)
        c = mul(mul(g, k, p), inv(g, p), p); assert c[0] == 0 and c[2] == 0
    for r in range(1, p):                              # 2./3. F_(1,r) subgroup of order p^5; sigma_r maps it to F_(1,1)
        F = [g for g in G if in_F(g, (1, r), p)]
        assert len(F) == p ** 5
        for _ in range(100):
            x, y = rng.choice(F), rng.choice(F)
            assert in_F(mul(x, y, p), (1, r), p)
            assert sigma(mul(x, y, p), r, p) == mul(sigma(x, r, p), sigma(y, r, p), p)
            assert in_F(sigma(x, r, p), (1, 1), p)
    hard = [h for h in G if h[0] and h[1] and h[2]]   # 4. hard cyclic case, every such h
    for h in hard:
        H = gen([h], p); assert len(H) == p
        rt = h[2] * pow(h[0], p - 2, p) % p
        for r in range(1, p):
            inside = all(in_F(x, (1, r), p) for x in H)
            meet = [x for x in H if in_F(x, (1, r), p)]
            assert inside == (r == rt)
            if r != rt: assert meet == [E]
    U4p = [g for g in G if g[0] == 0 and g[1] == 0 and g[2] == 0]    # commutator subgroup U_4'
    tried = 0
    while tried < 200:                                 # 5. two-generator case
        h0, h1 = rng.choice(G), rng.choice(U4p)
        if not (h0[0] and h0[2] and h1 != E) or mul(h0, h1, p) != mul(h1, h0, p): continue
        tried += 1
        H = gen([h0, h1], p); H1 = gen([h1], p)
        rt = h0[2] * pow(h0[0], p - 2, p) % p
        for r in range(1, p):
            meet = {x for x in H if in_F(x, (1, r), p)}
            if r == rt: assert meet == H
            else: assert meet == H1
    return len(hard)

if __name__ == "__main__":
    rng = random.Random(3)
    for p in (5, 7):
        n = check(p, rng)
        print(f"p = {p}: group law, K, F_(1,r), sigma_r ok; {n} hard cyclic generators and 200 two-generator cases ok")
    print("ok: the hidden subgroup lies in exactly one F_(1,r), and meets every other one only in its known part")
