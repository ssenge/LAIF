"""Checks of the dual (filtered gamma_2) solutions behind the O(sqrt n) bound for LSEG.
(1) OR_M: a_{0,i} = M^(-1/4), a_{z,i} = M^(1/4)/|z| on the ones of z. Constraints sum_{i: z_i != z'_i} a_{z,i} a_{z',i}
    = [OR z != OR z'] for all z, z', costs sqrt M at 0 and sqrt M / |z| otherwise.
(2) Boundary of a monotone string 1^b 0^(m+1-b): a_{z,i} = 1 at i = b and for i < b. Constraint = [b != b'].
(3) Composition with shared inputs: inner g_i = OR of a subset S_i of the input bits with the solution of (1); the
    vectors u_{x,(i,j)} = a_{g(x),i} * u^i_{x,j} satisfy the constraints of the outer function, and
    sum_j |u_{x,j}|^2 = sum_i a_{g(x),i}^2 * sum_j |u^i_{x,j}|^2.
(4) The cost of the scale search: with c_K = sqrt(M_K K) / t_K (t_K marked multiples) if L >= K, and sqrt(M_K K) if
    L < K, M_K = ceil(n/K), the sum c_{2^b} + sum_{i<b} c_{2^i} is at most 5 sqrt(2n)."""
import itertools, math, random

def or_sol(z):
    M, t = len(z), sum(z)
    return [M ** -0.25] * M if t == 0 else [(M ** 0.25 / t) if zi else 0.0 for zi in z]

def check_or(M):
    zs = list(itertools.product([0, 1], repeat=M))
    for z in zs:
        az = or_sol(z)
        c = sum(a * a for a in az)
        t = sum(z)
        assert abs(c - (math.sqrt(M) if t == 0 else math.sqrt(M) / t)) < 1e-9
        for w in zs:
            aw = or_sol(w)
            s = sum(az[i] * aw[i] for i in range(M) if z[i] != w[i])
            assert abs(s - (1 if (max(z) != max(w)) else 0)) < 1e-9, (z, w, s)

def bnd_sol(b, m):
    return [1.0 if i <= b else 0.0 for i in range(m + 1)]          # i = b is the first zero; b = m + 1: all ones

def check_boundary(m):
    for b in range(m + 2):
        for b2 in range(m + 2):
            z = [1 if i < b else 0 for i in range(m + 1)]
            z2 = [1 if i < b2 else 0 for i in range(m + 1)]
            s = sum(bnd_sol(b, m)[i] * bnd_sol(b2, m)[i] for i in range(m + 1) if z[i] != z2[i])
            assert abs(s - (1 if b != b2 else 0)) < 1e-9

def check_composition(n, rng):
    M = rng.randint(1, 4)
    S = [sorted(rng.sample(range(n), rng.randint(1, n))) for _ in range(M)]    # overlapping subsets
    def inner(i, x):                                                           # u^i_{x, j} for j in S_i, else 0
        a = or_sol([x[j] for j in S[i]])
        u = [0.0] * n
        for k, j in enumerate(S[i]): u[j] = a[k]
        return u
    outer = rng.choice(["or", "and_not"])
    def fsol(z):
        return or_sol(z) if outer == "or" else or_sol([1 - v for v in z])     # NOT-OR = AND of the negations
    xs = list(itertools.product([0, 1], repeat=n))
    g = {x: [max(x[j] for j in S[i]) for i in range(M)] for x in xs}
    U = {}
    for x in xs:
        a = fsol(g[x])
        U[x] = [[a[i] * inner(i, x)[j] for i in range(M)] for j in range(n)]
        cost = sum(v * v for row in U[x] for v in row)
        assert abs(cost - sum(a[i] ** 2 * sum(v * v for v in inner(i, x)) for i in range(M))) < 1e-9
    f = (lambda z: max(z)) if outer == "or" else (lambda z: int(all(z)))
    for x in xs:
        for y in xs:
            s = sum(sum(U[x][j][i] * U[y][j][i] for i in range(M)) for j in range(n) if x[j] != y[j])
            assert abs(s - (1 if f(g[x]) != f(g[y]) else 0)) < 1e-9, (S, x, y, s)

def longest(x):
    best = cur = 0
    for v in x:
        cur = cur + 1 if v == 0 else 0
        best = max(best, cur)
    return best

def run_through(x, p, K):
    if x[p]: return 0
    l = p
    while l - 1 >= max(0, p - K + 1) and x[l - 1] == 0: l -= 1
    r = p
    while r + 1 <= min(len(x) - 1, p + K - 1) and x[r + 1] == 0: r += 1
    return r - l + 1

def scale_cost(x):
    n, L = len(x), longest(x)
    m = n.bit_length() - 1
    D = []
    for i in range(m + 1):
        K = 2 ** i
        t = sum(1 for p in range(0, n, K) if run_through(x, p, K) >= K)
        assert (t > 0) == (L >= K)                                  # Lemma 5.1
        if L >= 2 * K: assert t >= L / (2 * K)
        D.append((K, t))
    b = next((i for i, (K, t) in enumerate(D) if t == 0), m + 1)
    c = lambda K, t: math.sqrt(math.ceil(n / K) * K) / (t if t else 1)
    total = sum(c(K, t) for K, t in D[:b]) + (c(*D[b]) if b <= m else 0)
    assert total <= 5 * math.sqrt(2 * n), (x, total)
    return total / math.sqrt(n)

if __name__ == "__main__":
    for M in range(1, 7): check_or(M)
    for m in range(0, 8): check_boundary(m)
    rng = random.Random(3)
    for _ in range(40): check_composition(rng.randint(2, 6), rng)
    worst = 0
    for n in range(1, 15):
        for x in itertools.product([0, 1], repeat=n): worst = max(worst, scale_cost(x))
    for _ in range(3000):
        n = rng.randint(1, 3000); q = rng.choice([0.5, 0.1, 0.01, 0.001])
        x = [1 if rng.random() < q else 0 for _ in range(n)]
        worst = max(worst, scale_cost(x))
    print("all checks passed; largest scale cost / sqrt(n):", round(worst, 3))
