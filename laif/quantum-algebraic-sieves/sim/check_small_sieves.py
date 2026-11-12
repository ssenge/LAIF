"""Small runs of the sieves, with the polynomial-space routes. See the README.

Run: python check_small_sieves.py

Tests, by assertion, all over GF(2^k) at random points:
1. Hamiltonicity: the walk sum of Section 4 of [B] equals the sum over simple paths, and it is nonzero exactly when a
   Hamiltonian cycle with m arcs inside V1 exists, up to field errors.
2. Graphs with a 2-factor of two cycles and no Hamiltonian cycle: the sum vanishes. Without the mirror property it does
   not, so this test sees the cancellation.
3. The marked fraction on the 6-cycle over small fields is at least P/2.
4. TSP: the coefficients in y are the tour weights, and the threshold sum over the evaluations of y equals the direct
   sum and decides whether a tour of weight at most W exists.
5. k-path: the sieve for a fixed start vertex, with and without the palindrome filter, and the cancellation of a path
   with its reversal when one sums over all start vertices.
6. Packing of 3-sets, including negatives that have a prepacking.

Limits: n <= 10, k <= 6, q = 3 for packing, no quantum circuit. Field errors are allowed at a low rate.
"""
import itertools
import random


class GF:
    POLYS = {4: 0x13, 5: 0x25, 8: 0x11D, 16: 0x1100B}

    def __init__(self, k):
        self.k, self.q = k, 1 << k
        self.exp, self.log = [0] * (2 * self.q), [0] * self.q
        x, seen = 1, set()
        for i in range(self.q - 1):
            seen.add(x)
            self.exp[i], self.log[x] = x, i
            x <<= 1
            if x & self.q:
                x ^= self.POLYS[k]
        assert len(seen) == self.q - 1, "not primitive"
        for i in range(self.q - 1, 2 * self.q):
            self.exp[i] = self.exp[i - (self.q - 1)]

    def mul(self, a, b):
        return self.exp[self.log[a] + self.log[b]] if a and b else 0

    def inv(self, a):
        return self.exp[self.q - 1 - self.log[a]]

    def pow(self, a, e):
        if e == 0:
            return 1
        return self.exp[(self.log[a] * e) % (self.q - 1)] if a else 0

    def det(self, M):
        M = [r[:] for r in M]
        n, d = len(M), 1
        mul = self.mul
        for c in range(n):
            p = next((r for r in range(c, n) if M[r][c]), None)
            if p is None:
                return 0
            M[c], M[p] = M[p], M[c]
            d = mul(d, M[c][c])
            iv = self.inv(M[c][c])
            for r in range(c + 1, n):
                if M[r][c]:
                    t = mul(M[r][c], iv)
                    Rr, Rc = M[r], M[c]
                    for k in range(c, n):
                        Rr[k] ^= mul(t, Rc[k])
        return d

    def root(self, deg):
        """Element of order N > deg, N dividing q-1, N odd. Returns (omega, N). Coefficient c_d = sum_i omega^(-i d) f(omega^i) as N is odd."""
        N = next(d for d in range(deg + 1, self.q) if (self.q - 1) % d == 0)
        return self.exp[(self.q - 1) // N], N


# ------- Hamiltonicity
def key_fn(s):
    return lambda u, v, d=None: (u, v, d) if s in (u, v) else (min(u, v), max(u, v), d)


def lemma6_lambda(F, n, E, V1, m, val, s=None):
    """Tabulated simple paths (Lemma 6/7)."""
    adj = lambda a, b: (min(a, b), max(a, b)) in E
    V2 = [v for v in range(n) if v not in V1]
    s = V1[0] if s is None else s
    k = key_fn(s)
    L = V2 + [("d", d) for d in range(m)]
    f = {}
    for u, v in itertools.permutations(V1, 2):
        for size in range(1, len(V2) + 1):
            for X in itertools.combinations(V2, size):
                tot = 0
                for path in itertools.permutations(X):
                    w = (u, *path, v)
                    if all(adj(a, b) for a, b in zip(w, w[1:])):
                        t = 1
                        for a, b in zip(w, w[1:]):
                            t = F.mul(t, val(k(a, b)))
                        tot ^= t
                if tot:
                    f[(u, v, frozenset(X))] = tot
        if adj(u, v):
            for d in range(m):
                f[(u, v, frozenset([("d", d)]))] = val(k(u, v, d))
    idx = {v: i for i, v in enumerate(V1)}
    deg = len(L) * len(V1)
    w, N = F.root(deg)
    total = 0
    for i in range(N):
        r = F.pow(w, i)
        acc = 0
        for sz in range(len(L) + 1):
            for Y in itertools.combinations(L, sz):
                Ys = set(Y)
                M = [[0] * len(V1) for _ in V1]
                for (u, v, Z), va in f.items():
                    if Z <= Ys:
                        M[idx[u]][idx[v]] ^= F.mul(F.pow(r, len(Z)), va)
                acc ^= F.det(M)
        total ^= F.mul(acc, F.pow(w, (N - i * len(L) % N) % N))
    return total


def walk_T(F, n, Eadj, V1, X1, X2, r, val, k, cap, edge_weight=None):
    """Section 4 matrix: sum_l r^l B A^(l-1) B^T, plus the label part. Zero diagonal. Polynomial space."""
    mul = F.mul
    n1 = len(V1)
    w8 = (lambda a, b: 1) if edge_weight is None else edge_weight
    out = [[0] * n1 for _ in V1]
    for iu, u in enumerate(V1):
        # row vector = walk from u after l interior vertices
        vec = {x: mul(val(k(u, x)), w8(u, x)) for x in X1 if (u, x) in Eadj}
        rp = r
        for l in range(1, cap + 1):
            for iv, v in enumerate(V1):
                if iv == iu:
                    continue
                acc = 0
                for x, c in vec.items():
                    if (x, v) in Eadj:
                        acc ^= mul(c, mul(val(k(x, v)), w8(x, v)))
                out[iu][iv] ^= mul(rp, acc)
            new = {}
            for x, c in vec.items():
                if not c:
                    continue
                for z in X1:
                    if (x, z) in Eadj:
                        new[z] = new.get(z, 0) ^ mul(c, mul(val(k(x, z)), w8(x, z)))
            vec = new
            rp = mul(rp, r)
        for iv, v in enumerate(V1):
            if iv != iu and (u, v) in Eadj:
                for d in X2:
                    out[iu][iv] ^= mul(r, mul(val(k(u, v, d)), w8(u, v)))
    return out


def walk_lambda(F, n, E, V1, m, val, s=None, edge_weight=None, y=None):
    Eadj = set(E) | {(b, a) for a, b in E}
    V2 = [v for v in range(n) if v not in V1]
    s = V1[0] if s is None else s
    k = key_fn(s)
    nL = len(V2) + m
    deg = nL * len(V1)
    w, N = F.root(deg)
    total = 0
    for i in range(N):
        r = F.pow(w, i)
        acc = 0
        for mask in range(1 << nL):
            X1 = [V2[b] for b in range(len(V2)) if mask >> b & 1]
            X2 = [b - len(V2) for b in range(len(V2), nL) if mask >> b & 1]
            acc ^= F.det(walk_T(F, n, Eadj, V1, X1, X2, r, val, k, nL, edge_weight))
        total ^= F.mul(acc, F.pow(w, (N - i * nL % N) % N))
    return total


def profiles(n, E, V1):
    Eadj = set(E) | {(b, a) for a, b in E}
    S = set(V1)
    out = {}
    for perm in itertools.permutations(range(1, n)):
        c = (0, *perm)
        if perm[0] < perm[-1] and all((a, b) in Eadj for a, b in zip(c, c[1:] + c[:1])):
            m = sum(a in S and b in S for a, b in zip(c, c[1:] + c[:1]))
            out.setdefault(m, []).append(c)
    return out


def make_val(F, rnd):
    store = {}

    def val(key):
        if key not in store:
            store[key] = rnd.randrange(F.q)
        return store[key]
    return val


def test_ham(rnd):
    F = GF(16)
    stats = {"same": 0, "diff": 0, "pos": 0, "fp": 0, "fn": 0, "tested_nonham": 0, "wrong_m_on_ham": 0}
    for n, dens, tr in ((6, .6, 25), (8, .5, 8)):
        for _ in range(tr):
            E = {(a, b) for a, b in itertools.combinations(range(n), 2) if rnd.random() < dens}
            V1 = sorted(rnd.sample(range(n), n // 2))
            prof = profiles(n, E, V1)
            for m in range(0, 3):
                val = make_val(F, rnd)
                a, b = lemma6_lambda(F, n, E, V1, m, val), walk_lambda(F, n, E, V1, m, val)
                stats["same" if a == b else "diff"] += 1
                if m in prof:
                    stats["pos"] += a != 0
                    stats["fn"] += a == 0
                else:
                    stats["fp"] += a != 0
                    stats["tested_nonham" if not prof else "wrong_m_on_ham"] += 1
    assert stats["diff"] == 0 and stats["fp"] == 0 and stats["fn"] <= 1 and stats["pos"] >= 20, stats
    print("Hamiltonicity:", stats)


def test_two_factors(rnd):
    """Two disjoint cycles: cycle covers exist, Hamiltonian cycles do not. Runs also with no mirror property."""
    global key_fn
    F = GF(16)
    correct = key_fn
    wrong = lambda s: (lambda u, v, d=None: (u, v, d))
    r = {"tests": 0, "fp": 0, "mutant": 0}
    for n, trials in ((8, 30), (10, 6)):
        for _ in range(trials):
            vs = list(range(n))
            rnd.shuffle(vs)
            a = rnd.randint(3, n - 3)
            cycles = vs[:a], vs[a:]
            E = {(min(C[i], C[(i + 1) % len(C)]), max(C[i], C[(i + 1) % len(C)])) for C in cycles for i in range(len(C))}
            while True:
                V1 = sorted(rnd.sample(range(n), n // 2))
                if all(len(set(V1) & set(C)) >= 2 for C in cycles):
                    break
            m = sum(C[i] in V1 and C[(i + 1) % len(C)] in V1 for C in cycles for i in range(len(C)))
            if m > 3:
                continue
            assert m not in profiles(n, E, V1)
            val = make_val(F, rnd)
            r["tests"] += 1
            r["fp"] += walk_lambda(F, n, E, V1, m, val) != 0
            key_fn = wrong
            r["mutant"] += walk_lambda(F, n, E, V1, m, val) != 0
            key_fn = correct
    assert r["fp"] == 0 and r["tests"] >= 10 and r["mutant"] >= r["tests"] // 2, r
    print("two cycles:", r)


def test_fraction(rnd):
    """Unique Hamiltonian cycle C_6: fraction of marked (partition, values) over small field against Lemma 10 / 2."""
    from math import comb
    n = 6
    E = {(min(i, (i + 1) % n), max(i, (i + 1) % n)) for i in range(n)}
    parts = [list(c) for c in itertools.combinations(range(n), n // 2)]
    for kk in (5, 8):
        F = GF(kk)
        for m in (0, 1, 2):
            if F.q - 1 <= (n // 2 + m) * (n // 2):
                continue
            hits = tot = 0
            for _ in range(120):
                V1 = rnd.choice(parts)
                val = make_val(F, rnd)
                tot += 1
                hits += walk_lambda(F, n, E, V1, m, val) != 0
            exact = sum(sum(a in V1 and b in V1 for a, b in zip(range(n), [(i + 1) % n for i in range(n)])) == m for V1 in map(set, parts)) / len(parts)
            lb = comb(n // 2 - 1, n // 2 - m - 1) ** 2 / comb(n, n // 2)
            assert hits / tot >= lb / 2, (kk, m, hits, tot, lb)
            print(f"6-cycle, GF(2^{kk}), m = {m}: marked {hits / tot:.3f}, partitions {exact:.3f}, P/2 = {lb / 2:.3f}")


# ------- TSP + poly-space threshold repair
def test_tsp(rnd):
    F = GF(16)
    n = 6
    res = {"ok": 0, "bad": 0, "geo_ok": 0, "geo_bad": 0, "pos": 0, "decided": 0, "missed": 0}
    for _ in range(4):
        E = {(a, b) for a, b in itertools.combinations(range(n), 2) if rnd.random() < .8}
        ell = {e: rnd.randint(1, 3) for e in E}
        wt = lambda a, b: ell[(min(a, b), max(a, b))]
        V1 = sorted(rnd.sample(range(n), 3))
        prof = profiles(n, E, V1)
        m = 1
        val = make_val(F, rnd)
        wyy, Ny = F.root(19)  # tours have weight <= 18
        T = []
        for l in range(Ny):
            y = F.pow(wyy, l)
            T.append(walk_lambda(F, n, E, V1, m, val, edge_weight=lambda a, b: F.pow(y, wt(a, b))))
        t = [0] * Ny
        for j in range(Ny):
            acc = 0
            for l in range(Ny):
                acc ^= F.mul(T[l], F.pow(wyy, (Ny - j * l % Ny) % Ny))
            t[j] = acc
        truth = {sum(wt(a, b) for a, b in zip(c, c[1:] + c[:1])) for c in prof.get(m, [])}
        got = {j for j, v in enumerate(t) if v}
        if got == truth:
            res["ok"] += 1
        else:
            res["bad"] += 1
        res["pos"] += bool(truth)
        # geometric repair: sum_{j<=W} gamma^j t(j) from the T(l) only, with no table of t
        gamma = rnd.randrange(2, F.q)
        for W in (6, 9, 12, 18):
            direct = 0
            for j in range(W + 1):
                direct ^= F.mul(F.pow(gamma, j), t[j])
            cc = 0
            for l in range(Ny):
                rho = F.mul(gamma, F.pow(wyy, (Ny - l) % Ny))
                if rho == 1:
                    gs = (W + 1) & 1
                else:
                    gs = F.mul(F.pow(rho, W + 1) ^ 1, F.inv(rho ^ 1))
                cc ^= F.mul(T[l], gs)
            res["geo_ok" if cc == direct else "geo_bad"] += 1
            if not [j for j in truth if j <= W]:
                assert cc == 0, (W, truth)
            elif cc:
                res["decided"] += 1
            else:
                res["missed"] += 1
    assert res["bad"] == 0 and res["geo_bad"] == 0 and res["missed"] <= 1, res
    print("TSP:", res)


# ------- k-path
PALINDROME_FILTER = True


def kpath_eval(F, n, E, V1, s, k, k1, l2, x, y, z):
    Eadj = {}
    for a, b in E:
        Eadj.setdefault(a, []).append(b)
        Eadj.setdefault(b, []).append(a)
    S1 = set(V1)
    tot = 0
    mul = F.mul
    for mI in range(1 << k1):
        Yv = {}
        for v in S1:
            a = 0
            for j in range(k1):
                if not mI >> j & 1:
                    a ^= y[(v, j)]
            Yv[v] = a
        for mJ in range(1 << l2):
            Ze = {}
            for (a, b) in E:
                if a not in S1 and b not in S1:
                    c = 0
                    for j in range(l2):
                        if not mJ >> j & 1:
                            c ^= z[((a, b), j)]
                    Ze[(a, b)] = c
            st = {}
            # state: (prev, cur, a, b) -> value
            init = 1 if s not in S1 else Yv[s]
            st[(None, s, 1 if s in S1 else 0, 0)] = init
            for t in range(k - 1):
                new = {}
                for (pv, cur, a, b), v in st.items():
                    for nb in Eadj.get(cur, ()):
                        if PALINDROME_FILTER and pv == nb and cur in S1 and nb not in S1:
                            continue  # forbidden V2 E V1 E V2 palindrome
                        e = (min(cur, nb), max(cur, nb))
                        w = mul(v, x[e])
                        aa, bb = a, b
                        if nb in S1:
                            aa += 1
                            if aa > k1:
                                continue
                            w = mul(w, Yv[nb])
                        if e in Ze:
                            bb += 1
                            if bb > l2:
                                continue
                            w = mul(w, Ze[e])
                        kk = (cur, nb, aa, bb)
                        new[kk] = new.get(kk, 0) ^ w
                st = new
            for (pv, cur, a, b), v in st.items():
                if a == k1 and b == l2:
                    tot ^= v
    return tot


def kpaths(n, E, s, k):
    adj = {i: [] for i in range(n)}
    for a, b in E:
        adj[a].append(b)
        adj[b].append(a)
    out = []

    def go(p):
        if len(p) == k:
            out.append(tuple(p))
            return
        for w in adj[p[-1]]:
            if w not in p:
                go(p + [w])
    go([s])
    return out


def test_kpath(rnd):
    F = GF(16)
    r = {"tests": 0, "pos": 0, "fp": 0, "fn": 0}
    for _ in range(50):
        n = rnd.choice((6, 7, 8))
        E = {(a, b) for a, b in itertools.combinations(range(n), 2) if rnd.random() < rnd.choice((.25, .35, .5))}
        k = rnd.choice((4, 5, 6))
        V1 = [v for v in range(n) if rnd.random() < .5]
        s = rnd.randrange(n)
        S1 = set(V1)
        ps = kpaths(n, E, s, k)
        for k1 in range(0, k + 1):
            for l2 in range(0, k):
                if k1 + l2 > 6:
                    continue
                x = {e: rnd.randrange(F.q) for e in E}
                y = {(v, j): rnd.randrange(F.q) for v in S1 for j in range(k1)}
                z = {(e, j): rnd.randrange(F.q) for e in E for j in range(l2)}
                adm = [p for p in ps if sum(v in S1 for v in p) == k1 and sum(a not in S1 and b not in S1 for a, b in zip(p, p[1:])) == l2]
                v = kpath_eval(F, n, E, V1, s, k, k1, l2, x, y, z)
                r["tests"] += 1
                if adm:
                    r["pos"] += v != 0
                    r["fn"] += v == 0
                else:
                    r["fp"] += v != 0
    assert r["fp"] == 0 and r["fn"] <= 1 and r["pos"] >= 20, r
    print("k-path:", r)
    # Summing over all starts: a path and its reversal have the same monomial and cancel.
    Epath = {(i, i + 1) for i in range(4)}
    n = 5
    cnt = {"fixed_s_nonzero": 0, "all_s_zero": 0, "trials": 0}
    for _ in range(20):
        V1 = [1, 3]
        k, k1, l2 = 5, 2, 0
        x = {e: rnd.randrange(1, F.q) for e in Epath}
        y = {(v, j): rnd.randrange(1, F.q) for v in V1 for j in range(k1)}
        z = {}
        vs = [kpath_eval(F, n, Epath, V1, s, k, k1, l2, x, y, z) for s in range(n)]
        allx = 0
        for v in vs:
            allx ^= v
        cnt["trials"] += 1
        cnt["fixed_s_nonzero"] += vs[0] != 0
        cnt["all_s_zero"] += allx == 0
    assert cnt["fixed_s_nonzero"] >= 18 and cnt["all_s_zero"] == 20, cnt
    print("path on 5 vertices, fixed start nonzero, all starts zero:", cnt)
    global PALINDROME_FILTER
    PALINDROME_FILTER = False
    fp = 0
    for _ in range(40):
        n = rnd.choice((6, 7, 8))
        E = {(a, b) for a, b in itertools.combinations(range(n), 2) if rnd.random() < rnd.choice((.25, .35, .5))}
        k = rnd.choice((4, 5, 6))
        V1 = [v for v in range(n) if rnd.random() < .5]
        s = rnd.randrange(n)
        S1 = set(V1)
        ps = kpaths(n, E, s, k)
        for k1 in range(k + 1):
            for l2 in range(k):
                if k1 + l2 > 6 or [p for p in ps if sum(v in S1 for v in p) == k1 and sum(a not in S1 and b not in S1 for a, b in zip(p, p[1:])) == l2]:
                    continue
                x = {e: rnd.randrange(F.q) for e in E}
                y = {(v, j): rnd.randrange(F.q) for v in S1 for j in range(k1)}
                z = {(e, j): rnd.randrange(F.q) for e in E for j in range(l2)}
                fp += kpath_eval(F, n, E, V1, s, k, k1, l2, x, y, z) != 0
    PALINDROME_FILTER = True
    assert fp > 0
    print("k-path without the palindrome filter: false positives", fp)


# ------- packing
def pack_eval(F, Uni, Fam, U1, q, p0, p1, p2, xv, yv, zv):
    U1s = set(U1)
    U2 = [u for u in Uni if u not in U1s]
    nL = q * p0 + (q - 1) * p1 + (q - 2) * p2
    mul, n1 = F.mul, len(U1)
    idx = {u: i for i, u in enumerate(U1)}
    a0 = 1
    a1 = len(Fam) + 1
    a2 = a1 * (n1 + 1)
    deg = len(Fam) * a0 + n1 * a1 + n1 * a2
    w, N = F.root(deg)
    tgt = a0 * p0 + a1 * p1 + a2 * 2 * p2
    total = 0
    for i in range(N):
        W = F.pow(w, i)
        w0s, w1s, w2 = F.pow(W, a0), F.pow(W, a1), F.pow(W, a2)
        acc = 0
        for J in range(1 << nL):
            zs = {}
            zr = {}
            for u in U2:
                c = c2 = 0
                for l in range(nL):
                    if not J >> l & 1:
                        c ^= zv[(u, l)]
                        c2 ^= mul(zv[(u, l)], zv[(u, l)])
                zs[u], zr[u] = c2, c
            S = 1
            T = [[0] * n1 for _ in range(n1)]
            Dg = [1] * n1
            Off = {}
            for ia, A in enumerate(Fam):
                inter = [u for u in A if u in U1s]
                rest = [u for u in A if u not in U1s]
                xa = xv[ia]
                if len(inter) == 0:
                    t = mul(w0s, mul(xa, xa))
                    for u in rest:
                        t = mul(t, zs[u])
                    S = mul(S, 1 ^ t)
                elif len(inter) == 1:
                    t = mul(w1s, mul(xa, xa))
                    for u in rest:
                        t = mul(t, zs[u])
                    Dg[idx[inter[0]]] ^= t
                elif len(inter) == 2:
                    t = mul(w2, xa)
                    for u in rest:
                        t = mul(t, zr[u])
                    key = tuple(sorted(idx[u] for u in inter))
                    Off[key] = Off.get(key, 0) ^ t
            for a in range(n1):
                yy = yv[(a,)]
                T[a][a] = mul(mul(yy, yy), Dg[a])
                for b in range(a + 1, n1):
                    T[a][b] = T[b][a] = mul(yv[(a, b)], 1 ^ Off.get((a, b), 0))
            acc ^= mul(S, F.det(T))
        total ^= mul(acc, F.pow(w, (N - i * tgt % N) % N))
    return total


def test_packing(rnd):
    F = GF(16)
    q = 3
    r = {"tests": 0, "pos": 0, "fp": 0, "fn": 0, "prepacking_only": 0}
    for _ in range(25):
        nu = rnd.choice((6, 7, 8))
        Uni = list(range(nu))
        allsets = list(itertools.combinations(Uni, q))
        Fam = rnd.sample(allsets, rnd.choice((3, 4, 5, 6)))
        n1 = rnd.choice((2, 3, 4))
        U1 = sorted(rnd.sample(Uni, n1))
        U1s = set(U1)
        for p in (2, 3):
            for p1 in range(p + 1):
                for p2 in range(p - p1 + 1):
                    p0 = p - p1 - p2
                    if q * p0 + (q - 1) * p1 + (q - 2) * p2 > 6:
                        continue
                    if p1 + 2 * p2 > n1:
                        continue
                    truth = pre = False
                    for sub in itertools.combinations(Fam, p):
                        c = [len(set(A) & U1s) for A in sub]
                        if not (c.count(0) == p0 and c.count(1) == p1 and c.count(2) == p2):
                            continue
                        inside = [u for A in sub for u in A if u in U1s]
                        pre = pre or len(inside) == len(set(inside))
                        truth = truth or len(set().union(*sub)) == p * q
                    nL = q * p0 + (q - 1) * p1 + (q - 2) * p2
                    xv = {i: rnd.randrange(F.q) for i in range(len(Fam))}
                    yv = {(a,): rnd.randrange(F.q) for a in range(n1)}
                    yv.update({(a, b): rnd.randrange(F.q) for a in range(n1) for b in range(a + 1, n1)})
                    zv = {(u, l): rnd.randrange(F.q) for u in Uni for l in range(max(nL, 1))}
                    v = pack_eval(F, Uni, Fam, U1, q, p0, p1, p2, xv, yv, zv)
                    r["tests"] += 1
                    if truth:
                        r["pos"] += v != 0
                        r["fn"] += v == 0
                    else:
                        r["fp"] += v != 0
                        r["prepacking_only"] += pre
    assert r["fp"] == 0 and r["fn"] <= 1 and r["pos"] >= 5 and r["prepacking_only"] >= 5, r
    print("packing:", r)


rnd = random.Random(20261105)
test_ham(rnd)
test_two_factors(rnd)
test_fraction(rnd)
test_tsp(rnd)
test_kpath(rnd)
test_packing(rnd)
print("ok")
