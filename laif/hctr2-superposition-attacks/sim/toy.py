"""Simon's algorithm against HCTR2, CHCTR and HCTR++ at toy block sizes, computed exactly.

Blocks have n bits, the block ciphers are independent random permutations, and POLYVAL is Horner evaluation in GF(2^n)
(GF(2^2n) for the 2n-bit hash of HCTR++), which is the real POLYVAL up to a fixed factor x^-k in the key.
For each scheme, with x = (first block, rest) and g(x) = C(x) xor x, the script
  1. checks C(x xor s) = C(x) xor s for every x and every s in the predicted subgroup S,
  2. computes p(t) = Pr_x[g(x xor t) = g(x)] for one t in every coset of S, and eps = the largest value off S,
  3. forms the exact distribution of one Simon sample, P(y) = (1/2^D) sum_t p(t) (-1)^{t.y}, checks that it lives on
     the orthogonal complement of S, and samples from it until the samples span that complement,
  4. recovers the hash keys from one element of S and compares with the true keys.
HCTR++1 is HCTR++ with a one-block rest and g the rest of C xor x, which gives h1; HCTR++d is the same on decryption,
which gives h2. For HCTR2 it also checks that eps equals max_u #{y : E(y) xor E(y xor u) = u} / 2^n.
Run with python toy.py [trials] [seed]."""
import sys
import numpy as np

TRIALS = int(sys.argv[1]) if len(sys.argv) > 1 else 300
rng = np.random.default_rng(int(sys.argv[2]) if len(sys.argv) > 2 else 1)
POLY = {2: 0b111, 3: 0b1011, 4: 0b10011, 5: 0b100101, 6: 0b1000011, 7: 0b10000011, 8: 0b100011011,
        10: 0b10000001001, 12: 0b1000001010011}


def gmul(a, b, k):
    r = 0
    while b:
        if b & 1:
            r ^= a
        b >>= 1
        a <<= 1
        if a >> k:
            a ^= POLY[k]
    return r


def ginv(a, k):
    return next(x for x in range(1, 1 << k) if gmul(a, x, k) == 1)


def times(h, k):
    """Table of y -> h*y in GF(2^k)."""
    return np.array([gmul(h, y, k) for y in range(1 << k)], dtype=np.int64)


def perm(n):
    return rng.permutation(1 << n).astype(np.int64)


def horner(mul, blocks):
    acc = np.zeros_like(blocks[-1])
    for b in blocks:
        acc = mul[acc ^ b]
    return acc


def hctr2(E, n, T, M0, Ms):
    """One HCTR2 encryption, hbar = E(0), L = E(1), XCTR block i = E(S xor i)."""
    mul = times(int(E[0]), n)
    L = int(E[1])
    lb = (len(Ms) + 2) % (1 << n)         # stands for the length block
    MM = M0 ^ horner(mul, [lb, T] + Ms)
    UU = E[MM]
    S = MM ^ UU ^ L
    V = [m ^ E[S ^ (i + 1)] for i, m in enumerate(Ms)]
    U = UU ^ horner(mul, [lb, T] + V)
    return U, V


def split(dom, n, parts):
    out, sh = [], 0
    for w in parts:
        out.append((dom >> sh) & ((1 << w) - 1))
        sh += w
    return out


def join(vals, parts):
    x, sh = 0, 0
    for v, w in zip(vals, parts):
        x = x | (v << sh)
        sh += w
    return x


# ---------------------------------------------------------------- schemes

def scheme_hctr2(n):
    E = perm(n)
    while E[0] == 0:                      # hash key 0 has probability 2^-n and is excluded
        E = perm(n)
    T = int(rng.integers(1 << n))
    parts = [n, n]
    dom = np.arange(1 << sum(parts), dtype=np.int64)
    M0, M1 = split(dom, n, parts)
    U, V = hctr2(E, n, T, M0, [M1])
    C = join([U, V[0]], parts)
    h = int(E[0])
    S = [join([gmul(d, h, n), d], parts) for d in range(1 << n)]
    keys = {"h": h}

    def recover(s):
        a, d = split(np.int64(s), n, parts)
        return {"h": gmul(int(a), ginv(int(d), n), n)}

    ddt = max(int(np.sum((E ^ E[np.arange(1 << n) ^ u]) == u)) for u in range(1, 1 << n))
    return C, parts, S, keys, recover, ddt / (1 << n), -1


def scheme_chctr(n):
    E1, E2 = perm(n), perm(n)
    while E1[0] == 0 or E2[0] == 0 or E1[0] == E2[0]:     # excluded keys, probability at most 3/2^n
        E1, E2 = perm(n), perm(n)
    T = int(rng.integers(1 << n))
    parts = [n, n, n]
    dom = np.arange(1 << sum(parts), dtype=np.int64)
    M0, M1, M2 = split(dom, n, parts)
    U1, V1 = hctr2(E1, n, T, M0, [M1, M2])
    U2, V2 = hctr2(E2, n, T, U1, V1)
    C = join([U2, V2[0], V2[1]], parts)
    h1, h2 = int(E1[0]), int(E2[0])
    s, p = h1 ^ h2, gmul(h1, h2, n)
    S = [join([gmul(d, p, n), d, gmul(d, s, n)], parts) for d in range(1 << n)]
    keys = {"h": tuple(sorted((h1, h2)))}

    def recover(el):
        a, d1, d2 = (int(v) for v in split(np.int64(el), n, parts))
        i = ginv(d1, n)
        ss, pp = gmul(d2, i, n), gmul(a, i, n)
        roots = [x for x in range(1 << n) if gmul(x, x, n) ^ gmul(ss, x, n) ^ pp == 0]
        return {"h": tuple(sorted(roots)) if len(roots) == 2 else tuple(roots * 2)}

    return C, parts, S, keys, recover, None, -1


def scheme_hctrpp(n, blocks=2, decrypt=False):
    """HCTR++ (ePrint 2026/383, Fig. 4, as in the public reference code), with a rest of 1 or 2 hash blocks of 2n bits.
    Decryption is the same map with h1 and h2 exchanged. With 2 blocks, g = C xor x and S comes from both keys; with
    1 block, g is the rest of C xor x and S comes from the first hash key alone."""
    k = 2 * n
    M = (1 << n) - 1
    while True:                                               # ideal cipher: E_u for every key u, and E_K = P_K
        P = np.stack([perm(n) for _ in range(1 << n)])
        E = P[int(rng.integers(1 << n))]
        if E[1] | E[2] << n not in (0, E[3] | E[4] << n) and E[3] | E[4] << n != 0:   # excluded keys; needs n >= 3
            break
    Pinv = np.argsort(P, axis=1)
    blk = [int(E[i]) for i in range(1, 7)]
    h1, h2, kb = blk[0] | blk[1] << n, blk[2] | blk[3] << n, blk[4] | blk[5] << n
    ha, hb = (h2, h1) if decrypt else (h1, h2)
    ma, mb, m12, mk = times(ha, k), times(hb, k), times(h1 ^ h2, k), times(kb, k)
    T = int(rng.integers(1 << k))

    def rekey(r, x, inv=False):
        uv = horner(mk, [3, r | (1 << n)])                    # H_kbar(empty, r), r padded with 0x01
        u, v = uv & M, uv >> n
        return (Pinv if inv else P)[u, x ^ v] ^ v

    parts = [n] + [k] * blocks
    dom = np.arange(1 << sum(parts), dtype=np.int64)
    b1, *R = split(dom, n, parts)
    x1 = horner(ma, [2 * blocks - 2, T] + R)
    pp1, re = b1 ^ (x1 & M), x1 >> n
    cc = rekey(re, pp1)
    x = horner(m12, [3, T, cc | (1 << n)])
    r, j = x & M, x >> n
    ks = [rekey(r ^ i, j ^ i) for i in range(1, 2 * blocks + 1)]
    O = [Ri ^ (ks[2 * i] | ks[2 * i + 1] << n) for i, Ri in enumerate(R)]
    x2 = horner(mb, [2 * blocks - 2, T] + O)
    out1 = rekey(x2 >> n, cc, inv=True) ^ (x2 & M)
    C = join([out1] + O, parts)
    S = []
    if blocks == 2:
        s, p = h1 ^ h2, gmul(h1, h2, k)
        for d in range(1 << k):
            q = gmul(d, p, k)
            if q >> n == 0:
                S.append(join([q, d, gmul(d, s, k)], parts))
        keys = {"h": tuple(sorted((h1, h2)))}

        def recover(el):
            a, d1, d2 = (int(v) for v in split(np.int64(el), n, parts))
            i = ginv(d1, k)
            ss, pp = gmul(d2, i, k), gmul(a, i, k)
            roots = [y for y in range(1 << k) if gmul(y, y, k) ^ gmul(ss, y, k) ^ pp == 0]
            return {"h": tuple(sorted(roots)) if len(roots) == 2 else tuple(roots * 2)}
        gmask = -1
    else:
        for d in range(1 << k):
            q = gmul(d, ha, k)
            if q >> n == 0:
                S.append(join([q, d], parts))
        keys = {"h": ha}

        def recover(el):
            a, d = (int(v) for v in split(np.int64(el), n, parts))
            return {"h": gmul(a, ginv(d, k), k)}
        gmask = ~M
    return C, parts, S, keys, recover, None, gmask


# ---------------------------------------------------------------- analysis

def wht(a):
    a = a.astype(np.float64).copy()
    h = 1
    while h < len(a):
        a = a.reshape(-1, 2, h)
        a = np.stack([a[:, 0] + a[:, 1], a[:, 0] - a[:, 1]], axis=1).reshape(-1)
        h *= 2
    return a


def rank_add(basis, v):
    for b in basis:
        v = min(v, v ^ b)
    if v:
        basis.append(v)
        basis.sort(reverse=True)
        return True
    return False


def complement(basis, D):
    """The set of y with y.b = 0 for every b in basis."""
    ys = np.arange(1 << D, dtype=np.int64)
    ok = np.ones(1 << D, dtype=bool)
    for b in basis:
        ok &= (np.bitwise_count(ys & b) & 1) == 0
    return set(ys[ok].tolist())


def analyse(name, n, scheme):
    C, parts, S, keys, recover, ddt, gmask = scheme(n)
    D = sum(parts)
    w0 = parts[0]
    dom = np.arange(1 << D, dtype=np.int64)
    g = (C ^ dom) & gmask
    if gmask == -1:
        inv_ok = all(np.array_equal(C[dom ^ s], C ^ s) for s in S)
    else:
        inv_ok = all(np.array_equal(g[dom ^ s], g) for s in S)
    dimS = len(S).bit_length() - 1
    # p(t) for the coset representatives t with first block 0 (the first block determines the element of S)
    first = {int(s) & ((1 << w0) - 1): int(s) for s in S}
    reps = np.arange(1 << (D - w0), dtype=np.int64) << w0
    p_rep = np.array([np.mean(g[dom ^ t] == g) for t in reps])
    eps = p_rep[1:].max()
    # p on the whole group: t = (a, rest) lies in the coset of (0, rest xor rest(s_a))
    a = dom & ((1 << w0) - 1)
    sa = np.array([first[int(v)] for v in range(1 << w0)], dtype=np.int64)[a]
    p_full = p_rep[(dom ^ sa) >> w0]
    P = wht(p_full) / (1 << D)
    Sperp = complement([int(s) for s in S], D)
    mass_off = P[[y for y in range(1 << D) if y not in Sperp]].sum() if len(Sperp) < (1 << D) else 0.0
    P = np.clip(P, 0, None)
    P /= P.sum()
    need = D - dimS
    cdf = np.cumsum(P)
    counts, wrong = [], 0
    for _ in range(TRIALS):
        basis, c = [], 0
        while len(basis) < need and c < 100 * need:
            rank_add(basis, min(int(np.searchsorted(cdf, rng.random() * cdf[-1])), (1 << D) - 1))
            c += 1
        counts.append(c)
        Srec = complement(basis, D)
        wrong += Srec != set(int(s) for s in S)
    bound = sum(1 / (1 - 2.0 ** -i - eps) for i in range(1, need + 1)) if eps < 0.5 else float("inf")
    el = next(int(s) for s in S if int(s) & ((1 << w0) - 1))
    rec_ok = recover(el) == keys
    extra = f" ddt/2^n={ddt:.4f} eq={abs(ddt - eps) < 1e-12}" if ddt is not None else ""
    print(f"{name:7s} n={n} D={D:2d} dimS={dimS} invariant={inv_ok} eps={eps:.4f} off-mass={mass_off:.1e} "
          f"samples mean={np.mean(counts):.2f} max={max(counts)} need={need} bound={bound:.2f} "
          f"wrongS={wrong} keys={rec_ok}{extra}", flush=True)
    return inv_ok and wrong == 0 and rec_ok and mass_off < 1e-9 and np.mean(counts) <= bound + 3 * np.std(counts) / np.sqrt(TRIALS) and eps < 1


if __name__ == "__main__":
    ok = True
    for n in (3, 4, 5, 6, 7, 8):
        ok &= analyse("HCTR2", n, scheme_hctr2)
    for n in (3, 4, 5, 6):
        ok &= analyse("CHCTR", n, scheme_chctr)
    for n in (3,):
        ok &= analyse("HCTR++", n, scheme_hctrpp)
    for n in (3, 4, 5):
        ok &= analyse("HCTR++1", n, lambda n: scheme_hctrpp(n, 1))
        ok &= analyse("HCTR++d", n, lambda n: scheme_hctrpp(n, 1, True))
    print("all checks passed" if ok else "SOME CHECK FAILED")
    sys.exit(0 if ok else 1)
