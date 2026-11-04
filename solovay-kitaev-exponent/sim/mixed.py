"""Mixed-level word recursions on SU(2), with free reduction counted.

Elkasapy's recursion multiplies words from two levels and gains from free cancellation. Yehuda's
multiplies sign-flipped copies from one level. This searches the common generalization:
    new = prod_m sigma_m(W_{level_m}),   W_0 the newest word, sigma_m any of the 8 sign patterns.
Valuations are bounded below by treating the components of each level as independent variables,
as in recursion.py. Lengths are exact reduced lengths of actual words in p, q.

Potential: psi = log2(x0^2 a + x0 b + c) - delta log2(L), for sorted valuations a >= b >= c.
(x0^2, x0, 1) is the left eigenvector of Yehuda's step, so psi stays bounded along his chain.
A recursion that beats tribonacci makes psi grow without bound.
"""
import math
import sys

import numpy as np

from recursion import DELTA, PATTERNS, X0

BIG = 1e12
P = 1048573
LEVELS, MMAX = (int(sys.argv[1]), int(sys.argv[2])) if len(sys.argv) > 2 else (2, 4)


# --- words -------------------------------------------------------------------------------------
TAU = str.maketrans("pqPQ", "qpQP")
RHO = str.maketrans("pqPQ", "QPqp")
TR = str.maketrans("pqPQ", "PQpq")
SWAP = str.maketrans("pqPQ", "PQpq")  # letters to their inverses


def inverse(w):
    return w[::-1].translate(SWAP)


def image(w, s):
    """Word with imaginary signs multiplied by s = (sx, sy, sz)."""
    if s[0] * s[1] * s[2] < 0:
        return inverse(image(w, (-s[0], -s[1], -s[2])))
    table = {(1, 1, 1): None, (1, -1, -1): TAU, (-1, 1, -1): RHO, (-1, -1, 1): TR}[s]
    return w if table is None else w.translate(table)


def concat(parts):
    """Concatenation with free reduction at the junctions."""
    out = parts[0]
    for w in parts[1:]:
        k = 0
        while k < len(out) and k < len(w) and out[-1 - k] == w[k].translate(SWAP):
            k += 1
        out = out[: len(out) - k] + w[k:]
    return out


# --- templates ---------------------------------------------------------------------------------
def mul(q, level, s, levels):
    def shift(poly, comp, sign):
        out = {}
        i = 3 * level + comp
        for e, c in poly.items():
            f = e[:i] + (e[i] + 1,) + e[i + 1:]
            out[f] = sign * c
        return out
    def add(*ps):
        out = {}
        for p in ps:
            for e, c in p.items():
                out[e] = out.get(e, 0) + c
        return {e: c for e, c in out.items() if c}
    sx, sy, sz = s
    a, b, c, d = q
    return (add(a, shift(b, 0, -sx), shift(c, 1, -sy), shift(d, 2, -sz)),
            add(b, shift(a, 0, sx), shift(c, 2, sz), shift(d, 1, -sy)),
            add(c, shift(a, 1, sy), shift(b, 2, -sz), shift(d, 0, sx)),
            add(d, shift(a, 2, sz), shift(b, 1, sy), shift(c, 0, -sx)))


def pareto(poly):
    pts = list(poly)
    return tuple(sorted(p for p in pts if not any(q != p and all(u <= v for u, v in zip(q, p)) for q in pts)))


def templates(levels, mmax, per_key=4):
    table = {}
    zero = (0,) * (3 * levels)
    def rec(q, seq):
        if len(seq) >= 2 and any(l == 0 for l, _ in seq):
            counts = tuple(sum(1 for l, _ in seq if l == i) for i in range(levels))
            key = (pareto(q[1]), pareto(q[2]), pareto(q[3]), counts)
            if any(key[:3]):
                bag = table.setdefault(key, [])
                if len(bag) < per_key:
                    bag.append(tuple(seq))
        if len(seq) == mmax:
            return
        for level in range(levels):
            for s in PATTERNS:
                if not seq and s != (1, 1, 1):
                    continue
                rec(mul(q, level, s, levels), seq + [(level, s)])
    rec(({zero: 1}, {}, {}, {}), [])
    return table


def pack(table, levels):
    keys = list(table)
    m = max(len(k[c]) for k in keys for c in range(3))
    arr = np.zeros((len(keys), 3, m, 3 * levels), dtype=np.float64)
    mask = np.zeros((len(keys), 3, m), dtype=bool)
    for t, k in enumerate(keys):
        for c in range(3):
            for i, e in enumerate(k[c]):
                arr[t, c, i] = e
                mask[t, c, i] = True
    needs = np.array([[k[3][i] > 0 for i in range(levels)] for k in keys])
    weight = np.array([k[3] for k in keys], dtype=np.float64)
    return keys, arr, mask, needs, weight


def zero_cap(L):
    """A component of a word of length L is a form of degree L in (c, s, t). Multiplying out by its
    conjugate in c gives a polynomial in s, t of degree <= 2L, of weight <= 4L. So a nonzero component
    has valuation at most 4L, and a larger lower bound means the component vanishes exactly."""
    return 4 * L + 4


def psi(v, L):
    f = sorted(x for x in v if x < min(BIG, zero_cap(L)))
    if not f:
        return -math.inf
    c = f[0]
    b = f[1] if len(f) > 1 else c
    a = f[2] if len(f) > 2 else b
    return math.log2(X0 * X0 * a + X0 * b + c) - DELTA * math.log2(max(L, 1))


# --- exact check -------------------------------------------------------------------------------
def true_vals(word, K, seed=5):
    """Valuations of X, Y, Z at a random point of the normal form, s = alpha e, t = beta e^2."""
    rng = np.random.default_rng(seed)
    alpha, beta = (int(x) for x in rng.integers(1, P, 2))
    f = np.zeros(K, dtype=np.int64)
    if K > 2:
        f[2] = alpha * alpha % P
    if K > 4:
        f[4] = beta * beta % P
    c = np.zeros(K, dtype=np.int64)
    c[0] = 1
    half = pow(2, -1, P)
    for n in range(1, K):
        c[n] = (-f[n] - int((c[1:n] * c[n - 1:0:-1]).sum() % P)) * half % P
    def conv(a, b):
        return np.convolve(a, b)[:K] % P
    def sh(a, k, m):
        out = np.zeros(K, dtype=np.int64)
        out[k:] = a[:K - k] * m % P
        return out
    u = [np.zeros(K, dtype=np.int64) for _ in range(4)]
    u[0][0] = 1
    gen = {"p": (alpha, beta), "q": (alpha, -beta), "P": (-alpha, -beta), "Q": (-alpha, beta)}
    for ch in word:
        s, t = gen[ch]
        a, b, g, d = u
        u = [(conv(a, c) - sh(b, 1, s) - sh(g, 2, t)) % P,
             (conv(b, c) + sh(a, 1, s) - sh(d, 2, t)) % P,
             (conv(g, c) + sh(a, 2, t) + sh(d, 1, s)) % P,
             (conv(d, c) + sh(b, 2, t) - sh(g, 1, s)) % P]
    def val(a):
        nz = np.nonzero(a)[0]
        return int(nz[0]) if len(nz) else K
    return val(u[1]), val(u[2]), val(u[3])


# --- search ------------------------------------------------------------------------------------
class State:
    __slots__ = ("window", "vals", "psi", "parent", "move")

    def __init__(self, window, vals, parent, move):
        cap = zero_cap(len(window[0]))
        w, inv = window[0], inverse(window[0])
        # X = 0 on SU(2) iff tau(w) = w^-1 as elements, which holds iff as reduced words, as SU(2) has no law
        zero = [image(w, s) == inv for s in ((1, -1, -1), (-1, 1, -1), (-1, -1, 1))]
        vals = tuple(BIG if (x > cap or z) else x for x, z in zip(vals[:3], zero)) + tuple(vals[3:])
        self.window, self.vals, self.parent, self.move = window, vals, parent, move
        self.psi = psi(vals[:3], len(window[0]))


def search(pack_, levels, horizon, width, per_state):
    keys, arr, mask, needs, weight = pack_
    table = TABLE
    buckets = {}
    def push(st):
        buckets.setdefault(round(math.log2(len(st.window[0])) * 4), []).append(st)
    push(State(("p",), (1.0, 2.0, BIG), None, None))
    best = {}
    visited = set()
    global BEST_MIN
    BEST_MIN = {}
    while buckets:
        b = min(buckets)
        states = []
        for st in sorted(buckets.pop(b), key=lambda s: -s.psi):
            sig = (tuple(round(x, 3) for x in st.vals), tuple(len(w) for w in st.window))
            if sig not in visited:  # global: free reduction can send a word back to an earlier bucket
                visited.add(sig)
                states.append(st)
            if len(states) == width:
                break
        for st in states:
            if min(st.vals[:3]) < BIG and (b not in BEST_MIN or min(st.vals[:3]) > min(BEST_MIN[b].vals[:3])):
                BEST_MIN[b] = st
        if states and (b not in best or states[0].psi > best[b].psi):
            best[b] = states[0]
            print(f"  bucket {b / 4:6.2f} psi {states[0].psi:6.3f} min val {min(states[0].vals[:3]):8.0f}", flush=True)
        for st in states:
            n = len(st.window)
            v = np.full(3 * levels, BIG)
            v[: 3 * n] = st.vals
            lens = np.array([len(st.window[i]) if i < n else 0 for i in range(levels)], dtype=np.float64)
            ok = ~needs[:, n:].any(axis=1)
            vals = (arr @ v).astype(np.float64)
            vals[~mask] = np.inf
            vals = vals.min(axis=2)
            formal = weight @ lens
            vals = np.where(vals > 4 * formal[:, None] + 4, BIG, vals)
            finite = vals.min(axis=1) < BIG
            s = np.sort(vals, axis=1)
            a = np.where(s[:, 2] < BIG, s[:, 2], np.where(s[:, 1] < BIG, s[:, 1], s[:, 0]))
            bb = np.where(s[:, 1] < BIG, s[:, 1], s[:, 0])
            score = np.log2(X0 * X0 * a + X0 * bb + s[:, 0]) - DELTA * np.log2(np.maximum(formal, 1))
            score[~(ok & finite)] = -np.inf
            for t in np.argsort(-score)[:per_state]:
                if not np.isfinite(score[t]):
                    break
                new_vals = tuple(float(x) for x in vals[t])
                for seq in table[keys[t]]:
                    w = concat([image(st.window[l], sg) for l, sg in seq])
                    if not w or math.log2(len(w)) > horizon:
                        continue
                    window = ((w,) + st.window)[:levels]
                    push(State(window, (new_vals + st.vals)[: 3 * levels], st, seq))
    return best


def chain(st):
    out = []
    while st.parent is not None:
        out.append(st.move)
        st = st.parent
    return out[::-1]


if __name__ == "__main__":
    # Yehuda: seed and two steps, exact valuations of Lemma 4.1 and Proposition 5.2
    u0 = "ppQP"
    assert true_vals(u0, 12) == (5, 2, 3)
    u1 = concat([u0, image(u0, (1, -1, -1))])
    assert true_vals(u1, 30) == (5, 8, 7), true_vals(u1, 30)
    u2 = concat([u1, image(u1, (-1, 1, -1))])
    assert true_vals(u2, 30) == (15, 8, 13), true_vals(u2, 30)
    # Elkasapy: w_{n+2} = [w_{n+1}^-1, w_n], order f_n, length about 13 * 2^(n-2) / 7
    w = ["p", "q"]
    fib = [1, 1]
    for n in range(2, 12):
        a, b = w[-1], w[-2]
        w.append(concat([inverse(a), b, a, inverse(b)]))
        fib.append(fib[-1] + fib[-2])
    for n in range(2, 12):
        assert len(w[n]) in {(13 * 2 ** (n - 1) + e) // 7 for e in (2, 4, -6)}, (n, len(w[n]))
    assert min(true_vals(w[8], 60)) >= fib[8]  # above f_n here, since p and q are closer than generic g, h
    assert image("pQ", (1, -1, -1)) == inverse("pQ")  # X = 0 for p q^-1: its X-component vanishes
    assert true_vals("pQ", 20)[0] == 20
    print("self-check ok: Yehuda valuations and Elkasapy lengths and orders reproduced")

    TABLE = templates(LEVELS, MMAX)
    print(f"levels={LEVELS} M<={MMAX}: {len(TABLE)} distinct templates", flush=True)
    packed = pack(TABLE, LEVELS)
    horizon = float(sys.argv[3]) if len(sys.argv) > 3 else 14
    width = int(sys.argv[4]) if len(sys.argv) > 4 else 30
    per_state = int(sys.argv[5]) if len(sys.argv) > 5 else 60
    best = search(packed, LEVELS, horizon, width, per_state)
    # Yehuda's chain, for comparison: |u_n| = 4 * 2^n, order d_n
    d = {-1: 1, 0: 2, 1: 5}
    for n in range(2, 40):
        d[n] = d[n - 1] + d[n - 2] + d[n - 3]
    print("  log2 L  best min val  ratio to Yehuda   best-psi state")
    for b in sorted(BEST_MIN):
        st = BEST_MIN[b]
        L = len(st.window[0])
        n = math.log2(L / 4)
        base = d[math.floor(n)] * X0 ** (n - math.floor(n)) if n >= 0 else 1
        print(f"  {b / 4:6.2f} {min(st.vals[:3]):10.0f} {min(st.vals[:3]) / base:10.3f}   L={L} {st.vals[:3]}  psi {best[b].psi:.3f} {best[b].vals[:3]}", flush=True)
    top = max(BEST_MIN.values(), key=lambda s: math.log2(min(s.vals[:3])) - DELTA * math.log2(len(s.window[0])) if len(s.window[0]) > 1000 else -1e9)
    print("best deep chain:", len(top.window[0]), top.vals[:3])
    for move in chain(top):
        print("   ", move)
    print("exact valuations:", true_vals(top.window[0], 3000) if len(top.window[0]) < 3000 else "skipped")
