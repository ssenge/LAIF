"""Tests the combinatorial steps of the label algorithm on real instances, with the quantum searches
replaced by exhaustive classical ones. It checks the proof's claims, not any quantum speedup."""
import math, random
from collections import Counter
from itertools import combinations, product

A1, A0 = 0.12765, 0.15397       # optimum at p = 1/4 from exact.py
SIGMA = 0.26326

def is_prime(m):
    return m > 1 and all(m % d for d in range(2, int(m**.5)+1))

def prime_in(lo, rng):
    while True:
        q = rng.randint(lo, 2*lo)
        if is_prime(q):
            return q

def layout(n):
    z = round(n/4)
    minus = (n - z)//2
    plus = n - z - minus            # one more +1 than -1 when the support is odd
    a0, a1 = round(A0*n), round(A1*n)
    b0, b1 = (z - a0)//2, (minus - a1)//2
    # counts per label as (d=-1, d=0, d=+1); plus > minus puts the extra +1 on label A
    return dict(z=z, plus=plus, minus=minus, A=(a1, a0, a1 + plus - minus), B=(b1, b0, b1), C=(minus-a1-b1, z-a0-b0, minus-a1-b1))

def plant(n, kind, rng):
    """y with a planted balanced D. 'heavy' turns coordinates into pairs (g, 2g), which give the lists
    huge equal-sum classes (d1 + 2 d2 = 0 has only the zero solution on {-1,0,1}) with no new solution."""
    L = layout(n)
    D = [1]*L["plus"] + [-1]*L["minus"] + [0]*L["z"]
    y = [rng.getrandbits(3*n) for _ in range(n)]
    if kind == "heavy":
        for i in range(1, n-1, 2):
            y[i+1] = 2*y[i]
    y[0] = 0
    y[0] = -sum(d*v for d, v in zip(D, y))
    order = list(range(n)); rng.shuffle(order)
    return [y[i] for i in order], [D[i] for i in order], L

def min_support(y):
    """Smallest support of a nonzero {-1,0,1} solution, by meet in the middle."""
    h = len(y)//2
    left = {}
    for e in product((-1, 0, 1), repeat=h):
        v, s = sum(a*b for a, b in zip(e, y)), sum(map(abs, e))
        left[v] = min(s, left.get(v, 99), ) if s else left.get(v, 99)
    best = 99
    for e in product((-1, 0, 1), repeat=len(y)-h):
        v, s = sum(a*b for a, b in zip(e, y[h:])), sum(map(abs, e))
        if -v in left:
            best = min(best, s + left[-v])
        if s and v == 0:
            best = min(best, s)
    return best

def good_partition(D, L, rng):
    lab = {}
    for pos, d in enumerate((-1, 0, 1)):
        idx = [i for i in range(len(D)) if D[i] == d]
        rng.shuffle(idx)
        cuts = iter(idx)
        for name in "ABC":
            for _ in range(L[name][pos]):
                lab[next(cuts)] = name
    return lab

def side(y, lab, L, swap):
    """The list X, or Y when swap, as (sum, vector). A: {0,1}, B: typed {0,1,2}, C: constant 1."""
    A, B, C = ([i for i in lab if lab[i] == c] for c in ("ACB" if swap else "ABC"))
    nm, n0, np_ = L["C" if swap else "B"]
    nzero, ntwo = (np_, nm) if swap else (nm, np_)
    aminus, af, aplus = L["A"]
    ones = (aminus if swap else aplus) + (af - af//2)
    base = sum(y[i] for i in C)
    Bs = []
    for zeros in combinations(B, nzero):
        rest = [i for i in B if i not in zeros]
        for twos in combinations(rest, ntwo):
            v = {i: 1 for i in rest}
            v.update({i: 0 for i in zeros}); v.update({i: 2 for i in twos})
            Bs.append((sum(y[i]*w for i, w in v.items()), v))
    for pick in combinations(A, ones):
        sa = sum(y[i] for i in pick)
        for sb, v in Bs:
            yield base + sa + sb, pick, v

def vector(n, lab, swap, pick, v):
    out = [1]*n
    for i in lab:
        if lab[i] == "A":
            out[i] = int(i in pick)
    for i, w in v.items():
        out[i] = w
    return out

def run(n, kind, seed, st):
    rng = random.Random(seed)
    y, D, L = plant(n, kind, rng)
    assert sum(a*b for a, b in zip(D, y)) == 0
    st["odd support"] += sum(map(abs, D)) % 2
    if n <= 20 and min_support(y) != sum(map(abs, D)):
        st["discarded, smaller solution"] += 1
        return
    lab = good_partition(D, L, rng)
    X, Y = list(side(y, lab, L, False)), list(side(y, lab, L, True))
    st["runs"] += 1
    cx, cy = Counter(t[0] for t in X), Counter(t[0] for t in Y)
    st["max class"] = max(st["max class"], max(cx.values()))
    common = set(cx) & set(cy)
    a0 = L["A"][1]
    K = math.comb(a0, a0//2)
    assert len(common) >= K, (len(common), K)   # the K representations have distinct sums
    # any equal-sum pair is a real solution
    if n <= 20:
        xv = {t[0]: t for t in X if t[0] in common}
        for t in Y:
            if t[0] in xv:
                _, px, vx = xv[t[0]]
                dif = [a-b for a, b in zip(vector(n, lab, False, px, vx), vector(n, lab, True, t[1], t[2]))]
                assert set(dif) <= {-1, 0, 1} and any(dif) and sum(a*b for a, b in zip(dif, y)) == 0
                st["pairs verified"] += 1
    s = max(2, round(2**(SIGMA*n)))
    P = prime_in(K*s, rng)
    bx, by = {}, {}
    for t in X: bx.setdefault(t[0] % P, []).append(t[0])
    for t in Y: by.setdefault(t[0] % P, []).append(t[0])
    T = 4*n*len(X)//P + 1       # the proof's cap T = O(n) U/P
    good = 0
    for rho in {v % P for v in common}:
        wx, wy = bx[rho], by[rho]
        if len(wx) > T:
            st["capped bins"] += 1
            wx = wx[:T]
        if len(wy) > T:
            st["capped bins"] += 1
            wy = wy[:T]
        good += bool(set(wx) & set(wy))
    st["reps"] += K
    st["good residues"] += good
    st["good fraction * s * n >= 1"] += good/P*s*n >= 1

if __name__ == "__main__":
    for n, runs in ((15, 40), (19, 30), (20, 30), (23, 8), (24, 6)):
        for kind in ("random", "heavy"):
            st = Counter()
            for seed in range(runs):
                run(n, kind, 1000*n+seed, st)
            print(n, kind, dict(st), flush=True)
