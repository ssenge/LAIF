"""Re-evaluates a saved certificate in interval arithmetic: the boxes cover the simplex, and on each box every tangent
bound and side condition holds. Shares only the label set with certify.py. Usage: python verify.py d"""
import math, os, pickle, sys
os.environ["OMP_NUM_THREADS"] = "1"
from itertools import product
from multiprocessing import Pool
from mpmath import iv

iv.dps = 30
ZERO, ONE = iv.mpf(0), iv.mpf(1)
LOG2 = iv.log(iv.mpf(2))


def lg(x):
    return iv.log(x)/LOG2


d = int(sys.argv[1])
CERT = pickle.load(open(f"cert_{d}.pkl", "rb")) if len(sys.argv) > 1 else None
LABS = [(s, 2*d - s, s - d) for s in range(2*d + 1)]
CELLS = [(L, x, o + y) for L, (s, t, o) in enumerate(LABS) for x in range(s + 1) for y in range(t + 1)]
TARGET = iv.mpf(CERT["target"])
CS = list(range(-d, d + 1))


def pi_of(w):
    w0 = ONE - sum(w, ZERO)
    return {c: (w0 if c == 0 else w[abs(c) - 1]/2) for c in CS}


def group(q, key):
    out = {}
    for cell, m in q.items():
        k = key(cell)
        out[k] = out.get(k, ZERO) + m
    return out


def forms(Wf, centre):
    """Value at the centre and coefficients per c of a, a0, ux, uy, as tangents in pi."""
    tot = {}
    for cell, v in Wf.items():
        c = cell[1] - cell[2]
        tot[c] = tot.get(c, ZERO) + iv.mpf(v)
    W = {cell: iv.mpf(v)/tot[cell[1] - cell[2]] for cell, v in Wf.items()}
    pi0 = pi_of(centre)
    q0 = {cell: W[cell]*pi0[cell[1] - cell[2]] for cell in W}
    mL = group(q0, lambda e: e[0])
    mCL = group(q0, lambda e: (e[1] - e[2], e[0]))
    mX = group(q0, lambda e: (e[1], e[0]))
    mY = group(q0, lambda e: (e[2], e[0]))
    mC = group(q0, lambda e: e[1] - e[2])
    H = lambda m: -sum((v*lg(v) for v in m.values()), ZERO)
    hL, hCL, hC, hX, hY = H(mL), H(mCL), H(mC), H(mX), H(mY)
    hA = H(q0)
    vals = dict(a=hC + hL - hCL, a0=hA - hCL, ux=hX - hL, uy=hY - hL)
    # gradients in q; the constants -1/ln 2 cancel in each difference, and sum(q - q0) = 0 handles a
    coef = {k: {c: ZERO for c in CS} for k in vals}
    for e in W:
        L, x, y = e
        c = x - y
        g = {"a": -lg(mC[c]) - lg(mL[L]) + lg(mCL[c, L]),
             "a0": -lg(q0[e]) + lg(mCL[c, L]),
             "ux": -lg(mX[x, L]) + lg(mL[L]),
             "uy": -lg(mY[y, L]) + lg(mL[L])}
        for k in coef:
            coef[k][c] += g[k]*W[e]
    return W, pi0, vals, coef


def corners(lo, hi):
    return list(product(*zip(lo, hi)))


def check(entry):
    box, kind, Wf, sigma = entry
    lo, hi = box
    c = [(a + b)/2 for a, b in zip(lo, hi)]
    s = sum(c)
    if s >= 1 - 1e-4:
        c = [x/s*(1 - 1e-4) for x in c]
    c = [iv.mpf(max(x, 1e-6)) for x in c]
    cs = [[iv.mpf(x) for x in v] for v in corners(lo, hi)]
    pi0 = pi_of(c)
    if kind == "grover":
        h0 = -sum((v*lg(v) for v in pi0.values()), ZERO)
        grad = {k: -lg(v) for k, v in pi0.items()}
        for v in cs:
            pi = pi_of(v)
            b = h0/2 + sum((grad[k]*(pi[k] - pi0[k]) for k in CS), ZERO)/2
            if not b.b < TARGET.a:
                return False
        return True
    if not sigma >= 0 or min(Wf) < 0:
        return False
    Wf = {CELLS[i]: v for i, v in enumerate(Wf) if v > 0}
    if {e[1] - e[2] for e in Wf} != set(CS):      # every value of the profile needs a row of the kernel
        return False
    W, pi0, vals, coef = forms(Wf, c)
    sg = iv.mpf(sigma)
    for v in cs:
        pi = pi_of(v)
        t = {k: vals[k] + sum((coef[k][q]*(pi[q] - pi0[q]) for q in CS), ZERO) for k in vals}
        terms = [t["a"]/2 + t["a0"] + sg,
                 t["a"]/2 + sg/2 + 2*(t["ux"] - t["a0"] - sg)/3,
                 t["a"]/2 + sg/2 + 2*(t["uy"] - t["a0"] - sg)/3,
                 t["a"]/2 + sg/2]
        if not all(x.b < TARGET.a for x in terms):
            return False
        if not (t["a0"] + sg).a > 0:
            return False
    # representations vary only on (c, L) classes with at least two positive kernel entries
    counts = {}
    for e in W:
        k = (e[1] - e[2], e[0])
        counts[k] = counts.get(k, 0) + 1
    vary = [e for e in W if counts[e[1] - e[2], e[0]] > 1]
    if vary:
        for v in cs:
            pi = pi_of(v)
            if not (ONE - pi[0] - sum((W[e]*pi[e[1] - e[2]] for e in vary), ZERO)).a > 0:
                return False
    return True


def covered(done):
    have = {tuple(map(tuple, e[0])) for e in done}
    size = 1/8
    m = round(1/size)
    stack = [(tuple(i*size for i in t), tuple((i + 1)*size for i in t)) for t in product(range(m), repeat=d) if sum(t) < m]
    while stack:
        lo, hi = stack.pop()
        if sum(lo) >= 1 or (lo, hi) in have:
            continue
        if hi[0] - lo[0] < 1e-6:
            return False
        mid = [(a + b)/2 for a, b in zip(lo, hi)]
        for bits in product((0, 1), repeat=d):
            stack.append((tuple(l if not b else q for l, q, b in zip(lo, mid, bits)),
                          tuple(q if not b else h for h, q, b in zip(hi, mid, bits))))
    return True


if __name__ == "__main__":
    done = CERT["done"]
    assert not CERT["left"], "the certificate has open boxes"
    assert covered(done), "the boxes do not cover the simplex"
    with Pool(11) as p:
        res = p.map(check, done, chunksize=16)
    print(f"d={d} target={CERT['target']}: {sum(res)}/{len(res)} boxes verified in interval arithmetic; covers the simplex")
    sys.exit(0 if all(res) else 1)
