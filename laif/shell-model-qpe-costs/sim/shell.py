"""M-scheme shell-model Hamiltonian from a KSHELL .snt file (proton-neutron formalism, normalized J-coupled TBMEs).
H = sum_p t_p n_p + sum_{p<q, r<s} W[p,q,r,s] a+_p a+_q a_s a_r, with W[p,q,r,s] = W[r,s,p,q]."""
import math, itertools
from functools import lru_cache
import numpy as np
from sympy.physics.quantum.cg import CG
from sympy import S

def read_snt(path):
    L = [l.split("!")[0].split() for l in open(path)]
    L = [l for l in L if l]
    npo, nno = int(L[0][0]), int(L[0][1])
    orbs = {}
    for l in L[1:1 + npo + nno]:
        i, n, lq, j2, tz = map(int, l[:5]); orbs[i] = (n, lq, j2, tz)
    k = 1 + npo + nno
    n1 = int(L[k][0]); spe = {}
    for l in L[k + 1:k + 1 + n1]:
        spe[(int(l[0]), int(l[1]))] = float(l[2])
    k += 1 + n1
    hdr = L[k]; ntb, mass_method = int(hdr[0]), int(hdr[1])
    A0, p = (float(hdr[2]), float(hdr[3])) if mass_method == 1 else (None, None)
    tb = [(int(l[0]), int(l[1]), int(l[2]), int(l[3]), int(l[4]), float(l[5])) for l in L[k + 1:k + 1 + ntb]]
    return orbs, spe, tb, A0, p

@lru_cache(None)
def cg(j1, m1, j2, m2, J, M):   # arguments are doubled (2j, 2m)
    if m1 + m2 != M: return 0.0
    return float(CG(S(j1) / 2, S(m1) / 2, S(j2) / 2, S(m2) / 2, S(J), S(M) / 2).doit())

def build(path, A):
    orbs, spe, tb, A0, p = read_snt(path)
    states = []                                   # (orbit, 2m)
    for i in sorted(orbs):
        j2 = orbs[i][2]
        for m2 in range(-j2, j2 + 1, 2): states.append((i, m2))
    idx = {s: k for k, s in enumerate(states)}
    t = np.zeros(len(states))
    for (i, j), v in spe.items():
        assert i == j
        for k, (o, m2) in enumerate(states):
            if o == i: t[k] = v
    scale = (A / A0) ** p if A0 else 1.0     # KSHELL: (A/A0)^p
    # coefficient of a+_p a+_q a_s a_r (unordered), from sum_{J,M} V_J(ab,cd) A+_{abJM} A_{cdJM}
    C = {}
    def pairop(a, b, J, M):     # A+_{abJM} = N sum CG a+_{a ma} a+_{b mb}
        N = 1 / math.sqrt(2) if a == b else 1.0
        out = []
        for ma in range(-orbs[a][2], orbs[a][2] + 1, 2):
            mb = 2 * M - ma
            if abs(mb) > orbs[b][2]: continue
            c = cg(orbs[a][2], ma, orbs[b][2], mb, J, 2 * M)
            if c: out.append((idx[(a, ma)], idx[(b, mb)], N * c))
        return out
    seen = set()
    for (a, b, c, d, J, v) in tb:
        for (x, y) in (((a, b), (c, d)), ((c, d), (a, b))):
            key = (x, y, J)
            if key in seen: continue
            seen.add(key)
            for M in range(-J, J + 1):
                for (p1, q1, c1) in pairop(*x, J, M):
                    for (r1, s1, c2) in pairop(*y, J, M):
                        C[(p1, q1, r1, s1)] = C.get((p1, q1, r1, s1), 0) + v * scale * c1 * c2
    # canonicalize to p<q, r<s:  a+_p a+_q a_s a_r is antisymmetric in (p,q) and in (r,s)
    W = {}
    for (p1, q1, r1, s1), v in C.items():
        if p1 == q1 or r1 == s1: continue
        sg = 1
        if p1 > q1: p1, q1, sg = q1, p1, -sg
        if r1 > s1: r1, s1, sg = s1, r1, -sg
        W[(p1, q1, r1, s1)] = W.get((p1, q1, r1, s1), 0) + sg * v
    W = {k: v for k, v in W.items() if abs(v) > 1e-12}
    for (p1, q1, r1, s1), v in W.items():
        assert abs(W.get((r1, s1, p1, q1), 0) - v) < 1e-10      # hermitian
    return states, orbs, t, W

def basis(states, orbs, Zv, Nv, M2):
    prot = [k for k, (o, m) in enumerate(states) if orbs[o][3] == -1]
    neut = [k for k, (o, m) in enumerate(states) if orbs[o][3] == 1]
    out = []
    for P in itertools.combinations(prot, Zv):
        for Nn in itertools.combinations(neut, Nv):
            if sum(states[k][1] for k in P + Nn) == M2:
                out.append(sum(1 << k for k in P + Nn))
    return np.array(sorted(out), dtype=np.uint64)

def sign_before(x, k):   # (-1)^(number of occupied modes below k), vectorized
    mask = (np.uint64(1) << np.uint64(k)) - np.uint64(1)
    v = x & mask
    c = np.zeros_like(v)
    while np.any(v): c += v & np.uint64(1); v >>= np.uint64(1)
    return 1 - 2 * (c & np.uint64(1)).astype(np.int64)

def hamiltonian(states, t, W, B):
    import scipy.sparse as sp
    n = len(B); rows, cols, vals = [], [], []
    occ = [((B >> np.uint64(k)) & np.uint64(1)).astype(bool) for k in range(len(states))]
    diag = sum(t[k] * occ[k] for k in range(len(states)))
    rows.append(np.arange(n)); cols.append(np.arange(n)); vals.append(diag.astype(float))
    for (p, q, r, s), v in W.items():        # a+_p a+_q a_s a_r
        x = B.copy(); ok = occ[r] & occ[s]; sg = np.ones(n)
        sg *= sign_before(x, r); x = x ^ (np.uint64(1) << np.uint64(r))
        ok &= True; sg *= sign_before(x, s); x = x ^ (np.uint64(1) << np.uint64(s))
        ok &= ((x >> np.uint64(q)) & np.uint64(1)) == 0; sg *= sign_before(x, q); x = x ^ (np.uint64(1) << np.uint64(q))
        ok &= ((x >> np.uint64(p)) & np.uint64(1)) == 0; sg *= sign_before(x, p); x = x ^ (np.uint64(1) << np.uint64(p))
        j = np.searchsorted(B, x); ok &= (j < n)
        j = np.where(ok, j, 0); ok &= B[j] == x
        rows.append(j[ok]); cols.append(np.arange(n)[ok]); vals.append(v * sg[ok])
    return sp.csr_matrix((np.concatenate(vals), (np.concatenate(rows), np.concatenate(cols))), shape=(n, n))
