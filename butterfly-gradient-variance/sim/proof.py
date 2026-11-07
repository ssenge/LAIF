"""Proof of Theorem 1 in exact rational arithmetic: readout n_0 n_{n/2}, phase of mode 0 in the first Rz layer,
k = n/4, n = 2^K >= 8. The recursion of butterfly.py gives s(K) = E[(dL/dphi_0)^2] = -sum_tau w_tau^T M_tau^{K-3} u_tau,
with fixed rational matrices M_tau (one middle bit), start vectors u_tau (top bit) and end vectors w_tau (bits 1, 0).
1. For every tau, G(M_tau) u_tau = 0 exactly, where G has the 20 simple rational roots printed below.
2. Hence s(K) satisfies the linear recurrence with characteristic polynomial G (degree 20).
3. The closed form 9^K/(18 n^6) + 4 9^K/(3 n^7) - 1/(16 n^3) - 3/(2 n^4) is a combination of lambda^K with lambda among
   the roots of G, so it satisfies the same recurrence; it equals s(K) exactly for 21 consecutive K, so for all K >= 3."""
import numpy as np, sys, itertools, time
from fractions import Fraction as Fr
sys.path.insert(0, ".")
import butterfly as dp
from butterfly import CORR

CORRq = np.array([[[[Fr(float(v)).limit_denominator(1 << 20) for v in row] for row in m2] for m2 in m3] for m3 in CORR], dtype=object)
assert all(abs(float(CORRq[idx]) - CORR[idx]) < 1e-15 for idx in np.ndindex(4, 4, 4, 4))
X8 = list(itertools.product((0, 1), repeat=8))
C1, C2 = (0, 1, 4, 5), (2, 3, 6, 7)
ROWS = dp.ROWS


def mom(a, b):
    if a % 2 or b % 2: return Fr(0)
    return Fr(dp.dfact(a - 1) * dp.dfact(b - 1), dp.dfact(a + b))


def gate_phase(pi, x, out, ab):
    groups = {}
    for s in range(8):
        groups.setdefault((pi[s], ROWS[s] if not ab else ""), []).append(s)
    g = Fr(1)
    for sl in groups.values():
        c = [0, 0, 0, 0]
        for s in sl: c[2 * out[s] + x[s]] += 1
        m = mom(c[0] + c[3], c[1] + c[2])
        if m == 0: return None
        g *= (-1) ** c[1] * m
    newpi = dp.canon([(pi[s], x[s]) for s in range(8)])
    cls = {}
    for s in range(8):
        key = (newpi[s], ROWS[s] if not ab else ""); cls[key] = cls.get(key, 0) + (1 if s >= 4 else -1)
    if any(cls.values()): return None
    return g, newpi


def hi_tensor(active):
    """12 high-bit tensors t[(c,e)](x4) for p_b = 0: chi_c * (1/4) sum_y (-1)^{x.y} u_e(y)."""
    act = (1, 1) if active else (1, 0)
    def u(e, y):
        a, b, c, d = y
        if e == 0: return int(a == d and b == c) * act[a] * act[b]
        if e == 1: return int(a == c and b == d) * act[a] * act[b]
        return int(a == b == c == d) * act[a]
    out = []
    for c in range(4):
        for e in range(3):
            t = {}
            for x in itertools.product((0, 1), repeat=4):
                if x[c] != 0: t[x] = Fr(0); continue
                t[x] = Fr(sum((-1) ** sum(xi * yi for xi, yi in zip(x, y)) * u(e, y) for y in itertools.product((0, 1), repeat=4)), 4)
            out.append(t)
    return out


def low_tensor():
    """12 joint tensors over (bit1, bit0) of 4 slots, including the signs of W2 and of chi on gamma, delta, and the weights."""
    H4 = [[Fr((-1) ** bin(q & z).count("1"), 2) for z in range(4)] for q in range(4)]
    out = []
    for c in range(4):
        for e in range(3):
            t = {}
            for z in itertools.product(range(4), repeat=4):          # z = 2*bit1 + bit0 per slot (input frame of W)
                if z[c] != 0: t[z] = Fr(0); continue
                val = Fr(0)
                for q in itertools.product(range(4), repeat=4):
                    a, b, cc, d = q
                    if e == 0: uq = Fr(int(a == d and b == cc))
                    elif e == 1: uq = Fr(-int(a == cc and b == d))
                    else: uq = CORRq[q]
                    if uq == 0: continue
                    val += H4[a][z[0]] * H4[b][z[1]] * H4[cc][z[2]] * H4[d][z[3]] * uq
                wt = Fr(1, 4) if e < 2 else Fr(1)
                t[z] = val * wt * (1 if c < 2 else -1)
            out.append(t)
    return out


def main(Kmax):
    t0 = time.time()
    i, j = 0, 1                # bits of rows at the top bit: i = 0, j = n/2 -> top bits 0, 1; all lower bits 0
    top = hi_tensor(False); mid = hi_tensor(True); low = low_tensor()
    nb = 12
    # top step
    pi0 = (0,) * 8
    U = {}
    out_top = [0 if ROWS[s] == "i" else 1 for s in range(8)]
    for x in X8:
        r = gate_phase(pi0, x, out_top, True)
        if r is None: continue
        g, npi = r
        a = np.array([top[t][tuple(x[s] for s in C1)] for t in range(nb)], dtype=object)
        b = np.array([top[t][tuple(x[s] for s in C2)] for t in range(nb)], dtype=object)
        U[npi] = U.get(npi, 0) + g * np.outer(a, b)
    # reachable states under mid steps
    zero = [0] * 8
    states = set(U); trans = {}
    frontier = set(U)
    while frontier:
        nf = set()
        for pi in frontier:
            lst = []
            for x in X8:
                r = gate_phase(pi, x, zero, True)
                if r is None: continue
                lst.append((x, r[0], r[1]))
                if r[1] not in states: nf.add(r[1])
            trans[pi] = lst
        states |= nf; frontier = nf
    states = sorted(states); S = len(states); sid = {s: t for t, s in enumerate(states)}
    print("reachable partitions:", S)
    # M[t1, t2] as S x S object matrices
    M = np.empty((nb, nb), dtype=object)
    for a in range(nb):
        for b in range(nb):
            M[a, b] = np.full((S, S), Fr(0), dtype=object)
    for pi, lst in trans.items():
        for x, g, npi in lst:
            ta = [mid[t][tuple(x[s] for s in C1)] for t in range(nb)]
            tb = [mid[t][tuple(x[s] for s in C2)] for t in range(nb)]
            for a in range(nb):
                if ta[a] == 0: continue
                for b in range(nb):
                    if tb[b] == 0: continue
                    M[a, b][sid[npi], sid[pi]] += g * ta[a] * tb[b]
    u = np.empty((nb, nb), dtype=object)
    for a in range(nb):
        for b in range(nb):
            u[a, b] = np.array([U[s][a, b] if s in U else Fr(0) for s in states], dtype=object)
    # final functional: bits 1 and 0
    w = np.empty((nb, nb), dtype=object)
    for a in range(nb):
        for b in range(nb):
            w[a, b] = np.full(S, Fr(0), dtype=object)
    for pi in states:
        acc = np.full((nb, nb), Fr(0), dtype=object)
        for x1 in X8:
            r1 = gate_phase(pi, x1, zero, True)
            if r1 is None: continue
            g1, p1 = r1
            for x0 in X8:
                r0 = gate_phase(p1, x0, zero, True)
                if r0 is None: continue
                g0 = r0[0]
                z1 = tuple(2 * x1[s] + x0[s] for s in C1); z2 = tuple(2 * x1[s] + x0[s] for s in C2)
                ta = np.array([low[t][z1] for t in range(nb)], dtype=object)
                tb = np.array([low[t][z2] for t in range(nb)], dtype=object)
                acc += (g1 * g0) * np.outer(ta, tb)
        for a in range(nb):
            for b in range(nb):
                w[a, b][sid[pi]] = acc[a, b]
    return M, u, w, states


if __name__ == "__main__":
    M, u, w, states = main(0)
    nb = 12
    roots_all = {}
    for a in range(nb):
        for b in range(nb):
            Mf = np.array(M[a, b], dtype=float)
            if not np.any(Mf) or not any(u[a, b]):
                continue
            ev = np.linalg.eigvals(Mf)
            assert np.max(np.abs(ev.imag)) < 1e-9
            cand = sorted({Fr(float(e.real)).limit_denominator(4096) for e in ev})
            # exact annihilation of u by prod (M - lambda), adding multiplicity until zero
            v = u[a, b].copy(); used = {}
            for lam in cand:
                v = M[a, b].dot(v) - lam * v
                used[lam] = 1
            extra = 0
            while any(v):
                extra += 1
                assert extra < 6, ("not annihilated", a, b)
                for lam in cand:
                    v2 = M[a, b].dot(v) - lam * v
                    if not any(v2):
                        used[lam] += 1; v = v2; break
                else:
                    # try each root once more in turn
                    lam = cand[extra % len(cand)]; v = M[a, b].dot(v) - lam * v; used[lam] += 1
            for lam, mlt in used.items():
                roots_all[lam] = max(roots_all.get(lam, 0), mlt)
    print("roots (value: multiplicity):", {str(k): v for k, v in sorted(roots_all.items(), reverse=True)})
    deg = sum(roots_all.values()); print("degree of G:", deg)
    # exact s(K) for K = 3 .. 3 + deg, compare with closed form
    vec = {(a, b): u[a, b].copy() for a in range(nb) for b in range(nb)}
    ok = True
    for K in range(3, 3 + deg + 1):
        s = -sum(w[a, b].dot(vec[(a, b)]) for a in range(nb) for b in range(nb))
        n = 2 ** K
        f = Fr(9 ** K, 18 * n ** 6) + Fr(4 * 9 ** K, 3 * n ** 7) - Fr(1, 16 * n ** 3) - Fr(3, 2 * n ** 4)
        ok &= (s == f)
        vec = {key: M[key].dot(v) for key, v in vec.items()}
    assert ok
    print("closed form equals s(K) exactly for K = 3 ..", 3 + deg)
    for lam in (Fr(9, 64), Fr(1, 8), Fr(9, 128), Fr(1, 16)):
        assert lam in roots_all
    print("the four roots of the closed form are roots of G, so both sides satisfy the same recurrence: formula holds for all K >= 3")
