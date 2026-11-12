"""Checks ../README.md: three-qubit circuits of CZ gates and Y rotations as networks of two-coordinate rotations
in a half-spin representation of SO(8).

1. Half-spin form. Eight anticommuting real symmetric 16 x 16 strings g_1..g_8, the chirality G = g_1 ... g_8, and
   S+ = {G = +1}. An antisymmetric A maps to s(A) = (1/4) sum A_ij g_i g_j on S+. The generator -iY_q/2 of a Y
   rotation maps to a rank-2 matrix, and the three planes, moved by the images of the CZ gates, give 12 planes that
   are the coordinate planes of one orthonormal basis l_0..l_7 along the edges of a cube graph. The images of the
   CZ gates are signed permutations of this basis.
2. Words. The circuit of [1] gives a word on the 8 edges of a cycle. The paired circuit gives a word on the 7 edges
   of a path through all 8 vertices, and as a word in adjacent transpositions of that path it has 28 letters and
   product the reversal, so it is reduced. The identity F+(x) = K C(x) is checked at random angles. All circuits
   of the same shape with a reduced word on a path are enumerated.
3. Fold of the circuit of [1]. Exact derivative matrix over Q(sqrt 2) at angles in (pi/4) Z: rank 27 and kappa != 0.
4. Compilation by least squares. The 10 targets of the SO(8) experiment of [1], sampled as in its code (seed 69214), and 100
   uniform targets, by least squares from random starts, for both circuits; curvature at the best points.
5. Exact compilation into the paired circuit along the proof of Theorem 2: lift to S+, nested word, moves.
"""
import itertools
from fractions import Fraction as Fr
import numpy as np
from scipy.linalg import expm, logm, schur
from scipy.optimize import least_squares
from scipy.stats import special_ortho_group

P1 = {"I": np.eye(2), "X": np.array([[0, 1], [1, 0]]), "Y": np.array([[0, -1j], [1j, 0]]), "Z": np.diag([1, -1])}


def word(s):
    M = np.eye(1)
    for c in s:
        M = np.kron(M, P1[c])
    return M.astype(complex)


def one(q, c):
    return "".join(c if k == q else "I" for k in range(3))


def cz(a, b):
    return np.diag([-1.0 if (i >> (2 - a)) & 1 and (i >> (2 - b)) & 1 else 1.0 for i in range(8)])


def circuit(pairs, last):
    """Y on each qubit, then for each pair (a, b): CZ_ab, Y_a, Y_b; the last CZ is followed only by Y on `last`."""
    g = [("r", q) for q in range(3)]
    for i, (a, b) in enumerate(pairs):
        g += [("f", (a, b))] + [("r", q) for q in ((a, b) if i < len(pairs) - 1 else (last,))]
    assert sum(t == "r" for t, _ in g) == 28
    return g


THEIRS = circuit([(0, 1), (1, 2)] * 6 + [(0, 1)], 0)       # the SO(8) brick wall of [1]
PAIRED = circuit([(0, 1)] + [(1, 2), (1, 2), (0, 1), (0, 1)] * 3, 1)
NAMES = [s for s in ("".join(t) for t in itertools.product("IXYZ", repeat=3)) if s.count("Y") % 2 == 1]
BAS = [word(s) for s in NAMES]
YQ = [np.real(-1j * word(one(q, "Y"))) for q in range(3)]  # -iY_q, real antisymmetric


def F(gates, x):
    U, k = np.eye(8), 0
    for t, v in gates:
        if t == "f":
            U = cz(*v) @ U
        else:
            U = expm(x[k] / 2 * YQ[v]) @ U
            k += 1
    return U


def Jac(gates, x):
    """Columns: coefficients in the odd-Y strings of H_k = V_k Y_q V_k^T, with dF = -(i/2) H_k F dx_k."""
    cols, V, k = [], np.eye(8), 27
    for t, v in gates[::-1]:
        if t == "f":
            V = V @ cz(*v)
        else:
            H = V @ word(one(v, "Y")) @ V.T
            cols.append([np.real(np.trace(B @ H)) / 8 for B in BAS])
            V = V @ expm(x[k] / 2 * YQ[v])
            k -= 1
    return np.array(cols[::-1]).T


# ---------------- 1. half-spin form ----------------
GN = ["YXZY", "ZZXI", "XIXX", "IXIZ", "XYYI", "IIZX", "XZIZ", "ZZZZ"]
GM = [np.real(word(s)) for s in GN]
for i, j in itertools.combinations(range(8), 2):
    assert np.allclose(GM[i] @ GM[j], -GM[j] @ GM[i])
assert all(np.allclose(g, g.T) and np.allclose(g @ g, np.eye(16)) for g in GM)
CH = np.linalg.multi_dot(GM)
w, Q = np.linalg.eigh(CH)
SP = Q[:, w > 0]


def splus(A):
    return SP.T @ (0.25 * sum(A[i, j] * GM[i] @ GM[j] for i in range(8) for j in range(8))) @ SP


def check_hom():
    rng = np.random.default_rng(1)
    A, Bm = (lambda m: m - m.T)(rng.normal(size=(8, 8))), (lambda m: m - m.T)(rng.normal(size=(8, 8)))
    assert np.allclose(splus(A @ Bm - Bm @ A), splus(A) @ splus(Bm) - splus(Bm) @ splus(A))


check_hom()
GEN = [splus(Y / 2) for Y in YQ]                           # image of the generator of a Y rotation
for g in GEN:
    assert np.allclose(np.sort(np.abs(np.linalg.eigvals(g).imag)), [0] * 6 + [1, 1])  # rank 2, rotation by t


def czlift(a, b):
    i, j = np.where(np.diag(cz(a, b)) < 0)[0]
    E = np.zeros((8, 8)); E[i, j], E[j, i] = np.pi, -np.pi
    assert np.allclose(expm(E), cz(a, b))
    return expm(splus(E))


K = {ab: czlift(*ab) for ab in [(0, 1), (1, 2), (0, 2)]}
planes = {}
frontier = [g @ g.T for g in GEN]                          # projector onto the plane of a rank-2 generator
key = lambda P: tuple(np.round(P, 8).ravel())
while frontier:
    P = frontier.pop()
    if key(P) in planes:
        continue
    planes[key(P)] = P
    frontier += [k.T @ P @ k for k in K.values()]
PL = list(planes.values())
lines = []
for P, R in itertools.combinations(PL, 2):
    if abs(np.trace(P @ R) - 1) < 1e-9:
        v = np.linalg.eigh(P @ R @ P)[1][:, -1]
        if not any(abs(abs(v @ l) - 1) < 1e-9 for l in lines):
            lines.append(v)
L = np.array(lines)
assert len(PL) == 12 and len(L) == 8 and np.allclose(L @ L.T, np.eye(8))
edge = lambda P: tuple(k for k in range(8) if L[k] @ P @ L[k] > 1 - 1e-9)
EDGES = sorted(edge(P) for P in PL)
assert all(len(e) == 2 for e in EDGES) and all(sum(v in e for e in EDGES) == 3 for v in range(8))
side = {0: 0}                                              # 3-regular and bipartite on 4 + 4 vertices: K_{4,4} minus
for _ in range(8):                                         # a perfect matching, which is the cube graph
    for a, b in EDGES:
        if (a in side) != (b in side):
            side[b if a in side else a] = 1 - side[a if a in side else b]
assert len(side) == 8 and all(side[a] != side[b] for a, b in EDGES) and sum(side.values()) == 4
for k in K.values():                                       # signed permutations of the basis
    M = L @ k @ L.T
    assert np.allclose(np.abs(M).sum(0), 1) and np.allclose(np.abs(M).sum(1), 1) and np.allclose(np.abs(M), np.round(np.abs(M)))
print(f"half-spin form: Y rotations act on S+ as rotations in coordinate planes of one basis; 12 planes = edges "
      f"of a cube graph {EDGES}; CZ images are signed permutations")


# ---------------- 2. words ----------------
def network(gates):
    """Word of edges (time order), the signs, and the fixed element: F+(x) = K * prod exp(sign x_k E_edge)."""
    Pm, out = np.eye(8), []
    for t, v in gates:
        if t == "f":
            Pm = K[v] @ Pm
        else:
            Bp = L @ np.linalg.inv(Pm) @ GEN[v] @ Pm @ L.T
            a, b = edge(L.T @ (Bp @ Bp.T) @ L)
            out.append(((a, b), int(np.sign(Bp[b, a]))))
    return out, Pm


def plus_of(gates, x):
    Pm, k = np.eye(8), 0
    for t, v in gates:
        if t == "f":
            Pm = K[v] @ Pm
        else:
            Pm = expm(x[k] * GEN[v]) @ Pm
            k += 1
    return Pm


def plane_rot(e, t):
    a, b = e
    M = np.eye(8); M[a, a] = M[b, b] = np.cos(t); M[b, a], M[a, b] = np.sin(t), -np.sin(t)
    return M


def is_path(es):
    deg = {v: sum(v in e for e in es) for v in range(8)}
    if len(es) != 7 or sorted(deg.values()) != [1, 1] + [2] * 6:
        return None
    seq = [min(v for v in range(8) if deg[v] == 1)]
    while len(seq) < 8:
        nxt = [w for e in es for w in e if seq[-1] in e and w != seq[-1] and w not in seq]
        if not nxt:
            return None
        seq.append(nxt[0])
    return seq


def reversal_product(word, seq):
    """Product of the letters of `word` as adjacent transpositions along `seq`, and its number of inversions."""
    pos = {v: i for i, v in enumerate(seq)}
    perm = list(range(8))
    for e in word:
        i, j = sorted((pos[e[0]], pos[e[1]]))
        assert j == i + 1
        perm[i], perm[j] = perm[j], perm[i]
    return perm, sum(perm[i] > perm[j] for i in range(8) for j in range(i + 1, 8))


rng = np.random.default_rng(2)
for name, g in (("circuit of [1]", THEIRS), ("paired circuit", PAIRED)):
    wd, Pm = network(g)
    x = rng.uniform(0, 4 * np.pi, 28)
    C = np.eye(8)
    for (e, s), t in zip(wd, x):
        C = plane_rot(e, s * t) @ C
    Kfix = L @ Pm @ L.T
    assert np.allclose(L @ plus_of(g, x) @ L.T, Kfix @ C)
    es = sorted(set(e for e, _ in wd))
    seq = is_path(es)
    if seq is None:
        assert len(es) == 8 and all(sum(v in e for e in es) == 2 for v in range(8))
        # connected 2-regular graph on 8 vertices: one cycle
        comp, todo = {0}, [0]
        while todo:
            v = todo.pop()
            for e in es:
                if v in e:
                    u = e[0] + e[1] - v
                    if u not in comp:
                        comp.add(u); todo.append(u)
        assert len(comp) == 8
        print(f"{name}: word of 28 rotations on the 8 edges of a cycle through all vertices")
    else:
        perm, inv = reversal_product([e for e, _ in wd], seq)
        assert inv == 28 and perm == list(range(8))[::-1]
        print(f"{name}: word of 28 rotations on the 7 edges of the path {seq}; as adjacent transpositions its "
              f"product is the reversal with {inv} inversions, so the word is reduced")

# all circuits of the same shape: three Y rotations, 13 bricks CZ_ab Y_a Y_b, one of the 29 rotations left out
E0 = [edge(g @ g.T) for g in GEN]                          # edge of Y_q before any CZ
VP = {ab: np.abs(np.round(L @ k @ L.T)).astype(int) for ab, k in K.items()}
adj = {v: [w for e in EDGES for w in e if v in e and w != v] for v in range(8)}
HP = set()                                                 # edge sets of the paths through all 8 vertices


def extend(p):
    if len(p) == 8:
        HP.add(frozenset(tuple(sorted(e)) for e in zip(p, p[1:])))
    for w in adj[p[-1]]:
        if w not in p:
            extend(p + [w])


for v0 in range(8):
    extend([v0])


def enumerate_reduced(pairs):
    hits = []
    def dfs(M, word, czs, skip):
        if not any(set(word) <= P for P in HP):
            return
        if len(czs) == 13:
            seq = is_path(sorted(set(word))) if len(word) == 28 else None
            if seq and reversal_product(word, seq)[1] == 28:
                hits.append((tuple(czs), skip))
            return
        for ab in pairs:
            M2 = VP[ab] @ M
            new = [tuple(sorted(int(np.argmax(M2[v])) for v in E0[q])) for q in ab]
            dfs(M2, word + new, czs + [ab], skip)
            if skip is None:
                for i, q in enumerate(ab):
                    dfs(M2, word + [new[1 - i]], czs + [ab], (len(czs) + 1, q))
    init = [E0[q] for q in range(3)]
    dfs(np.eye(8, dtype=int), init, [], None)
    for q in range(3):
        dfs(np.eye(8, dtype=int), init[:q] + init[q + 1:], [], (0, q))
    return hits


for g in (THEIRS, PAIRED):                                 # the fast edge rule agrees with network()
    M, wfast = np.eye(8, dtype=int), []
    for t, v in g:
        if t == "f":
            M = VP[v] @ M
        else:
            wfast.append(tuple(sorted(int(np.argmax(M[a])) for a in E0[v])))
    assert wfast == [e for e, _ in network(g)[0]]
NN = enumerate_reduced([(0, 1), (1, 2)])
ALL = enumerate_reduced([(0, 1), (1, 2), (0, 2)])
paired_pairs = tuple([(0, 1)] + [(1, 2), (1, 2), (0, 1), (0, 1)] * 3)
assert len(NN) == 8 and len(ALL) == 24 and (paired_pairs, (13, 0)) in NN
assert all(all(c[i] == c[i + 1] for i in range(0 if c[0] == c[1] else 1, 12, 2)) for c, _ in NN)
assert [h for h in NN if h[0][0] == (0, 1) and h[1][0] == 13] == [(paired_pairs, (13, 0))]
print(f"circuits of this shape with a reduced word on a path: {len(NN)} with CZ on (0, 1), (1, 2), {len(ALL)} with all "
      f"three pairs; the {len(NN)} take the bricks in pairs, and the paired circuit is the only one of them that starts "
      f"with CZ_01 and leaves out a rotation of the last brick, as the circuit of [1] does")


# ---------------- 3. exact fold of the circuit of [1] ----------------
class Q2:
    """a + b sqrt 2."""
    __slots__ = ("a", "b")

    def __init__(self, a=0, b=0):
        self.a, self.b = Fr(a), Fr(b)

    def __add__(s, o): return Q2(s.a + o.a, s.b + o.b)
    def __neg__(s): return Q2(-s.a, -s.b)
    def __sub__(s, o): return s + (-o)
    def __mul__(s, o): return Q2(s.a * o.a + 2 * s.b * o.b, s.a * o.b + s.b * o.a)
    def inv(s):
        n = s.a * s.a - 2 * s.b * s.b
        return Q2(s.a / n, -s.b / n)
    def zero(s): return s.a == 0 and s.b == 0
    def __float__(s): return float(s.a) + float(s.b) * 2 ** 0.5
    def __repr__(s): return f"{s.a} + {s.b} sqrt2"


HALF = Q2(0, Fr(1, 2))
COS = [Q2(1), HALF, Q2(0), -HALF, Q2(-1), -HALF, Q2(0), HALF]
SIN = [COS[(m - 2) % 8] for m in range(8)]
FULL = ["".join(t) for t in itertools.product("IXYZ", repeat=3)][1:]
FM = {s: word(s) for s in FULL}


def adj_data(gates):
    """Per gate, its conjugation action on strings: rotations give None (commutes) or (R, sign), CZ gives (R, sign)."""
    out = []
    for t, v in gates:
        dd = {}
        for q in NAMES:
            Qm = FM[q]
            if t == "r":
                Pm = FM[one(v, "Y")]
                if np.allclose(Pm @ Qm, Qm @ Pm):
                    dd[q] = None; continue
                PQ = Pm @ Qm
                r = next(r for r in FULL if abs(np.trace(FM[r] @ PQ)) > 1)
                dd[q] = (r, int(round(np.real(-1j * np.trace(FM[r] @ PQ) / 8))))  # R Q R^T = cos t Q + sign sin t R
            else:
                Cq = cz(*v) @ Qm @ cz(*v)
                r = next(r for r in FULL if abs(np.trace(FM[r] @ Cq)) > 1)
                dd[q] = (r, int(round(np.real(np.trace(FM[r] @ Cq) / 8))))
        out.append((t, v, dd))
    return out


def exact_columns(data, ms, j=None):
    rot = [i for i, (t, _, _) in enumerate(data) if t == "r"]
    mk = {g: ms[i] for i, g in enumerate(rot)}
    cols = []
    for i, g in enumerate(rot):
        if j is not None and j <= i:
            cols.append({}); continue
        vec = {one(data[g][1], "Y"): Q2(1)}
        for h in range(g + 1, len(data)):
            t, _, dd = data[h]; new = {}
            add = lambda s, c: new.__setitem__(s, new.get(s, Q2(0)) + c)
            for q, c in vec.items():
                if t == "f":
                    r, sg = dd[q]; add(r, c * Q2(sg))
                elif dd[q] is None:
                    if not (j is not None and h == rot[j]):
                        add(q, c)
                else:
                    r, sg = dd[q]; m = mk[h]
                    if j is not None and h == rot[j]:
                        add(q, -(SIN[m] * c)); add(r, COS[m] * c * Q2(sg))
                    else:
                        add(q, COS[m] * c); add(r, SIN[m] * c * Q2(sg))
            vec = new
        cols.append(vec)
    return [[c.get(s, Q2(0)) for c in cols] for s in NAMES]


def null_vector(A):
    A = [row[:] for row in A]; m, n = len(A), len(A[0]); piv, r = [], 0
    for c in range(n):
        p = next((i for i in range(r, m) if not A[i][c].zero()), None)
        if p is None:
            continue
        A[r], A[p] = A[p], A[r]; iv = A[r][c].inv(); A[r] = [x * iv for x in A[r]]
        for i in range(m):
            if i != r and not A[i][c].zero():
                f = A[i][c]; A[i] = [x - f * y for x, y in zip(A[i], A[r])]
        piv.append(c); r += 1
    free = [c for c in range(n) if c not in piv]
    assert len(free) == 1
    v = [Q2(0)] * n; v[free[0]] = Q2(1)
    for i, c in enumerate(piv):
        v[c] = -A[i][free[0]]
    return r, v


MS = [5, 7, 0, 0, 7, 6, 3, 1, 3, 0, 6, 0, 3, 5, 6, 6, 2, 7, 6, 7, 6, 3, 6, 0, 0, 5, 1, 2]  # x_k = MS[k] pi/4
data = adj_data(THEIRS)
Jx = exact_columns(data, MS)
assert np.allclose(np.array([[float(a) for a in row] for row in Jx]), Jac(THEIRS, np.array(MS) * np.pi / 4))
rk, v = null_vector(Jx)
rk2, u = null_vector([list(col) for col in zip(*Jx)])
assert rk == rk2 == 27
dv = [[Q2(0)] * 28 for _ in range(28)]
for j in range(28):
    if v[j].zero():
        continue
    dJ = exact_columns(data, MS, j)
    for a in range(28):
        for b in range(28):
            if not dJ[a][b].zero():
                dv[a][b] = dv[a][b] + v[j] * dJ[a][b]
kap = Q2(0)
for a in range(28):
    for b in range(28):
        kap = kap + u[a] * dv[a][b] * v[b]
assert not kap.zero()
nrm = lambda z: float(sum((t * t for t in z), Q2(0))) ** 0.5
s27 = np.linalg.svd(Jac(THEIRS, np.array(MS) * np.pi / 4), compute_uv=False)[-2]
x0f = np.array(MS) * np.pi / 4                             # the exact derivative agrees with finite differences
uf, vf = np.array([float(t) for t in u]) / nrm(u), np.array([float(t) for t in v]) / nrm(v)
kfd = uf @ ((Jac(THEIRS, x0f + 1e-6 * vf) - Jac(THEIRS, x0f - 1e-6 * vf)) / 2e-6) @ vf
assert abs(kfd - float(kap) / (nrm(u) * nrm(v) ** 2)) < 1e-8 and abs(s27 - 0.170) < 5e-4
print(f"fold of the circuit of [1] at x = (pi/4) {MS}: exact over Q(sqrt 2), rank J = 27, sigma_27 = {s27:.3f}, "
      f"u^T (d_v J) v = {kap} for the null vectors of the check, {float(kap) / (nrm(u) * nrm(v) ** 2):+.4f} for unit ones")


# ---------------- 4. compilation ----------------
def compile_(g, U, rng, starts):
    res = lambda x: (F(g, x) - U).ravel() / 4
    def jac(x):
        Fx, J = F(g, x), Jac(g, x)
        return np.array([np.real(-0.5j * sum(J[w, k] * BAS[w] for w in range(28)) @ Fx).ravel() / 4 for k in range(28)]).T
    best, bx = np.inf, None
    for s in range(starts):
        r = least_squares(res, rng.uniform(0, 4 * np.pi, 28), jac=jac, method="lm", xtol=1e-15, ftol=1e-15, gtol=1e-15, max_nfev=3000)
        if 2 * r.cost < best:
            best, bx = 2 * r.cost, r.x  # 2 cost = 1 - tr(U^T F)/8
        if best < 1e-20:
            return best, s + 1, bx
    return best, starts, bx


T = special_ortho_group.rvs(8, size=10, random_state=69214)
rng = np.random.default_rng(3)
out = [compile_(THEIRS, U, rng, 120) for U in T]
print("circuit of [1], the 10 targets of [1] (best loss, starts): " + ", ".join(f"{L:.1e} ({s})" for L, s, _ in out))
assert [i for i, (L, _, _) in enumerate(out) if L > 1e-12] == [1, 4, 5]
assert all(L < 1e-22 and s <= 20 for i, (L, s, _) in enumerate(out) if i not in (1, 4, 5))
for i in (1, 4, 5):
    x = out[i][2]
    Uu, S, Vt = np.linalg.svd(Jac(THEIRS, x))
    A = np.real(-2 * logm(T[i] @ F(THEIRS, x).T))  # T F^T = exp(-(i/2) sum a_w P_w), so -2 log = i sum a_w P_w
    a = np.array([np.real(np.trace(-1j * A @ B)) / 8 for B in BAS])
    u, v = Uu[:, -1], Vt[-1]
    h = 1e-5
    kap = u @ ((Jac(THEIRS, x + h * v) - Jac(THEIRS, x - h * v)) / (2 * h)) @ v
    print(f"  target {i}: at the best point sigma_min(J) = {S[-1]:.1e}, sigma_27 = {S[-2]:.3f}, "
          f"|kappa| = {abs(kap):.3f} for unit null vectors, |cos(residual, u)| = {abs(a @ u) / np.linalg.norm(a):.6f}")
    assert S[-1] < 1e-8 and S[-2] > 0.08 and 0.06 < abs(kap) < 0.1 and abs(a @ u) / np.linalg.norm(a) > 0.9999
out = [compile_(PAIRED, U, rng, 20) for U in T]
print("paired circuit, the 10 targets of [1]: " + ", ".join(f"{L:.1e} ({s})" for L, s, _ in out))
assert max(L for L, _, _ in out) < 1e-22 and max(s for _, s, _ in out) == 1
out = [compile_(PAIRED, special_ortho_group.rvs(8, random_state=rng), rng, 20) for _ in range(100)]
print(f"paired circuit, 100 uniform targets: largest loss {max(L for L, _, _ in out):.1e}, starts used at most "
      f"{max(s for _, s, _ in out)}")
assert max(L for L, _, _ in out) < 1e-21 and max(s for _, s, _ in out) == 1


# ---------------- 5. exact compilation into the paired circuit, along the proof of Theorem 2 ----------------
wdP, PmP = network(PAIRED)
path = is_path(sorted(set(e for e, _ in wdP)))
posP = {v: i for i, v in enumerate(path)}
LET = [min(posP[a], posP[b]) for (a, b), _ in wdP]                  # letter i = rotation in path positions i, i+1
ORI = [s * (1 if posP[a] < posP[b] else -1) for (a, b), s in wdP]
Pp = np.zeros((8, 8))
for i, v0 in enumerate(path):
    Pp[i, v0] = 1


def gr(i, t, n=8):
    return plane_rot((i, i + 1), t)[:n, :n]


def prod(word, ang):
    M = np.eye(8)
    for a, t in zip(word, ang):
        M = gr(a, t) @ M
    return M


def nested_angles(C):
    """Angles along the nested word, nested(n) = nested(n - 1) + [n-2, ..., 0], with prod = C."""
    word, ang = [], []
    for n in range(8, 1, -1):
        z, th = C[:, n - 1].copy(), []
        for i in range(n - 1):                                       # G_0(t_0) ... G_{n-2}(t_{n-2}) e_{n-1} = column
            t = np.arctan2(-z[i], z[i + 1])
            z = gr(i, t).T @ z
            th.append(t)
        Gs = np.eye(8)
        for i in range(n - 1):
            Gs = Gs @ gr(i, th[i])
        C = Gs.T @ C                                                 # fixes e_{n-1}; recurse on the rest
        word, ang = list(range(n - 2, -1, -1)) + word, th[::-1] + ang
    return word, ang


def three(M3, first):
    """M3 = R_f(c) R_g(b) R_f(a) on three coordinates, f the plane (0, 1) if first == 0, else (1, 2)."""
    if first == 1:
        Jr = np.eye(3)[::-1]                                        # conjugation swaps the planes, R12(t) -> R01(-t)
        a, b, c = three(Jr @ M3 @ Jr, 0)
        return -a, -b, -c
    b = np.arctan2(np.hypot(M3[0, 2], M3[1, 2]), M3[2, 2])
    c = np.arctan2(M3[0, 2], -M3[1, 2]) if np.hypot(M3[0, 2], M3[1, 2]) > 1e-9 else 0.0
    X = gr(1, b, 3).T @ gr(0, c, 3).T @ M3
    a = np.arctan2(X[1, 0], X[0, 0])
    assert np.allclose(gr(0, c, 3) @ gr(1, b, 3) @ gr(0, a, 3), M3, atol=1e-9)
    return a, b, c


def bring(W, A, k, s):
    """Rewrite W[k:] by moves so that W[k] == s, for s a left descent of the rest."""
    t = W[k]
    if t == s:
        return
    bring(W, A, k + 1, s)
    if abs(s - t) >= 2:                                             # commutation
        W[k], W[k + 1], A[k], A[k + 1] = W[k + 1], W[k], A[k + 1], A[k]
    else:                                                           # braid, solved on three coordinates
        bring(W, A, k + 2, t)
        i = min(W[k:k + 3])
        A[k:k + 3] = three(prod(W[k:k + 3], A[k:k + 3])[i:i + 3, i:i + 3], W[k + 1] - i)
        W[k:k + 3] = [W[k + 1], W[k], W[k + 1]]
    assert W[k] == s


def lift_plus(U):
    """An element of SO(S+) over U: exp of s(A) for a real logarithm A of U."""
    Tm, Z = schur(U, output="real")
    A, i, neg = np.zeros((8, 8)), 0, []
    while i < 8:
        if i < 7 and abs(Tm[i + 1, i]) > 1e-12:
            th = np.arctan2(Tm[i + 1, i], Tm[i, i]); A[i + 1, i], A[i, i + 1] = th, -th; i += 2
        else:
            if Tm[i, i] < 0:
                neg.append(i)
            i += 1
    for p, q in zip(neg[::2], neg[1::2]):
        A[q, p], A[p, q] = np.pi, -np.pi
    A = Z @ A @ Z.T
    assert np.allclose(expm(A), U, atol=1e-9)
    return expm(splus(A))


def compile_exact(U):
    Cp = Pp @ (L @ PmP @ L.T).T @ (L @ lift_plus(U) @ L.T) @ Pp.T   # F+ = K C, in path coordinates
    W, A = nested_angles(Cp)
    assert np.allclose(prod(W, A), Cp, atol=1e-9)
    for k in range(28):
        bring(W, A, k, LET[k])
    assert W == LET
    x = np.array([t * o for t, o in zip(A, ORI)])
    if np.abs(F(PAIRED, x) + U).max() < 1e-6:                      # the other lift: shift one angle by 2 pi
        x[0] += 2 * np.pi
    return np.abs(F(PAIRED, x) - U).max()


rng = np.random.default_rng(4)
special = [np.eye(8), -np.eye(8), np.diag([-1.0, -1] + [1] * 6), cz(0, 1) @ cz(1, 2)]
special += [F(PAIRED, rng.integers(0, 8, 28) * np.pi / 2) for _ in range(20)]
special += [F(THEIRS, np.array(MS) * np.pi / 4)]
errs = [compile_exact(U) for U in list(T) + special + [special_ortho_group.rvs(8, random_state=rng) for _ in range(200)]]
print(f"exact compilation into the paired circuit (lift, nested word, moves): {len(errs)} targets (the 10 of [1], "
      f"{len(special)} special ones, 200 uniform), largest max |F(x) - U| = {max(errs):.1e}")
assert max(errs) < 1e-12
print("all checks pass")
