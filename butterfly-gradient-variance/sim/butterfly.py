"""Gradient variance of the unitary butterfly of [1] for the readout n_i n_j and a phase of its first Rz layer.

Model ([1], Sections II and III C): k particles in k/2 blocks (|1100> + |0011>)/sqrt(2) on the modes 0, ..., 2k - 1,
spread by the sign transform H_ab = (-1)^{a.b} / sqrt(n), then the trainable butterfly W = F_K R_K ... F_1 R_1 with all
rotation angles and phases uniform on [0, 2 pi). L = <n_i n_j>, and dL/dphi_p is taken at the phase of mode p in R_1.

Part 1 (sampling): samples of dL/dphi_p from the rows of W.
Part 2 (recursion): E[(dL/dphi_p)^2] exactly, by a backward recursion over the bits of the mode labels. The state is the
partition of the 8 index slots of the fourth-order moment by equality on the bits processed so far; the gates of one layer
are independent, so their moments depend only on which slots share a gate, and the phase averages only on which slots
carry equal labels. The input tensor is a sum of products over bits. Requires 2k to be a power of 2.
Part 3: the value for the uniform (rotation-invariant) unitary from [1, Theorem 11], with the norm of B in closed form.
"""
import itertools
import numpy as np
from math import prod
from itertools import product

# ---- block 4-point function correction -------------------------------------------------------------
def mode_ops(m):
    """annihilators on m modes in the standard qubit encoding; basis index bit q = occupation of mode q."""
    dim = 2 ** m
    ops = []
    for q in range(m):
        A = np.zeros((dim, dim))
        for s in range(dim):
            if s >> q & 1:
                sign = (-1) ** bin(s & ((1 << q) - 1)).count("1")
                A[s ^ (1 << q), s] = sign
        ops.append(A)
    return ops

cs = mode_ops(4)
blk = np.zeros(16); blk[0b0011] = blk[0b1100] = 1 / np.sqrt(2)   # modes 0,1 occupied or modes 2,3
T = np.zeros((4,) * 4)
for a, b, c, d in product(range(4), repeat=4):
    T[a, b, c, d] = blk @ cs[a].T @ cs[b].T @ cs[c] @ cs[d] @ blk
D1 = np.array([[blk @ cs[a].T @ cs[d] @ blk for d in range(4)] for a in range(4)])
assert np.allclose(D1, np.eye(4) / 2)
PAIR = np.einsum("ad,bc->abcd", D1, D1) - np.einsum("ac,bd->abcd", D1, D1)
CORR = T - PAIR             # block correction to the pairing formula of the 1-RDM


def sign_transform(X):
    """X @ H along the last axis, H_ab = (-1)^{a.b}/sqrt(n)."""
    X = X.copy(); n = X.shape[-1]; h = 1
    while h < n:
        X = X.reshape(X.shape[:-1] + (n // (2 * h), 2, h))
        a, b = X[..., 0, :].copy(), X[..., 1, :].copy()
        X[..., 0, :], X[..., 1, :] = a + b, a - b
        X = X.reshape(X.shape[:-3] + (n,)); h *= 2
    return X / np.sqrt(n)


def F(u, v, y, x, k):
    """<Psi_in| c^dag(u) c^dag(v) c(y) c(x) |Psi_in>, c^dag(u) = sum u_m c^dag_m, c(x) = sum conj(x_m) c_m."""
    act = slice(0, 2 * k)
    dot = lambda s, t: 0.5 * np.sum(s[:, act] * np.conj(t[:, act]), axis=1)
    out = dot(u, x) * dot(v, y) - dot(u, y) * dot(v, x)
    r = lambda z: z[:, act].reshape(-1, k // 2, 4)
    out = out + np.einsum("sga,sgb,sgc,sgd,abcd->s", r(u), r(v), np.conj(r(y)), np.conj(r(x)), CORR)
    return out


def rows_butterfly(n, idx, S, rng):
    """W_rest^dag e_i for i in idx; W_rest = F_K R_K ... F_2 R_2 F_1. Returns list of (S, n) arrays (common W)."""
    K = n.bit_length() - 1
    th = rng.uniform(0, 2 * np.pi, (S, K, n // 2))
    ph = rng.uniform(0, 2 * np.pi, (S, K, n))
    out = []
    for i in idx:
        v = np.zeros((S, n), complex); v[:, i] = 1
        for l in range(K - 1, -1, -1):          # apply F_{l+1}^dag then R_{l+1}^dag (no R for l = 0)
            s = 2 ** l
            X = v.reshape(S, n // (2 * s), 2, s)
            c = np.cos(th[:, l]).reshape(S, n // (2 * s), s); sn = np.sin(th[:, l]).reshape(S, n // (2 * s), s)
            a, b = X[:, :, 0, :].copy(), X[:, :, 1, :].copy()
            # F block [[c, -s], [s, c]] on (q, q+s); F^dag = [[c, s], [-s, c]]
            X[:, :, 0, :], X[:, :, 1, :] = c * a + sn * b, -sn * a + c * b
            v = X.reshape(S, n)
            if l > 0:
                v = v * np.exp(1j * ph[:, l])
        out.append(v)
    return out


def rows_uniform(n, S, rng):
    Z = rng.normal(size=(S, n, 2)) + 1j * rng.normal(size=(S, n, 2))
    Q, _ = np.linalg.qr(Z)
    return Q[:, :, 0], Q[:, :, 1]


def grad(a, b, p, k, rng):
    """dL/dphi_p with uniform input phases R_1."""
    S, n = a.shape
    Pa = np.zeros_like(a); Pa[:, p] = a[:, p]
    Pb = np.zeros_like(b); Pb[:, p] = b[:, p]
    ph = np.exp(-1j * rng.uniform(0, 2 * np.pi, (S, n)))      # R_1^dag
    tr = lambda z: sign_transform(z * ph)                               # H R_1^dag z
    a_, b_, Pa_, Pb_ = map(tr, (a, b, Pa, Pb))
    return -2 * np.imag(F(Pa_, b_, b_, a_, k) + F(a_, Pb_, b_, a_, k))


# ---------------- Part 2: recursion ----------------

ROW = None  # set per call
BRA = [0, 1, 2, 3]; KET = [4, 5, 6, 7]
# copy 1: alpha->0 (row i), beta->1 (row j), gamma->4 (row j), delta->5 (row i); copy 2 likewise 2,3,6,7
C1 = [0, 1, 4, 5]; C2 = [2, 3, 6, 7]
ROWS = ["i", "j", "i", "j", "j", "i", "j", "i"]


def dfact(m):
    return prod(range(m, 0, -2)) if m > 0 else 1


def mom(a, b):
    if a % 2 or b % 2:
        return 0.0
    return dfact(a - 1) * dfact(b - 1) / dfact(a + b)


def canon(lab):
    m = {}; out = []
    for v in lab:
        if v not in m:
            m[v] = len(m)
        out.append(m[v])
    return tuple(out)


h = np.array([[1, 1], [1, -1]]) / np.sqrt(2)


def sign4(u):
    """u indexed by Psi-frame bits y (4 slots, shape (2,2,2,2)) -> t(x) = sum_y prod h(y_s, x_s) u(y)."""
    return np.einsum("abcd,aw,bx,cy,dz->wxyz", u, h, h, h, h)


def bit_tensors(b, p_b, r, R_svd):
    """list of 4-slot tensors t[tau] (shape (2,2,2,2)) for bit b >= 2; tau = (c, e), e in W1, W2, C_0..C_{R-1}."""
    act = np.array([1.0, 1.0]) if b < r else np.array([1.0, 0.0])
    I = np.eye(2)
    W1 = np.einsum("ad,bc,a,b->abcd", I, I, act, act)
    W2 = np.einsum("ac,bd,a,b->abcd", I, I, act, act)   # sign carried by the low bits
    Cc = np.zeros((2,) * 4); Cc[0, 0, 0, 0] = act[0]; Cc[1, 1, 1, 1] = act[1]
    us = [W1, W2] + [Cc] * R_svd
    out = []
    for c in range(4):
        sign = 1 if c < 2 else -1
        chi = np.zeros((2,) * 4)
        for x in np.ndindex(2, 2, 2, 2):
            chi[x] = 1.0 if x[c] == p_b else 0.0
        for u in us:
            out.append(chi * sign4(u))
    return out


def low_tensors(p0, p1):
    """bits 1 and 0 jointly: returns per-tau (t_bit1, t_bit0) lists, with C split into products across the two bits by a singular value decomposition."""
    I = np.eye(4)
    W1 = np.einsum("ad,bc->abcd", I, I); W2 = -np.einsum("ac,bd->abcd", I, I)
    # 4-slot tensors over local index q = 2*bit1 + bit0 -> reshape to (bit1 x4, bit0 x4)
    def split(u):
        u = u.reshape((2, 2) * 4)                      # axes: s0b1, s0b0, s1b1, s1b0, ...
        u = u.transpose(0, 2, 4, 6, 1, 3, 5, 7)          # bit1 of 4 slots, bit0 of 4 slots
        return u
    def sign_both(u):
        u = np.einsum("abcdefgh,aw,bx,cy,dz->wxyzefgh", u, h, h, h, h)
        return np.einsum("wxyzefgh,eA,fB,gC,hD->wxyzABCD", u, h, h, h, h)
    cw = sign_both(split(CORR)).reshape(16, 16)
    U, S, Vt = np.linalg.svd(cw)
    R = int(np.sum(S > 1e-12 * S[0]))
    pieces = [(sign_both(split(W1)), None), (sign_both(split(W2)), None)]
    out = []
    for c in range(4):
        sign = 1 if c < 2 else -1
        def chi(bitval):
            t = np.zeros((2,) * 4)
            for x in np.ndindex(2, 2, 2, 2):
                t[x] = 1.0 if x[c] == bitval else 0.0
            return t
        for full, _ in pieces:
            # W1, W2 are products of per-bit deltas (rank 1 across the bit split): compute factors directly
            M = full.reshape(16, 16)
            u_, s_, v_ = np.linalg.svd(M)
            assert s_[1] < 1e-10 * s_[0]
            out.append((sign * chi(p1) * (u_[:, 0] * s_[0]).reshape((2,) * 4), chi(p0) * v_[0].reshape((2,) * 4)))
        for q in range(R):
            out.append((sign * chi(p1) * (U[:, q] * S[q]).reshape((2,) * 4), chi(p0) * Vt[q].reshape((2,) * 4)))
    return out, R


def run(K, r, i, j, p):
    n = 2 ** K
    low, R = low_tensors(p & 1, p >> 1 & 1)
    B = 4 * (2 + R)
    rowbit = lambda s, b: (i >> b & 1) if ROWS[s] == "i" else (j >> b & 1)
    def agree_below(b):
        return (i ^ j) & ((1 << b) - 1) == 0
    V = {tuple([0] * 8): np.ones((B, B))}
    X = list(np.ndindex(*(2,) * 8))
    for b in range(K - 1, -1, -1):
        if b >= 2:
            ts = bit_tensors(b, p >> b & 1, r, R)
        elif b == 1:
            ts = [t1 for t1, _ in low]
        else:
            ts = [t0 for _, t0 in low]
        T = np.array(ts)                              # (B, 2,2,2,2)
        ab = agree_below(b)
        out = [rowbit(s, b) for s in range(8)]
        newV = {}
        for pi, val in V.items():
            for x in X:
                # gate groups: same pi class and (same row or agree below)
                groups = {}
                for s in range(8):
                    key = (pi[s], ROWS[s] if not ab else "")
                    groups.setdefault(key, []).append(s)
                g = 1.0
                for sl in groups.values():
                    n00 = n01 = n10 = n11 = 0
                    for s in sl:
                        o, inn = out[s], x[s]
                        if o == 0 and inn == 0: n00 += 1
                        elif o == 0: n01 += 1
                        elif inn == 0: n10 += 1
                        else: n11 += 1
                    mm = mom(n00 + n11, n01 + n10)
                    if mm == 0:
                        g = 0.0; break
                    g *= (-1) ** n01 * mm
                if g == 0.0:
                    continue
                newpi = canon([(pi[s], x[s]) for s in range(8)])
                # phase balance on current index: newpi refined by row type if rows disagree below
                cls = {}
                for s in range(8):
                    key = (newpi[s], ROWS[s] if not ab else "")
                    cls[key] = cls.get(key, 0) + (1 if s >= 4 else -1)
                if any(v != 0 for v in cls.values()):
                    continue
                t1 = T[:, x[0], x[1], x[4], x[5]]
                t2 = T[:, x[2], x[3], x[6], x[7]]
                contrib = g * (t1[:, None] * val * t2[None, :])
                if newpi in newV:
                    newV[newpi] += contrib
                else:
                    newV[newpi] = contrib
        V = newV
    tot = sum(v for v in V.values())
    # overall: i^2 = -1 from the two D factors; rho = Pi/2 gives 1/4 for the pairing terms W1, W2
    w = np.array(([0.25, 0.25] + [1.0] * R) * 4)
    return -np.sum(w[:, None] * tot * w[None, :]), len(V)




# ---------------- Part 3: value for the uniform unitary ----------------
def uniform_value(n, k):
    """(4 |B|^2 + 2 |Gamma(B)|^2) / (n^2 (n^2 - 1)) of [1, Theorem 11]; |Gamma(B)|^2 = (k-1)^2 (k/n)(1 - 2k/n) [1, Claim 2],
    |B|^2 = (k(k+2)n/2 - k^3 + 3k^2/2 - 3k) / n^2 (checked against the definition below)."""
    B2 = (k * (k + 2) * n / 2 - k ** 3 + 1.5 * k ** 2 - 3 * k) / n ** 2
    G2 = (k - 1) ** 2 * (k / n) * (1 - 2 * k / n)
    return (4 * B2 + 2 * G2) / (n ** 2 * (n ** 2 - 1))


def B2_direct(n, k, p):
    """|B|^2 = |[G, rho_2]|^2 = 2 sum over pairs x containing p, y not containing p of |rho_2(x, y)|^2."""
    H = np.array([[(-1) ** bin(a & b).count("1") for b in range(n)] for a in range(n)]) / np.sqrt(n)
    Q = H[:, :2 * k] @ H[:2 * k, :] / 2
    Hb = H[:2 * k].reshape(k // 2, 4, n)
    E = np.einsum("s,qt->qts", Q[p], Q) - np.einsum("t,qs->qts", Q[p], Q)
    E += np.einsum("ga,gbq,gct,gds,abcd->qts", Hb[:, :, p], Hb, Hb, Hb, CORR, optimize=True)
    tri = np.tril(np.ones((n, n), bool), -1); tri[p, :] = tri[:, p] = False
    keep = np.arange(n) != p
    return 2 * np.sum((E[keep] ** 2)[:, tri])


def sample_var(n, k, i, j, p, rows, reps, rng):
    s1 = s2 = N = 0
    for _ in range(reps):
        a, b = rows()
        g = grad(a, b, p, k, rng) ** 2
        s1 += g.sum(); s2 += (g * g).sum(); N += g.size
    m = s1 / N
    return m, np.sqrt((s2 / N - m * m) / N)


if __name__ == "__main__":
    rng = np.random.default_rng(2024)
    print("1. recursion against sampling (mean of (dL/dphi_p)^2, 10^6 samples), and the uniform value against sampling")
    for K, r, j in ((3, 2, 1), (3, 2, 4), (5, 4, 16), (6, 5, 32), (6, 5, 1)):
        n, k = 2 ** K, 2 ** (r - 1)
        v, _ = run(K, r, 0, j, 0)
        m, e = sample_var(n, k, 0, j, 0, lambda: rows_butterfly(n, (0, j), 25000, rng), 40, rng)
        mu, eu = sample_var(n, k, 0, j, 0, lambda: rows_uniform(n, 25000, rng), 40, rng)
        assert abs(v - m) < 4 * e and abs(uniform_value(n, k) - mu) < 4 * eu
        print(f"   n={n:3d} k={k:2d} (i,j)=(0,{j:2d}) p=0: recursion {v:.4e}, sampled {m:.4e} +- {e:.0e};"
              f" uniform {uniform_value(n, k):.4e}, sampled {mu:.4e} +- {eu:.0e}")
    for n, k, p in ((16, 4, 3), (32, 8, 5), (64, 16, 9), (128, 32, 77)):
        assert abs(B2_direct(n, k, p) / ((k * (k + 2) * n / 2 - k ** 3 + 1.5 * k ** 2 - 3 * k) / n ** 2) - 1) < 1e-12
    print("2. closed form of |B|^2 equals its definition at (n, k) = (16, 4), (32, 8), (64, 16), (128, 32)")
    print("3. ratio of the butterfly value to the uniform value, i = 0, p = 0")
    for kind in ("k=2", "k=n/8", "k=n/4"):
        for K in (6, 9, 12, 15):
            n = 2 ** K
            r = {"k=2": 2, "k=n/8": K - 2, "k=n/4": K - 1}[kind]; k = 2 ** (r - 1)
            u = uniform_value(n, k)
            vals = [run(K, r, 0, j, 0)[0] / u for j in (1, n // 4, n // 2, n // 2 + 1)]
            print(f"   {kind:6s} n={n:6d}: j=1 {vals[0]:.4f}, j=n/4 {vals[1]:.4f}, j=n/2 {vals[2]:.6f}, j=n/2+1 {vals[3]:.4f}")
    n = 64
    same = {round(run(6, 5, i, i ^ 32, p)[0], 18) for i in (0, 5) for p in range(0, 64, 7)}
    assert len(same) == 1
    print("4. n = 64, k = 16, readout (i, i + 32): the same value for i in {0, 5} and p in {0, 7, ..., 63}")
