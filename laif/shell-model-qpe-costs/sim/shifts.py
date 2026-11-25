"""Symmetry shifts for the shell-model LCU of 2607.21563. H' = H - sum_k c_k (S_k - s_k) with operators S_k that take
the value s_k on the target sector (particle numbers, J = 0, T = 0, M = 0). The LCU 1-norm in the encoding of
2607.21563 is lambda = sum_p |t_p| / 2 + sum over all ordered (pq),(rs) of |W_pqrs|; the best c is a linear program.
usage: python shifts.py snt A Z N"""
import sys, numpy as np, scipy.sparse.linalg as sla
from scipy.optimize import linprog
from shell import build, basis, hamiltonian

def product(n, A, B):
    """one-body diagonal part and two-body dict of (sum A_pq a+p a_q)(sum B_rs a+r a_s); A, B dense n x n"""
    one = np.zeros((n, n)); two = {}
    for p, q in zip(*np.nonzero(A)):
        for r, s in zip(*np.nonzero(B)):
            v = A[p, q] * B[r, s]
            if q == r: one[p, s] += v
            P, Q, R, S = p, r, q, s                    # + a+_p a+_r a_s a_q
            if P == Q or R == S: continue
            sg = 1
            if P > Q: P, Q, sg = Q, P, -sg
            if R > S: R, S, sg = S, R, -sg
            two[(P, Q, R, S)] = two.get((P, Q, R, S), 0) + sg * v
    assert np.allclose(one, np.diag(np.diag(one)))
    return np.diag(one), {k: v for k, v in two.items() if abs(v) > 1e-12}

def operators(states, orbs):
    n = len(states); jz = np.diag([m / 2 for (o, m) in states])
    jp = np.zeros((n, n)); tp = np.zeros((n, n))
    idx = {s: k for k, s in enumerate(states)}
    for k, (o, m) in enumerate(states):
        j = orbs[o][2] / 2; mm = m / 2
        if (o, m + 2) in idx: jp[idx[(o, m + 2)], k] = np.sqrt(j * (j + 1) - mm * (mm + 1))
    for k, (o, m) in enumerate(states):            # T+ : neutron -> proton, same (n, l, j, m)
        if orbs[o][3] == 1:
            twin = [i for i in orbs if orbs[i][:3] == orbs[o][:3] and orbs[i][3] == -1][0]
            tp[idx[(twin, m)], k] = 1.0
    tz = np.diag([-orbs[o][3] / 2 for (o, m) in states])     # protons +1/2 (only T_z^2 enters)
    npr = np.diag([1.0 if orbs[o][3] == -1 else 0.0 for (o, m) in states]); nne = np.eye(n) - npr
    def sq(A, B):
        return product(n, A, B)
    ops = {}
    J2a = sq(jz, jz); J2b = sq(jp, jp.T); J2c = sq(jp.T, jp)
    ops["J2"] = (J2a[0] + (J2b[0] + J2c[0]) / 2, merge([J2a[1], J2b[1], J2c[1]], [1, .5, .5]))
    T2a = sq(tz, tz); T2b = sq(tp, tp.T); T2c = sq(tp.T, tp)
    ops["T2"] = (T2a[0] + (T2b[0] + T2c[0]) / 2, merge([T2a[1], T2b[1], T2c[1]], [1, .5, .5]))
    ops["Np2"] = sq(npr, npr); ops["Nn2"] = sq(nne, nne); ops["NpNn"] = sq(npr, nne)
    ops["Jz2"] = sq(jz, jz)
    ops["Np"] = (np.diag(npr).copy(), {}); ops["Nn"] = (np.diag(nne).copy(), {}); ops["Jz"] = (np.diag(jz).copy(), {})
    return ops

def merge(ds, ws):
    out = {}
    for d, w in zip(ds, ws):
        for k, v in d.items(): out[k] = out.get(k, 0) + w * v
    return {k: v for k, v in out.items() if abs(v) > 1e-12}

def l1_fit(b, A, w=None):
    """min_c sum w |b - A c| as a sparse linear program (variables c free, u >= |b - A c|)"""
    import scipy.sparse as sp
    m, nc = A.shape; w = np.ones(m) if w is None else w
    As = sp.csr_matrix(A); I = sp.identity(m, format="csr")
    Aub = sp.vstack([sp.hstack([-As, -I]), sp.hstack([As, -I])], format="csr")
    res = linprog(np.concatenate([np.zeros(nc), w]), A_ub=Aub, b_ub=np.concatenate([-b, b]),
                  bounds=[(None, None)] * nc + [(0, None)] * m, method="highs")
    assert res.status == 0, res.message
    return res.x[:nc]

def lam(t, W):
    return np.abs(t).sum() / 2 + sum(abs(v) for v in W.values())

def optimize(t, W, ops, names):
    keys = sorted(set(W) | set().union(*[set(ops[k][1]) for k in names]))
    # residual r = b - A c over one-body (weight 1/2) and two-body (weight 1) coefficients; minimize sum w |r|
    b = np.concatenate([t, [W.get(k, 0) for k in keys]])
    A = np.column_stack([np.concatenate([ops[k][0], [ops[k][1].get(q, 0) for q in keys]]) for k in names])
    w = np.concatenate([np.full(len(t), .5), np.ones(len(keys))])
    c = l1_fit(b, A, w)
    t2 = t - sum(ci * ops[k][0] for ci, k in zip(c, names))
    W2 = {}
    for q in keys:
        v = W.get(q, 0) - sum(ci * ops[k][1].get(q, 0) for ci, k in zip(c, names))
        if abs(v) > 1e-12: W2[q] = v
    return dict(zip(names, c)), t2, W2

if __name__ == "__main__":
    path, A, Z, N = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4])
    states, orbs, t, W = build(path, A)
    ops = operators(states, orbs)
    B = basis(states, orbs, Z, N, 0)
    H = hamiltonian(states, t, W, B)
    vals, vecs = sla.eigsh(H, k=1, which="SA"); E0, g = vals[0], vecs[:, 0]
    target = {"J2": 0, "T2": abs(Z - N) / 2 * (abs(Z - N) / 2 + 1), "Np2": Z * Z, "Nn2": N * N, "NpNn": Z * N, "Jz2": 0, "Np": Z, "Nn": N, "Jz": 0}
    for k, (o1, o2) in ops.items():                         # each shift operator has its target value on the ground state
        Sk = hamiltonian(states, o1, o2, B); ev = g @ (Sk @ g)
        print("%-5s <g|S|g> = %.6f (target %g)" % (k, ev, target[k])); assert abs(ev - target[k]) < 1e-6
    print("lambda baseline %.2f  (one-body %.2f, two-body %.2f, terms %d)" % (lam(t, W), np.abs(t).sum() / 2, lam(0 * t, W), len(W)))
    for names in (["Np", "Nn"], ["Np", "Nn", "Np2", "Nn2", "NpNn"], ["Np", "Nn", "Np2", "Nn2", "NpNn", "Jz", "Jz2"],
                  ["Np", "Nn", "Np2", "Nn2", "NpNn", "Jz", "Jz2", "J2"], ["Np", "Nn", "Np2", "Nn2", "NpNn", "Jz", "Jz2", "J2", "T2"]):
        c, t2, W2 = optimize(t, W, ops, names)
        H2 = hamiltonian(states, t2, W2, B); const = sum(c[k] * target[k] for k in names)
        e2 = sla.eigsh(H2, k=1, which="SA")[0][0]
        assert abs(e2 + const - E0) < 1e-6, (e2 + const, E0)      # spectrum shifts by the constant on the target sector
        print("%-45s lambda %.2f  ratio %.3f  terms %d" % ("+".join(names), lam(t2, W2), lam(t, W) / lam(t2, W2), len(W2)))
