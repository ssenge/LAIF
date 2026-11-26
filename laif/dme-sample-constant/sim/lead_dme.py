"""Leading-order optimal one-copy step for sample-based Hamiltonian simulation (target e^{-i t [sigma, .]}).
A step is Lambda_D = Tr_P + D G + D^2 E with G(rho (x) X) = -i[X, rho] forced; per-step error D^2 e_sigma + O(D^3),
e_sigma = (1/2)||E_sigma - ad^2/2||_diamond, ad = -i[sigma, .]. Choi C(D) = C0 + D C1 + D^2 C2 >= 0 for small D needs
K C1 K >= 0 on K = ker C0 and Q (C2 - C1 C0^+ C1) Q >= 0 on Q = ker C0 cap ker(K C1 K); Tr_out C2 = 0.
E is WLOG covariant under U (x) U: C2 in the span of partially transposed permutations of [sys_in, prog, out]
(transpose on the two inputs). Minimax over sigma by a cutting plane (local search over density matrices).
Also prints the leading constant of DME itself (E = sigma tr(rho) - rho). usage: lead_dme.py d rounds"""
import os, sys, itertools
for _v in ("OMP_NUM_THREADS", "OPENBLAS_NUM_THREADS", "MKL_NUM_THREADS", "VECLIB_MAXIMUM_THREADS", "NUMEXPR_NUM_THREADS"):
    os.environ[_v] = "1"
import numpy as np, cvxpy as cp
from scipy.optimize import minimize

def ptrace(A, dims, axis):
    k = len(dims); A = A.reshape(dims + dims)
    return np.trace(A, axis1=axis, axis2=k + axis).reshape(int(np.prod(dims) / dims[axis]), -1)

def choi_map(f, d):
    """Choi (input S (x) P first, output last) of |s><s'| (x) |p><p'| -> f(R, X) with R = |s><s'|, X = |p><p'|"""
    D = d * d * d; C = np.zeros((D, D), complex)
    for s in range(d):
        for s2 in range(d):
            for p in range(d):
                for p2 in range(d):
                    R = np.zeros((d, d)); R[s, s2] = 1; X = np.zeros((d, d)); X[p, p2] = 1
                    a = s * d + p; b = s2 * d + p2
                    C[a * d:(a + 1) * d, b * d:(b + 1) * d] = f(R, X)
    return C

def basis(d):
    m = 3; ops = []
    for perm in itertools.permutations(range(m)):
        A = np.zeros((d,) * (2 * m))
        for idx in itertools.product(range(d), repeat=m):
            A[tuple(idx[perm[k]] for k in range(m)) + idx] = 1
        for f in (0, 1): A = np.swapaxes(A, f, m + f)
        ops.append(A.reshape(d ** m, d ** m))
    M = np.array([x.reshape(-1) for x in ops]); _, sv, vh = np.linalg.svd(M, full_matrices=False)
    span = [vh[k].reshape(d ** m, d ** m) for k in range(int((sv > 1e-9 * sv[0]).sum()))]
    out = []
    for A in span:
        for H in ((A + A.conj().T) / 2, (A - A.conj().T) / 2j):
            if np.abs(H).max() > 1e-12: out.append(H)
    M = np.array([x.reshape(-1) for x in out]); _, sv, vh = np.linalg.svd(np.concatenate([M.real, M.imag], 1), full_matrices=False)
    r = int((sv > 1e-9 * sv[0]).sum()); n = d ** (2 * m)
    return [(vh[k, :n] + 1j * vh[k, n:]).reshape(d ** m, d ** m) for k in range(r)]

def reduce(C, sig, d):
    """Choi of rho -> Lambda(rho (x) sigma)"""
    K = np.kron(np.kron(np.eye(d), sig.T), np.eye(d)); return ptrace(K @ C, [d, d, d], 1)

def choi_sop(f, d):
    J = np.zeros((d * d, d * d), complex)
    for i in range(d):
        for j in range(d):
            E = np.zeros((d, d)); E[i, j] = 1; J += np.kron(E, f(E))
    return J

def target2(sig, d):
    ad = lambda r: -1j * (sig @ r - r @ sig); return choi_sop(lambda r: ad(ad(r)) / 2, d)

def dia_cons(Jd, s, d):
    Z = cp.Variable((d * d, d * d), hermitian=True)
    return [Z >> 0, Z - (Jd + Jd.H) / 2 >> 0, s * np.eye(d) - cp.partial_trace(Z, [d, d], axis=1) >> 0]

def dia(J, d):
    s = cp.Variable(); cp.Problem(cp.Minimize(s), dia_cons(cp.Constant(J), s, d)).solve(solver="SCS", eps=1e-9); return s.value

def setup(d):
    C0 = choi_map(lambda R, X: R * np.trace(X), d)
    C1 = choi_map(lambda R, X: -1j * (X @ R - R @ X), d)
    w, V = np.linalg.eigh(C0); K = V[:, w < 1e-9]; A = K.conj().T @ C1 @ K; A = (A + A.conj().T) / 2
    wa, Va = np.linalg.eigh(A); assert wa.min() > -1e-10, wa.min()
    Q = K @ Va[:, np.abs(wa) < 1e-9]
    S = Q.conj().T @ (C1 @ np.linalg.pinv(C0) @ C1) @ Q
    return C0, C1, Q, S

def solve(d, sigs, B, Q, S):
    c = cp.Variable(len(B)); C2 = sum(c[k] * B[k] for k in range(len(B))); s = cp.Variable()
    cons = [cp.partial_trace(C2, [d * d, d], axis=1) == 0]
    M = Q.conj().T @ C2 @ Q - S; cons.append((M + M.H) / 2 >> 0)
    for sg in sigs:
        cons += dia_cons(sum(c[k] * reduce(B[k], sg, d) for k in range(len(B))) - target2(sg, d), s, d)
    cp.Problem(cp.Minimize(s), cons).solve(solver="SCS", eps=1e-9, max_iters=200000)
    return s.value, sum(c.value[k] * B[k] for k in range(len(B)))

def state(x, d):
    G = (x[:d * d] + 1j * x[d * d:]).reshape(d, d); r = G @ G.conj().T; return r / np.trace(r)

if __name__ == "__main__":
    d, rounds = int(sys.argv[1]), int(sys.argv[2]); rng = np.random.default_rng(1)
    B = basis(d); C0, C1, Q, S = setup(d)
    dme = choi_map(lambda R, X: X * np.trace(R) - R * np.trace(X), d)
    pure = np.zeros((d, d), complex); pure[0, 0] = 1
    print("d=%d basis %d; DME leading constant at a pure sigma: %.5f" % (d, len(B), dia(reduce(dme, pure, d) - target2(pure, d), d)), flush=True)
    sigs = [pure, np.eye(d) / d] + [state(rng.normal(size=2 * d * d), d) for _ in range(4)]
    for r in range(rounds):
        val, C2 = solve(d, sigs, B, Q, S)
        best, bs = -1, None
        for _ in range(5):
            res = minimize(lambda x: -dia(reduce(C2, state(x, d), d) - target2(state(x, d), d), d), rng.normal(size=2 * d * d),
                           method="Nelder-Mead", options={"maxfev": 250, "fatol": 1e-7})
            if -res.fun > best: best, bs = -res.fun, state(res.x, d)
        print("round %d: minimax %.5f over %d states, worst found %.5f" % (r, val, len(sigs), best), flush=True)
        sigs.append(bs)
    np.save(os.path.join(os.path.dirname(os.path.abspath(__file__)), "C2_d%d.npy" % d), C2)
