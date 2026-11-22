"""Check of Theorem 1 by semidefinite programming: optimal worst-case fidelity of n copies of rank-r rho on C^d -> |A_rho> on r registers.
Covariant channels suffice; Choi in span of partial transposes (on inputs) of permutations of n+r systems.
Positivity checked in the left-regular rep of that algebra (faithful *-rep)."""
import itertools, math, sys
import resource, time
def mem(t): pass
import numpy as np, scipy.sparse as sp, cvxpy as cp

def lds(w):
    tails = []
    for x in w:
        x = -x; lo, hi = 0, len(tails)
        while lo < hi:
            m = (lo + hi) // 2
            if tails[m] < x: lo = m + 1
            else: hi = m
        tails[lo:lo + 1] = [x]
    return len(tails)

def predicted(lam, d, n):
    r = len(lam); law = np.zeros(r + 1)
    for w in itertools.product(range(r), repeat=n):
        law[lds(w)] += np.prod([lam[x] for x in w])
    return sum(law[k] / math.comb(d - k, r - k) for k in range(1, r + 1)), law

def run(lam, d, n):
    r = len(lam); N = n + r; D = d ** N
    idxs = np.array(list(itertools.product(range(d), repeat=N)))
    rav = lambda t: np.ravel_multi_index(t.T, (d,) * N)
    bs = []
    for pi in itertools.permutations(range(N)):
        out = idxs[:, list(pi)]                       # P_pi |idx> = |out>
        row = np.concatenate([idxs[:, :n], out[:, n:]], 1)
        col = np.concatenate([out[:, :n], idxs[:, n:]], 1)
        bs.append(sp.csr_matrix((np.ones(D), (rav(row), rav(col))), shape=(D, D)))
    m0 = len(bs)
    Bv = sp.vstack([b.reshape(1, D * D) for b in bs]).tocsr()
    G = (Bv @ Bv.T).toarray()
    ev, U = np.linalg.eigh(G); keep = ev > 1e-8 * ev.max()
    T = U[:, keep] / np.sqrt(ev[keep])                # e_k = sum_pi T[pi,k] b_pi, orthonormal
    m = T.shape[1]
    mem('m = T.shape[')
    # left-regular structure: L_k[i,j] = <e_i, e_k e_j>; via b products
    Pb = np.zeros((m0, m0, m0))                       # <b_t, b_a b_c>
    for a in range(m0):
        prods = sp.vstack([(bs[a] @ bs[c]).reshape(1, D * D) for c in range(m0)]).tocsr()
        Pb[a] = (prods @ Bv.T).toarray().T              # Pb[a][t,c]
    # L for b_a in e-coordinates: e_i^T (b_a e_j) = T[:,i]^T Pb[a] T[:,j]
    Lb = np.einsum('ti,atc,cj->aij', T, Pb, T)
    Lk = np.einsum('ak,aij->kij', T, Lb)              # L_{e_k}
    mem('Lk = np.eins')
    # partial trace over outputs of b_pi -> d^n x d^n
    Din, Dout = d ** n, d ** r
    PT = []
    for b in bs:
        bb = b.toarray().reshape(Din, Dout, Din, Dout)
        PT.append(np.einsum('iaja->ij', bb).ravel())
    PT = np.array(PT)                                 # m0 x Din^2
    mem('PT = np.arra')
    # objective vector: <b_pi, X0>, X0 = (rho^{xn})^T (x) |A><A|, real
    rho = np.diag(list(lam) + [0] * (d - r)); R = np.array([[1.0]])
    for _ in range(n): R = np.kron(R, rho)
    A = np.zeros(Dout)
    for perm in itertools.permutations(range(r)):
        sgn = np.linalg.det(np.eye(r)[list(perm)])
        A[np.ravel_multi_index(tuple(perm), (d,) * r)] += sgn
    A /= np.linalg.norm(A)
    X0 = np.kron(R.T, np.outer(A, A))
    obj_b = np.array([b.multiply(sp.csr_matrix(X0)).sum() for b in bs])
    c = cp.Variable(m)
    Ls = (Lk + Lk.transpose(0, 2, 1)) / 2; La = (Lk - Lk.transpose(0, 2, 1)).reshape(m, -1).T
    keepa = np.abs(La).sum(1) > 1e-12
    Sexpr = cp.reshape(Ls.reshape(m, -1).T @ c, (m, m), order='F')
    coef = T @ c
    cons = [Sexpr >> 0, La[keepa] @ c == 0, PT.T @ coef == np.eye(Din).ravel()]
    prob = cp.Problem(cp.Maximize(obj_b @ coef), cons)
    mem('prob = cp.Pr')
    prob.solve(solver='SCS', eps=1e-9, max_iters=200000)
    return prob.value, m

if __name__ == '__main__':
    for d, lam, n in [(3, (0.7, 0.3), 3), (3, (0.5, 0.5), 3), (3, (0.9, 0.1), 3),
                      (4, (0.7, 0.3), 1), (4, (0.7, 0.3), 2), (4, (0.6, 0.4), 3), (4, (0.5, 0.3, 0.2), 1), (4, (0.5, 0.3, 0.2), 2)]:
        val, m = run(lam, d, n); pred, law = predicted(lam, d, n)
        print(f"d={d} lam={lam} n={n} dimA={m} SDP={val:.6f} pred={pred:.6f} P(L=r)={law[len(lam)]:.6f} diff={val-pred:+.2e}", flush=True)
        assert abs(val - pred) < 1e-6
    print("SDP optimum equals E[1/C(d - L_n, r - L_n)] in all cases")
