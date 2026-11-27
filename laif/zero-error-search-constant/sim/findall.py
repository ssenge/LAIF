"""Find-All, m = 1: exact optimum of the expected number of queries for zero-error output of the whole marked set S
(|S| = k known) among N items, over all algorithms with at most T queries (Gram-matrix program, symmetrized).
Inputs: k-subsets S. Active Gram C_t is S_N-invariant: C = sum_j c_j A_j, A_j = [|S cap S'| = j] (Johnson scheme).
A query on index x: C = sum_x Gamma^(x) + Gamma^null, Gamma^(x) invariant under Stab(x), afterwards
C' = sum_x D_x Gamma^(x) D_x + Gamma^null, D_x = diag((-1)^[x in S]). Halting removes d I (outputs S differ).
Gamma^(x) is parametrized by the Stab(0)-orbit basis on pairs (S, S'); PSD is imposed after a numerical block
diagonalization of that algebra. Prints min E / ((pi/4) sqrt N * H_k), H_k = sum_{r<=k} r^{-1/2}, against the sequential
weakly measured strike-out value 1/2 + 1/pi. Mode 'any': zero-error output of one element of S instead; the halted
part is then sum_x of a PSD Stab(x)-invariant matrix supported on the pairs with x in S and x in S'.
usage: findall.py N k T [all|any]"""
import os, sys, itertools
for _v in ("RAYON_NUM_THREADS", "OMP_NUM_THREADS", "OPENBLAS_NUM_THREADS", "MKL_NUM_THREADS", "VECLIB_MAXIMUM_THREADS"): os.environ[_v] = "1"
import numpy as np, cvxpy as cp

def setup(N, k):
    sets = [frozenset(s) for s in itertools.combinations(range(N), k)]; n = len(sets)
    inter = np.array([[len(s & t) for t in sets] for s in sets])
    has0 = np.array([0 in s for s in sets])
    # Stab(0)-orbits of pairs: (|S cap S'|, 0 in S, 0 in S') with symmetric pairs merged
    key = {}
    lab = np.zeros((n, n), int)
    for i in range(n):
        for j in range(n):
            kk = (inter[i, j], min(has0[i], has0[j]), max(has0[i], has0[j]))
            lab[i, j] = key.setdefault(kk, len(key))
    B = [(lab == q).astype(float) for q in range(len(key))]
    mixed = [kk[1] != kk[2] for kk in key]        # one of S, S' contains 0: sign flip under the query on 0
    J = [(inter == j).astype(float) for j in range(k + 1)]   # Johnson basis, J[k] = identity
    # sum over x of the permuted orbit matrix, expressed in the Johnson basis: coefficient = value at a representative pair
    rep = [np.argwhere(inter == j)[0] for j in range(k + 1)]
    def sum_x(Q, flip):
        out = np.zeros(k + 1)
        for j, (i, l) in enumerate(rep):
            s, t = sets[i], sets[l]; tot = 0.0
            for x in range(N):
                # value of the orbit matrix Q at (pi S, pi S') with pi mapping x -> 0: orbit key depends on x in S, x in S'
                kk = (j, min(x in s, x in t), max(x in s, x in t))
                if kk in key and key[kk] == Q: tot += (-1.0 if (flip and mixed[Q]) else 1.0)
            out[j] = tot
        return out
    Sp = np.array([sum_x(q, False) for q in range(len(B))]); Sm = np.array([sum_x(q, True) for q in range(len(B))])
    # numerical block diagonalization of the orbit algebra: commutant eigenbasis of a generic element
    rng = np.random.default_rng(0); G = sum(rng.normal() * b for b in B); G = (G + G.T) / 2
    w, V = np.linalg.eigh(G)
    groups = []; cur = [0]
    for i in range(1, n):
        if abs(w[i] - w[i - 1]) < 1e-7: cur.append(i)
        else: groups.append(cur); cur = [i]
    groups.append(cur)
    both0 = [q for q, kk in enumerate(key) if kk[1] == 1 and kk[2] == 1]
    return sets, B, Sp, Sm, J, V, groups, both0

def blocks(B, V, groups):
    """A Stab-invariant matrix M = sum_q g_q B_q acts on each isotypic component as M_i (x) I. Groups of equal
    eigenvalues of a generic element are the f_j (x) C^d; take v_1 in the first group of a component and
    v_j = P_j X v_1 (X generic) in the others, so that <v_j, M v_l> = (M_i)_{jl} up to positive scaling."""
    rng = np.random.default_rng(2); X = sum(rng.normal() * b for b in B)
    P = [V[:, g] @ V[:, g].T for g in groups]; v1s = [V[:, g[0]] for g in groups]
    comp = list(range(len(groups)))
    def find(i):
        while comp[i] != i: i = comp[i]
        return i
    for a in range(len(groups)):
        for b_ in range(a + 1, len(groups)):
            if len(groups[a]) == len(groups[b_]) and np.linalg.norm(P[b_] @ X @ v1s[a]) > 1e-8: comp[find(b_)] = find(a)
    out = []
    for r in sorted({find(i) for i in range(len(groups))}):
        mem = [i for i in range(len(groups)) if find(i) == r]
        vs = []
        for i in mem:
            v = v1s[r] if i == r else P[i] @ X @ v1s[r]
            vs.append(v / np.linalg.norm(v))
        W = np.array(vs).T
        out.append((None, [W.T @ b @ W for b in B]))
    return out

def solve(N, k, T, mode="all"):
    sets, B, Sp, Sm, J, V, groups, both0 = setup(N, k)
    blk = blocks(B, V, groups); nq = len(B)
    g = cp.Variable((T, nq)); gn = cp.Variable((T, k + 1)); c = cp.Variable((T + 1, k + 1)); d = cp.Variable(T, nonneg=True)
    cons = [c[0] == np.ones(k + 1), c[T] == 0]
    # PSD of an S_N-invariant matrix sum_j c_j J_j: eigenvalues of the Johnson scheme
    rngv = np.random.default_rng(1); Gj = sum(rngv.normal() * x for x in J); wj, Vj = np.linalg.eigh(Gj)
    reps = []; cur = [0]
    for i in range(1, len(wj)):
        if abs(wj[i] - wj[i - 1]) < 1e-7: cur.append(i)
        else: reps.append(cur[0]); cur = [i]
    reps.append(cur[0])
    Jeig = np.array([[Vj[:, r] @ x @ Vj[:, r] for x in J] for r in reps])   # rows: eigenspaces, cols: j
    for t in range(T):
        for idx, mats in blk:
            M = sum(g[t, q] * mats[q] for q in range(nq)); cons.append((M + M.T) / 2 >> 0)
        cons += [Jeig @ gn[t] >= 0]
        cons += [c[t] == g[t] @ Sp + gn[t]]
        post = g[t] @ Sm + gn[t]
        if mode == "all":
            cons += [c[t + 1][:k] == post[:k], c[t + 1][k] == post[k] - d[t]]
        else:
            hz = cp.Variable(len(both0))
            for idx, mats in blk:
                M = sum(hz[i] * mats[q] for i, q in enumerate(both0)); cons.append((M + M.T) / 2 >> 0)
            cons += [c[t + 1] == post - hz @ Sp[both0]]
        cons += [Jeig @ c[t + 1] >= 0]
    prob = cp.Problem(cp.Minimize(cp.sum(c[:T, k])), cons)
    prob.solve(solver="CLARABEL")
    return prob.value

if __name__ == "__main__":
    N, k, T = (int(v) for v in sys.argv[1:4]); mode = sys.argv[4] if len(sys.argv) > 4 else "all"
    val = solve(N, k, T, mode)
    if mode == "any":
        print("N=%d k=%d T=%d any: min E[queries] = %.4f, / ((pi/4) sqrt(N/k)) = %.5f"
              % (N, k, T, val, val / (np.pi / 4 * np.sqrt(N / k))), flush=True); sys.exit()
    Hk = sum(r ** -0.5 for r in range(1, k + 1)); ref = np.pi / 4 * np.sqrt(N) * Hk
    print("N=%d k=%d T=%d: min E[queries] = %.4f, / ((pi/4) sqrt N H_k) = %.5f  (1/2 + 1/pi = %.5f)"
          % (N, k, T, val, val / ref, 0.5 + 1 / np.pi), flush=True)
