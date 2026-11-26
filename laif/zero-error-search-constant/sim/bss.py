"""Exact optimum of zero-error search (one marked item among N, known), expected number of queries, over ALL algorithms
with at most T queries, via the Gram-matrix (BSS) characterization with intermediate stopping.
Inputs x in [N]. Gram of the active branch C_t (S_N-invariant: diagonal a_t, off-diagonal b_t). Query t+1 splits
C_t = sum_i Gamma^(i) + Gamma^null, Gamma^(i) the permutation of Gamma (invariant under S_{N-1} fixing 0; entries
p = [0,0], q = [0,y], r = [x,x], s = [x,y]) and Gamma^null S_N-invariant (a', b'). After the query the off-diagonal is
-2q + (N-2)s + b', the diagonal unchanged. Zero error forces every stopped branch with output z to have Gram d e_z e_z^T,
so the stopped part is d_{t+1} I and C_{t+1} = G_{t+1} - d_{t+1} I must stay PSD. Cost: sum_t a_t (active probability at
each query). Termination: C_T = 0. Prints min E[queries] / ((pi/4) sqrt N) and compares with 1/2 + 1/pi = 0.8183.
usage: bss.py N [T]"""
import os, sys
for _v in ("RAYON_NUM_THREADS", "OMP_NUM_THREADS", "OPENBLAS_NUM_THREADS", "MKL_NUM_THREADS", "VECLIB_MAXIMUM_THREADS"): os.environ[_v] = "1"
import numpy as np, cvxpy as cp

def psd2(x, z, y):          # [[x, z], [z, y]] >= 0 as a second-order cone
    return cp.SOC(x + y, cp.hstack([2 * z, x - y]))

def solve(N, T):
    # scaled: R = (N-1) r, S = (N-2) s, Q = sqrt(N-1) q keep all coefficients O(1)
    p, Q, R, S, a1, b1, d = (cp.Variable(T) for _ in range(7))
    a = cp.Variable(T + 1); b = cp.Variable(T + 1); c = 2 / np.sqrt(N - 1)
    cons = [a[0] == 1, b[0] == 1, a[T] == 0, b[T] == 0, d >= 0]
    for t in range(T):
        cons += [a[t] == p[t] + R[t] + a1[t], b[t] == c * Q[t] + S[t] + b1[t],
                 (N - 2) * R[t] >= (N - 1) * S[t], psd2(p[t], Q[t], R[t] / (N - 1) + S[t]),
                 a1[t] >= b1[t], a1[t] + (N - 1) * b1[t] >= 0,
                 a[t + 1] == a[t] - d[t], b[t + 1] == -c * Q[t] + S[t] + b1[t],
                 a[t + 1] >= b[t + 1], a[t + 1] + (N - 1) * b[t + 1] >= 0]
    prob = cp.Problem(cp.Minimize(cp.sum(a[:T])), cons)
    prob.solve(solver="CLARABEL", tol_gap_abs=1e-10, tol_gap_rel=1e-10, tol_feas=1e-10, max_iter=500)
    return prob.value, a.value, d.value, b.value

if __name__ == "__main__":
    N = int(sys.argv[1]); T = int(sys.argv[2]) if len(sys.argv) > 2 else int(np.ceil(1.0 * np.pi / 4 * np.sqrt(N))) + 3
    val, a, d, b = solve(N, T)
    ref = np.pi / 4 * np.sqrt(N)
    print("N=%d T=%d: min E[queries] = %.4f, / ((pi/4) sqrt N) = %.5f   (1/2 + 1/pi = %.5f, exact Grover 1)"
          % (N, T, val, val / ref, 0.5 + 1 / np.pi), flush=True)
