"""m parallel queries per round (k = 1). The m-register marking oracle acts, in the |+>/|-> basis of the target qubits, as the
set phase (-1)^[x in A], A = items hit an odd number of times by |->-registers, |A| <= m. One round from an S_N-invariant
Gram (a, b): Gamma^(A) for |A| = j <= m, invariant under the stabilizer of A, scaled variables R1, S1, Q, R2, S2 (per j):
a = sum (R1 + R2), b = sum (S1 + 2Q + S2), b' = sum (S1 - 2Q + S2), PSD: (R1/(N-1) + S1)(R2/(N-1) + S2) >= Q^2,
R1 (j-1) >= (N-1) S1, R2 (N-1-j) >= (N-1) S2, R1/(N-1)+S1 >= 0, R2/(N-1)+S2 >= 0 (j = 0: R1 = S1 = Q = 0; j = 1: S1 = 0).
Prints max |d omega| / (2 arcsin sqrt(m/N)), omega = arccos(|mean state| / sqrt a), |mean state|^2 = (a + (N-1) b)/N."""
import os, sys
for _v in ("RAYON_NUM_THREADS", "OMP_NUM_THREADS", "OPENBLAS_NUM_THREADS"): os.environ[_v] = "1"
import numpy as np, cvxpy as cp

def omega(N, a, b):
    return np.arccos(np.sqrt(np.clip((a + (N - 1) * b) / (N * a), 0, 1)))

def reach(N, m, a, b, sign):
    cons = []; A = 0; B = 0; Bp = 0
    for j in range(0, m + 1):
        R1, S1, Q, R2, S2 = (cp.Variable() for _ in range(5))
        if j == 0: cons += [R1 == 0, S1 == 0, Q == 0]
        if j == 1: cons += [S1 == 0]
        if j >= 2: cons += [R1 * (j - 1) >= (N - 1) * S1]
        if N - j >= 2: cons += [R2 * (N - 1 - j) >= (N - 1) * S2]
        X1 = R1 / (N - 1) + S1; X2 = R2 / (N - 1) + S2
        cons += [cp.SOC(X1 + X2, cp.hstack([2 * Q, X1 - X2]))]
        A += R1 + R2; B += S1 + 2 * Q + S2; Bp += S1 - 2 * Q + S2
    cons += [A == a, B == b]
    pr = cp.Problem(cp.Maximize(sign * Bp), cons); pr.solve(solver="CLARABEL", tol_gap_abs=1e-11, tol_gap_rel=1e-11, tol_feas=1e-11); return Bp.value

if __name__ == "__main__":
    for N, m in ((16, 2), (64, 2), (64, 4), (256, 4), (256, 8)):
        th = np.arcsin(np.sqrt(m / N)); worst = 0
        for b in np.linspace(0, 1, 41):
            for s in (1, -1):
                bp = reach(N, m, 1.0, b, s)
                if bp is None: continue
                bp = min(max(bp, -1 / (N - 1)), 1)
                worst = max(worst, abs(omega(N, 1, bp) - omega(N, 1, b)) / (2 * th))
        print("N=%d m=%d: max |d omega| / (2 arcsin sqrt(m/N)) = %.5f" % (N, m, worst), flush=True)
