# SDP upper bound on the basis-average purity (1/d^t) sum_f w_f ||S_f||_F^2 over rank-one POVMs on (C^d)^{(x)t}:
# X = sum_f w_f (ff^dag)^{(x)2} satisfies X >= 0, F X = X (replica swap), Tr_2 X = I; maximize <W, X>/(t^2 d^t),
# W = sum_{j,k} SWAP(system j of replica 1, system k of replica 2). Compare with the product basis 1/t + (1-1/t)/d.
import numpy as np, itertools, cvxpy as cp, sys
def perm_op(d, nsys, perm):              # operator permuting nsys qudits: out system i gets input system perm[i]
    D = d ** nsys; P = np.zeros((D, D))
    for idx in itertools.product(range(d), repeat=nsys):
        out = tuple(idx[perm[i]] for i in range(nsys))
        P[np.ravel_multi_index(out, [d] * nsys), np.ravel_multi_index(idx, [d] * nsys)] = 1
    return P
for d, t in [tuple(map(int, a.split(','))) for a in sys.argv[1:]]:
    D = d ** t; n = 2 * t
    W = np.zeros((D * D, D * D))
    for j in range(t):
        for k in range(t):
            p = list(range(n)); p[j], p[t + k] = p[t + k], p[j]; W += perm_op(d, n, p)
    F = perm_op(d, n, list(range(t, n)) + list(range(t)))
    X = cp.Variable((D * D, D * D), hermitian=True)
    cons = [X >> 0, F @ X == X, cp.partial_trace(X, [D, D], axis=1) == np.eye(D)]
    prob = cp.Problem(cp.Maximize(cp.real(cp.trace(W @ X)) / (t * t * D)), cons)
    prob.solve(solver="CLARABEL")
    print(f"d={d} t={t}: SDP bound {prob.value:.4f}  product {1/t + (1-1/t)/d:.4f}  1/t+1/d {1/t+1/d:.4f}", flush=True)
