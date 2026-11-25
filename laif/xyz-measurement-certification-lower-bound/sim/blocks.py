"""Numerical search (local, non-adaptive settings): minimize over orthogonal k-qubit pairs (A, A') the max over X/Y/Z basis settings B in {X,Y,Z}^k of the
overlap coefficient BC_B = sum_x |<x_B|A>| |<x_B|A'>|. Per-qubit exponent alpha = -log2(BC*)/k."""
import itertools, numpy as np, sys
from scipy.optimize import minimize
H = np.array([[1, 1], [1, -1]]) / np.sqrt(2); Sd = np.array([[1, 0], [0, -1j]])
U1 = {'Z': np.eye(2), 'X': H, 'Y': H @ Sd}          # rows: basis vectors <x_B|
def bases(k):
    out = []
    for B in itertools.product('XYZ', repeat=k):
        M = np.array([[1.0]])
        for b in B: M = np.kron(M, U1[b])
        out.append(M)
    return out
def unpack(v, k):
    D = 2 ** k; z = v[:2 * D] + 1j * 0; a = v[:D] + 1j * v[D:2 * D]; b = v[2 * D:3 * D] + 1j * v[3 * D:]
    a /= np.linalg.norm(a); b = b - (a.conj() @ b) * a; b /= np.linalg.norm(b); return a, b
def worst(v, k, Bs, beta=200.0):
    a, b = unpack(v, k); vals = np.array([np.sum(np.abs(M @ a) * np.abs(M @ b)) for M in Bs])
    return vals.max(), np.log(np.sum(np.exp(beta * (vals - vals.max())))) / beta + vals.max()
k = int(sys.argv[1]); trials = int(sys.argv[2]); Bs = bases(k); rng = np.random.default_rng(0); best = (9, None)
for t in range(trials):
    v = rng.normal(size=4 * 2 ** k)
    for beta in [20, 100, 500, 2000]:
        v = minimize(lambda w: worst(w, k, Bs, beta)[1], v, method='BFGS', options={'maxiter': 3000}).x
    m = worst(v, k, Bs)[0]
    if m < best[0]: best = (m, v)
print(f"k={k}: min max BC = {best[0]:.6f}, per-qubit factor {best[0] ** (1 / k):.6f}, alpha = {-np.log2(best[0]) / k:.4f}")
a, b = unpack(best[1], k); np.save(f"best_k{k}.npy", np.array([a, b]))
