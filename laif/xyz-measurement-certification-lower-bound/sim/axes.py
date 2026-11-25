"""kappa(S) = min over unit r of max over axes b in S of sqrt(1 - (r.b)^2), for finite axis sets S (README, Corollary 3).
Local minimization from many starts gives an admissible r, hence a valid upper estimate of kappa. Asserts kappa < 1,
kappa = sqrt(2/3) for X, Y, Z (attained at r = (1,1,1)/sqrt3) and kappa = 1/sqrt2 for X, Z. Prints the exponent
log2(1/kappa) per qubit, so that the bounds grow as d^{log2(1/kappa)}."""
import itertools, numpy as np
from scipy.optimize import minimize
def kappa(S, starts=400, seed=0):
    S = np.array([b / np.linalg.norm(b) for b in S]); rng = np.random.default_rng(seed); best = (2, None)
    f = lambda v: np.max(np.sqrt(np.clip(1 - (S @ (v / np.linalg.norm(v))) ** 2, 0, 1)))
    for _ in range(starts):
        res = minimize(f, rng.normal(size=3), method='Nelder-Mead', options={'xatol': 1e-12, 'fatol': 1e-13, 'maxiter': 4000})
        if res.fun < best[0]: best = (res.fun, res.x / np.linalg.norm(res.x))
    return best
E = np.eye(3)
sets = {
    'X, Y, Z': [E[0], E[1], E[2]],
    'X and Z only': [E[0], E[2]],
    'cube: 3 faces + 6 edges + 4 body diagonals': [E[0], E[1], E[2]] + [E[i] + s * E[j] for i, j in itertools.combinations(range(3), 2) for s in (1, -1)]
        + [np.array([1, s1, s2]) for s1 in (1, -1) for s2 in (1, -1)],
    'X, Y, Z and the 4 body diagonals': [E[0], E[1], E[2]] + [np.array([1, s1, s2]) for s1 in (1, -1) for s2 in (1, -1)],
}
for name, S in sets.items():
    k, r = kappa(S)
    assert k < 1 - 1e-6
    if name == 'X and Z only': assert abs(k - np.sqrt(0.5)) < 1e-9
    if name == 'X, Y, Z':
        assert abs(k - np.sqrt(2 / 3)) < 1e-9
        rr = np.ones(3) / np.sqrt(3); assert abs(np.max(np.sqrt(1 - (np.array(S) @ rr) ** 2)) - np.sqrt(2 / 3)) < 1e-12
    print(f"{name}: kappa = {k:.6f}, q = kappa^n, exponent log2(1/kappa) = {np.log2(1 / k):.4f} per qubit, r = {np.round(r, 4)}")
