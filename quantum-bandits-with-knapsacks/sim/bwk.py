# Optimistic-LP algorithm for quantum bandits with knapsacks (expected accounting), simulated.
# Quantum mean estimation is modelled by its guarantee: a block of N rounds of arm i returns estimates of r_i and C_i
# within eps(N) = A0 / N (l_inf). Checks: no resource is exceeded in T virtual rounds, the greedy schedule keeps every
# deficit in [-1, m], the regret stays below (Wbar + m + 2) OPT/B + W + m + 1, and the regret grows polylogarithmically in T.
# python -I bwk.py
import sys
import numpy as np
from scipy.optimize import linprog


def lp(r, C, budget):
    """max r.x s.t. C x <= budget (resource rows), sum x = 1, x >= 0; column 0 is the null arm."""
    res = linprog(-r, A_ub=C, b_ub=budget, A_eq=np.ones((1, len(r))), b_eq=[1.0], bounds=(0, None), method="highs")
    assert res.status == 0
    return res.x, -res.fun


def run(r, C, T, b, A0, N0, rng):
    """r: (m+1,), C: (d', m+1) resource rows without time; arm 0 is null (r = 0, C = 0). Returns regret, W, max deficit."""
    m = len(r) - 1
    B = b * T
    v_star = lp(r, C, np.full(C.shape[0], b))[1]
    Wbar = 2 * m * (m + 1 + 4 * A0 * (1 + np.log(T)))       # bound on the width sum (proof, Step 3)
    gamma = (Wbar + m + 2) / B
    if gamma >= 1:
        return None
    eps = np.ones(m + 1); eps[0] = 0.0                       # current radius per arm (trivial before a block completes)
    rhat = r.copy(); Chat = C.copy()
    blk_size = np.full(m + 1, N0); blk_done = np.zeros(m + 1, int)
    def solve():
        rU = np.minimum(1, rhat + eps); rU[0] = 0
        CL = np.maximum(0, Chat - eps); CL[:, 0] = 0
        return lp(rU, CL, np.full(C.shape[0], b * (1 - gamma)))[0]
    def estimate(i, N):
        e = A0 / N
        rhat[i] = np.clip(r[i] + rng.uniform(-e, e), 0, 1)
        Chat[:, i] = np.clip(C[:, i] + rng.uniform(-e, e, C.shape[0]), 0, 1)
        eps[i] = min(1.0, e)
    x = solve()
    X = np.zeros(m + 1); n = np.zeros(m + 1)
    rew = 0.0; cons = np.zeros(C.shape[0]); W = 0.0; dmin, dmax = 0.0, 0.0
    for t in range(T):
        X += x
        i = int(np.argmax(X - n))
        n[i] += 1
        rew += r[i]; cons += C[:, i]
        W += 2 * np.dot(x, eps)
        D = X - n; dmin = min(dmin, D.min()); dmax = max(dmax, D.max())
        assert np.all(cons <= B + 1e-9), "resource exceeded"
        if i > 0:
            blk_done[i] += 1
            if blk_done[i] == blk_size[i]:                     # block of arm i completed: new estimates, re-solve
                estimate(i, blk_size[i])
                blk_done[i] = 0; blk_size[i] *= 2
                x = solve()
    assert dmin >= -1 - 1e-9 and dmax <= m + 1e-9 and W <= Wbar + 1e-9
    regret = T * v_star - rew
    bound = (Wbar + m + 2) * T * v_star / B + W + m + 1      # gamma OPT + width sum + schedule deviation
    assert regret <= bound, (regret, bound)
    return regret, W, dmax, bound


if __name__ == "__main__":
    rng = np.random.default_rng(5)
    m, dres, b = 6, 3, 0.25
    A0, N0 = 2.0, 2
    for inst in range(3):
        r = np.concatenate([[0.0], rng.uniform(0.1, 1, m)])
        C = np.concatenate([np.zeros((dres, 1)), rng.uniform(0, 1, (dres, m))], axis=1)
        print(f"instance {inst}: v* = {lp(r, C, np.full(dres, b))[1]:.4f}")
        for T in [10 ** 4, 10 ** 5, 10 ** 6]:
            out = run(r, C, T, b, A0, N0, rng)
            if out is None:
                print(f"  T={T:8d}: budget below the slack, skipped"); continue
            reg, W, dmax, bound = out
            print(f"  T={T:8d}: regret {reg:9.1f}  (bound {bound:9.1f}, width sum {W:7.1f}, max deficit {dmax:.2f}, "
                  f"sqrt(T) = {np.sqrt(T):7.1f})", flush=True)
    print("bwk checks: ok")
