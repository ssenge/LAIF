"""k-tuple chain with free chain angles: x_{i+1} at angle t_i to s_i / |s_i| (s_1 = x1), s_{i+1} = s_i - x_{i+1}.
|s_{i+1}|^2 = |s_i|^2 + 1 - 2 |s_i| cos t_i, and |s_k| <= 1. Memory m from m^k prod p(t_i) = m, i.e. m = -sum p(t_i)/(k-1).
Time from k4_chain.time_k (nested two-oracle search with one product code per level).
Run: python k_general.py k seeds"""
import sys
from math import log2, sqrt
sys.path.insert(0, __file__.rsplit("/", 1)[0])
from k4_chain import p, time_k
from scipy.optimize import differential_evolution

def config(ts):
    s2 = 1.0
    for t in ts:
        s2 = s2 + 1 - 2 * sqrt(s2) * t
        if s2 <= 0:
            return None
    return s2

def evaluate(x, k):
    ts, cs = list(x[:k - 1]), list(x[k - 1:])
    s2 = config(ts)
    if s2 is None or s2 > 1 + 1e-9:
        return 9, None
    m = -sum(p(t) for t in ts) / (k - 1)
    return time_k(m, ts, cs), m

if __name__ == "__main__":
    k = int(sys.argv[1]); seeds = int(sys.argv[2]) if len(sys.argv) > 2 else 2
    # check: the balanced 4-configuration gives the minimal memory 0.172369 and time 0.304495
    tb, mb = evaluate([1 / 4, 1 / sqrt(6), sqrt(3 / 8), 0.23294119, 0.42108008, 0.42108008], 4)
    assert abs(mb - 0.172369) < 1e-6 and abs(tb - 0.304495) < 1e-6
    for wmem in (0.0, 0.5, 1.0, 2.0):          # minimize time + wmem * memory: points on the trade-off
        best = None
        for seed in range(seeds):
            r = differential_evolution(lambda x: (lambda tm: tm[0] + wmem * (tm[1] or 0))(evaluate(x, k)),
                                       [(0.01, 0.99)] * (2 * (k - 1)), seed=seed, tol=1e-10, maxiter=4000, popsize=30)
            if best is None or r.fun < best.fun:
                best = r
        t, m = evaluate(best.x, k)
        print(f"k={k} w={wmem}: time {t:.6f} memory {m:.6f} chain {[round(v, 4) for v in best.x[:k-1]]} buckets {[round(v, 4) for v in best.x[k-1:]]}", flush=True)
