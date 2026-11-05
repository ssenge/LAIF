"""Optimize depth-p local qudit algorithms for Max-k-Cut on the d-regular tree (see treeqaoa.py).

usage: optimize.py k d pmax [tries]
For each p it optimizes Grover QAOA (warm start from p-1 by interpolation, plus random starts), then
the richer families starting from the Grover optimum, and prints the cut fractions 1 - <P_uv>.
"""
import sys, json, time
import numpy as np
import jax
import jax.numpy as jnp
from scipy.optimize import minimize
from treeqaoa import unpack, nparams, edge_same_prob

FAMILIES = [("grover", "potts", "plus"), ("gen", "potts", "plus"), ("gen", "sym", "plus"), ("gen", "sym", "gen")]


def objective(k, d, p, fam):
    def obj(x):
        f, phis, _ = unpack(x, k, p, *fam)
        return edge_same_prob(f, phis, d)        # minimize same-label probability
    return jax.jit(jax.value_and_grad(obj))


def run(vg, x0):
    r = minimize(lambda x: tuple(np.asarray(v) for v in vg(jnp.array(x))), x0, jac=True, method="L-BFGS-B",
                 options={"maxiter": 3000, "gtol": 1e-10, "ftol": 1e-14})
    return r.fun, r.x


def embed(xg, k, p, fam):
    """Grover-QAOA angles (gamma_1, beta_1, ..., gamma_p, beta_p) -> parameters of family fam."""
    mixer, phase, start = fam
    out = []
    if start == "gen":
        out += [1.0] * k + [0.0] * k
    iu = np.triu_indices(k, 1)
    for t in range(p):
        g, b = xg[2 * t], xg[2 * t + 1]
        if phase == "potts":
            out.append(g)
        else:
            S = g * np.eye(k)
            out += list(S[np.triu_indices(k)])
        if mixer == "grover":
            out.append(b)
        else:                                            # H = b |+><+| = (b/k) * ones
            out += [b / k] * k + [b / k] * len(iu[0]) + [0.0] * len(iu[0])
    return np.array(out)


def interp(x, p):
    """INTERP warm start: depth p-1 -> p for (gamma, beta) pairs."""
    if p == 1:
        return None
    g, b = x[0::2], x[1::2]
    q = len(g)
    t = np.arange(p)
    ng = np.interp(t * (q - 1) / max(p - 1, 1), np.arange(q), g) if q > 1 else np.full(p, g[0])
    nb = np.interp(t * (q - 1) / max(p - 1, 1), np.arange(q), b) if q > 1 else np.full(p, b[0])
    out = np.empty(2 * p); out[0::2], out[1::2] = ng, nb
    return out


if __name__ == "__main__":
    k, d, pmax = map(int, sys.argv[1:4])
    tries = int(sys.argv[4]) if len(sys.argv) > 4 else 6
    rng = np.random.default_rng(0)
    xg, results = None, []
    for p in range(1, pmax + 1):
        t0 = time.time()
        vg = objective(k, d, p, FAMILIES[0])
        starts = ([interp(xg, p)] if xg is not None else []) + [rng.uniform(0, 1.5, 2 * p) for _ in range(tries)]
        best = min((run(vg, s) for s in starts), key=lambda r: r[0])
        xg = best[1]
        row = {"k": k, "d": d, "p": p, "grover": 1 - best[0]}
        for fam in FAMILIES[1:]:
            vgf = objective(k, d, p, fam)
            x0 = embed(xg, k, p, fam)
            cands = [run(vgf, x0)] + [run(vgf, x0 + rng.normal(0, 0.05, len(x0))) for _ in range(tries // 2)]
            row["/".join(fam)] = 1 - min(c[0] for c in cands)
        row["sec"] = round(time.time() - t0, 1)
        results.append(row)
        print(json.dumps(row), flush=True)
