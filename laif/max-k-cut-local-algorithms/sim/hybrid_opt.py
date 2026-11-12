"""Joint optimization of QAOA angles (depth q) and a one-round classical rule for Max-k-Cut on
d-regular graphs of girth >= 2q+4.

Rule: for each canonical state s = (count of neighbours sharing my label, sorted counts of the other
labels), a distribution pi_s over actions {keep, move to the label of count rank 0..k-2}, ties split
evenly. Cut = 1 - sum_{x,y,n,n'} J * <d_u, d_v>. Alternates: exact coordinate ascent over the
deterministic rule, then gradient steps on the angles for that rule.

usage: hybrid_opt.py k d q [rounds]
"""
import sys, json, time
import numpy as np
import jax
import jax.numpy as jnp
from scipy.optimize import minimize
from treeqaoa import unpack
from hybrid import joint, compositions, rule_states

jax.config.update("jax_enable_x64", True)


def tables(k, d):
    comps = list(compositions(d - 1, k))
    states = rule_states(k, d)
    sidx = {s: i for i, s in enumerate(states)}
    # for own label x, other endpoint label y, children counts n: state index and per-action label dists
    S = np.zeros((k, k, len(comps)), int)
    T = np.zeros((k, k, len(comps), k, k))              # [x, y, n, action, new label]
    for x in range(k):
        for y in range(k):
            for i, n in enumerate(comps):
                c = list(n); c[y] += 1
                others = [l for l in range(k) if l != x]
                S[x, y, i] = sidx[(c[x], tuple(sorted(c[l] for l in others)))]
                T[x, y, i, 0, x] = 1
                ranks = sorted(c[l] for l in others)
                for a in range(1, k):
                    tied = [l for l in others if c[l] == ranks[a - 1]]
                    T[x, y, i, a, tied] = 1 / len(tied)
    return comps, states, S, T


def cut_value(J, pi, S, T):
    """J[x, y, n, m]; pi[state, action]."""
    D = jnp.einsum("xyna,xynal->xynl", pi[S], T)        # d_u for own x, other y, children n
    # u has (x, other=y, n), v has (y, other=x, m)
    same = jnp.einsum("xynm,xynl,yxml->", J, D, D)
    return 1 - same


def main():
    k, d, q = map(int, sys.argv[1:4])
    rounds = int(sys.argv[4]) if len(sys.argv) > 4 else 6
    comps, states, S, T = tables(k, d)
    S, T = jnp.array(S), jnp.array(T)
    x = jnp.array(np.load(f"grover_{k}_{d}_{q}.npy"))

    def J_of(x):
        f, phis, _ = unpack(x, k, q, "grover", "potts", "plus")
        return jnp.real(joint(f, phis, d)[0])

    J_jit = jax.jit(J_of)
    obj = jax.jit(jax.value_and_grad(lambda x, pi: -cut_value(J_of(x), pi, S, T)))
    acts = np.zeros(len(states), int)                    # start: keep everywhere
    eye = np.eye(k)
    t0 = time.time()
    for r in range(rounds):
        J = J_jit(x)
        val = lambda a: float(cut_value(J, jnp.array(eye[a]), S, T))
        cur = val(acts)
        improved = True
        while improved:                                  # exact coordinate ascent on the rule
            improved = False
            for s in range(len(states)):
                for a in range(k):
                    if a == acts[s]:
                        continue
                    trial = acts.copy(); trial[s] = a
                    v = val(trial)
                    if v > cur + 1e-13:
                        acts, cur, improved = trial, v, True
        pi = jnp.array(eye[acts])
        res = minimize(lambda z: tuple(np.asarray(t) for t in obj(jnp.array(z), pi)), np.asarray(x),
                       jac=True, method="L-BFGS-B", options={"maxiter": 500, "gtol": 1e-11})
        x = jnp.array(res.x)
        print(json.dumps({"round": r, "rule_only": round(cur, 7), "joint": round(-res.fun, 7),
                          "sec": round(time.time() - t0)}), flush=True)
    np.save(f"hybrid_{k}_{d}_{q}.npy", np.asarray(x))
    np.save(f"hybridrule_{k}_{d}_{q}.npy", acts)
    print("RESULT", json.dumps({"k": k, "d": d, "q": q, "girth": 2 * q + 4, "cut": round(-res.fun, 7),
                                "moves": {str(states[s]): int(a) for s, a in enumerate(acts) if a}}))


if __name__ == "__main__":
    main()
