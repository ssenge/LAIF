"""QAOA at depth q, measure, then one round of a classical local rule, on d-regular graphs of girth
>= 2q+4 (the girth of depth q+1 algorithms).

joint(): exact distribution of the measured labels of an edge (u, v) and of the other d-1
neighbours of each endpoint, the neighbours summarized by label counts (the rule only sees counts).
rule search: every deterministic label-equivariant rule (own label, neighbour counts) -> new label.
"""
import itertools, math
import numpy as np
import jax.numpy as jnp
from treeqaoa import apply_axes, unpack


def compositions(total, parts):
    if parts == 1:
        yield (total,); return
    for i in range(total + 1):
        for rest in compositions(total - i, parts - 1):
            yield (i,) + rest


def joint(f, phis, d):
    """J[x, y, n, n'] = P(label u = x, label v = y, counts of u's other neighbours = n, of v's = n')."""
    q, k = len(phis), f.shape[0]
    E = [jnp.exp(-1j * ph) for ph in phis]
    ones = jnp.ones((k, k), dtype=complex)
    inner = E + [ones] + [jnp.conj(e) for e in E]
    H = jnp.ones_like(f)
    for _ in range(q):                                     # a measured neighbour needs its subtree to depth q
        H = apply_axes(f * H, inner) ** (d - 1)
    # message of one child whose own measured label is c
    child = f * H
    msg = []
    for c in range(k):
        sel = jnp.zeros(k).at[c].set(1.0).reshape((1,) * q + (k,) + (1,) * q)
        msg.append(apply_axes(child * sel, inner))
    comps = list(compositions(d - 1, k))
    G = []
    for n in comps:
        mult = math.factorial(d - 1) / np.prod([math.factorial(x) for x in n])
        t = f * mult
        for c, nc in enumerate(n):
            t = t * msg[c] ** nc
        G.append(t)
    G = jnp.stack(G)                                       # (N, k^(2q+1))
    root_nonmid = E + [jnp.eye(k, dtype=complex)] + [jnp.conj(e) for e in E]
    R = jnp.stack([apply_axes(g, root_nonmid) for g in G])  # identity on mid keeps y at the mid axis
    # J[x, y, n, n'] = sum_{a, a_mid = x} G[n](a) * R[n'](a with mid -> y)
    Gm = jnp.moveaxis(G.reshape((len(comps),) + (k,) * (2 * q + 1)), q + 1, 1).reshape(len(comps), k, -1)
    Rm = jnp.moveaxis(R.reshape((len(comps),) + (k,) * (2 * q + 1)), q + 1, 1).reshape(len(comps), k, -1)
    J = jnp.einsum("nxa,mya->xynm", Gm, Rm)
    return J, comps


def rule_states(k, d):
    """Canonical states seen by a vertex: (count of neighbours with my label, sorted counts of the others)."""
    S = set()
    for n in compositions(d, k):
        S.add((n[0], tuple(sorted(n[1:]))))
    return sorted(S)


def new_label_dist(x, counts, rule, k):
    """counts = full neighbour label counts (length k). rule[state] = 0 keep, r>0 move to a label whose
    count has rank r-1 among the other labels (ties split evenly). Returns a length-k distribution."""
    others = [c for c in range(k) if c != x]
    st = (counts[x], tuple(sorted(counts[c] for c in others)))
    a = rule[st]
    out = np.zeros(k)
    if a == 0:
        out[x] = 1.0
        return out
    target = sorted(counts[c] for c in others)[a - 1]
    tied = [c for c in others if counts[c] == target]
    out[tied] = 1.0 / len(tied)
    return out


def cut_after_rule(J, comps, rule, k):
    J = np.asarray(J).real
    same = 0.0
    for x, y in itertools.product(range(k), repeat=2):
        for i, n in enumerate(comps):
            cu = list(n); cu[y] += 1                       # u's neighbours: its children plus v
            du = new_label_dist(x, cu, rule, k)
            for j, m in enumerate(comps):
                pr = J[x, y, i, j]
                if pr == 0:
                    continue
                cv = list(m); cv[x] += 1
                dv = new_label_dist(y, cv, rule, k)
                same += pr * float(du @ dv)
    return 1 - same


def best_rule(J, comps, k, d):
    states = rule_states(k, d)
    choices = [range(k) for _ in states]                   # keep, or move to rank 0..k-2
    best = (-1, None)
    for acts in itertools.product(*choices):
        rule = dict(zip(states, acts))
        v = cut_after_rule(J, comps, rule, k)
        if v > best[0]:
            best = (v, rule)
    return best


if __name__ == "__main__":
    import sys
    k, d, q = map(int, sys.argv[1:4])
    x = np.load(f"grover_{k}_{d}_{q}.npy")
    f, phis, _ = unpack(jnp.array(x), k, q, "grover", "potts", "plus")
    J, comps = joint(f, phis, d)
    Jr = np.asarray(J)
    assert abs(Jr.sum() - 1) < 1e-9 and abs(Jr.imag).max() < 1e-9 and Jr.real.min() > -1e-12
    keep = {s: 0 for s in rule_states(k, d)}
    print("QAOA_q cut (rule = keep):", cut_after_rule(J, comps, keep, k))
    v, rule = best_rule(J, comps, k, d)
    print(f"QAOA_{q} + best 1-round rule: {v:.6f}   (girth >= {2*q+4}, compare depth {q+1})")
    print({s: a for s, a in rule.items() if a})
