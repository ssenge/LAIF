#!/usr/bin/env python3
"""Checks Theorem 1 of ../README.md on small instances of the qubit (l, n, k)-HSMT task.

The n-qubit model: qubit i starts in |0>; phase estimation of exp(2i u_i X_i) leaves it in |0> if u_i is a multiple
of pi/2 and otherwise projects it onto |+> or |->; then exp(-i g_v |1><1|_v) for every k-set v; then Z measurements
on the qubits of B; then phase estimation of a k-qubit unitary G on the remaining set C.

The hybrid: a quantum block Q of vertices plus k spare qubits, and the weights g_u of all k-sets u not inside Q
stored classically. Z outcomes outside Q are sampled classically. On C, spare qubits are prepared in their initial
states and the classically stored hyperedges are applied as exp(-i g_u |1><1|_{u & C}) when u \\ C lies in the ones
of z. The check compares, for every branch (initial outcomes s, Z outcomes z), the branch probability and the
k-qubit state on C (up to a global phase), hence the full output distribution.
"""
import itertools
import numpy as np

PLUS, MINUS, ZERO = np.array([1, 1]) / np.sqrt(2), np.array([1, -1]) / np.sqrt(2), np.array([1.0, 0.0])


def product(vecs):
    out = np.array([1.0 + 0j])
    for v in vecs:
        out = np.kron(out, v)
    return out


def bits(idx, m):
    return [(idx >> (m - 1 - j)) & 1 for j in range(m)]


def apply_phases(psi, verts, edges):
    """psi on qubits `verts` (in this order); edges: list of (set of vertices within verts, angle)."""
    m = len(verts)
    pos = {v: j for j, v in enumerate(verts)}
    out = psi.copy()
    for idx in range(2 ** m):
        b = bits(idx, m)
        ph = sum(g for e, g in edges if all(b[pos[v]] for v in e))
        out[idx] *= np.exp(-1j * ph)
    return out


def measure(psi, verts, which, outcome):
    """Project qubits `which` of psi (on `verts`) onto Z outcomes; return (prob, state on the rest, rest)."""
    m = len(verts)
    pos = [verts.index(v) for v in which]
    rest = [v for v in verts if v not in which]
    out = np.zeros(2 ** len(rest), dtype=complex)
    for idx in range(2 ** m):
        b = bits(idx, m)
        if all(b[p] == o for p, o in zip(pos, outcome)):
            r = int("".join(str(b[verts.index(v)]) for v in rest) or "0", 2)
            out[r] += psi[idx]
    p = np.vdot(out, out).real
    return p, (out / np.sqrt(p) if p > 1e-14 else out), rest


def init_states(u, s):
    """Initial one-qubit state per vertex, from u_i and the initial outcome s_i in {+1, -1}."""
    return [ZERO if np.isclose(np.mod(4 * ui / (2 * np.pi), 1), 0) or np.isclose(np.mod(4 * ui / (2 * np.pi), 1), 1)
            else (PLUS if si > 0 else MINUS) for ui, si in zip(u, s)]


def check(n, k, q0, rng, trials=5):
    V = list(range(n))
    ksets = [frozenset(c) for c in itertools.combinations(V, k)]
    Q = set(range(q0))
    worst_p, worst_state = 0.0, 0.0
    for _ in range(trials):
        u = rng.uniform(0.1, 3.0, n)
        u[rng.integers(n)] = np.pi / 2  # one degenerate qubit stays in |0>
        g = {e: rng.uniform(-np.pi, np.pi) for e in ksets}
        B = sorted(rng.choice(n, n - k, replace=False).tolist())
        C = [v for v in V if v not in B]
        for s in itertools.product([1, -1], repeat=n):
            init = init_states(u, s)
            # n-qubit model
            psi = apply_phases(product(init), V, [(e, g[e]) for e in ksets])
            # hybrid: quantum block Q, classical rest
            Ql = sorted(Q)
            phi = apply_phases(product([init[v] for v in Ql]), Ql, [(e, g[e]) for e in ksets if e <= Q])
            BQ = [b for b in B if b in Q]
            for z in itertools.product([0, 1], repeat=n - k):
                zd = dict(zip(B, z))
                p_full, post_full, rest = measure(psi, V, B, z)
                assert rest == C
                # quantum Z outcomes on B & Q, classical ones on B \ Q from the initial product state
                p_q, post_q, restq = measure(phi, Ql, BQ, [zd[b] for b in BQ])
                p_c = np.prod([abs(init[b][zd[b]]) ** 2 for b in B if b not in Q])
                p_h = p_q * p_c
                worst_p = max(worst_p, abs(p_full - p_h))
                if p_full < 1e-12:
                    continue
                # assemble C: register Q & C (restq) plus spare qubits for C \ Q
                spare = [v for v in C if v not in Q]
                reg = np.kron(post_q, product([init[v] for v in spare]))
                order = restq + spare
                ones = {b for b in B if zd[b] == 1}
                edges = [(e & set(C), g[e]) for e in ksets if not e <= Q and (e - set(C)) <= ones and e & set(C)]
                reg = apply_phases(reg, order, edges)
                # global phase from classical edges inside ones (e & C empty) is dropped; reorder to C
                perm = [order.index(v) for v in C]
                reg = reg.reshape([2] * k).transpose(perm).reshape(-1)
                worst_state = max(worst_state, 1 - abs(np.vdot(post_full, reg)))
    assert worst_p < 1e-12 and worst_state < 1e-12, (worst_p, worst_state)
    nc = len(ksets) - len([e for e in ksets if e <= Q])
    print(f"n={n} k={k} |Q|={q0}: {q0 + k} qubits, {nc} of {len(ksets)} weights classical; "
          f"max branch prob diff {worst_p:.1e}, max 1-|overlap| {worst_state:.1e}")


def main():
    rng = np.random.default_rng(1)
    check(5, 2, 0, rng)
    check(5, 2, 3, rng)
    check(6, 2, 4, rng)
    check(6, 3, 4, rng)
    check(6, 3, 6, rng)


if __name__ == "__main__":
    main()
