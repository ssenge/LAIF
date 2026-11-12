"""Depth-p QAOA for LocalMaxCut (vertex satisfied iff at least ceil(d/2) of its d neighbours lie on the other side)
on the d-regular tree. State B_p C_p ... B_1 C_1 |+>^n, C_j = exp(-i gamma_j sum_w H_w), B_j = exp(-i beta_j sum X).

Each qubit carries a path a = (a_1..a_p, a_0, a_-p..a_-1): ket bits before each mixer, the measured bit, bra bits.
Its weight is (1/2) prod_j <a_{j+1}|B_j|a_j> conj(<a_-(j+1)|B_j|a_-j>), with a_{p+1} = a_-(p+1) = a_0. Each star
term H_w contributes exp(-i sum_j gamma_j (H_w(a_j) - H_w(a_-j))). By the light cone, stars with centre at distance
at most 2p from the root suffice, on the tree of radius 2p+1. The sum is computed from the leaves inwards with
messages M_r(a_parent, a_u) for u at distance r."""
import itertools, sys
import numpy as np

def value(d, gam, bet, extra=0):
    p = len(gam); k = -(-d // 2); L = 2 * p + 1
    P = np.array(list(itertools.product([0, 1], repeat=L)))          # columns: a_1..a_p, a_0, a_-p..a_-1
    ket = list(range(p)); zero = p; bra = [2 * p - j for j in range(p)]   # bra[j] is the column of a_-(j+1)
    def mix(x, y, b): return np.where(x == y, np.cos(b), -1j * np.sin(b))
    w = np.full(len(P), 0.5, complex)
    for j in range(p):
        nxt = ket[j + 1] if j + 1 < p else zero
        w *= mix(P[:, nxt], P[:, ket[j]], bet[j])
        nb = bra[j + 1] if j + 1 < p else zero
        w *= np.conj(mix(P[:, nb], P[:, bra[j]], bet[j]))
    def star_phase(own, nbrs):
        """own: path indices shape (...), nbrs: list of index arrays broadcastable; returns phase of H at own."""
        ph = 0
        for j in range(p):
            for col, sgn in ((ket[j], 1), (bra[j], -1)):
                cnt = sum((P[n, col] != P[own, col]).astype(int) for n in nbrs)
                ph = ph + sgn * gam[j] * (cnt >= k)
        return np.exp(-1j * ph)
    n = len(P); I = np.arange(n)
    M = np.ones((n, n), complex)                                       # message from a leaf-parent's children (r = 2p+1)
    for r in range(2 * p + extra, 0, -1):                                      # u at distance r with parent q
        # M_new[q, u] = sum_{c_1..c_{d-1}} star_phase(u; q, c) prod_i w(c_i) M[u, c_i]
        Wc = w[None, :] * M                                            # (u, c)
        if d - 1 == 2:
            q, u, c1, c2 = np.ix_(I, I, I, I)
            T = star_phase(u, [q, c1, c2]) * Wc[u, c1] * Wc[u, c2]
            Mn = T.sum((2, 3))
        else:
            Mn = np.zeros((n, n), complex)
            for qi in range(n):
                u = I.reshape([n] + [1] * (d - 1)); cs = [I.reshape([1] * (i + 1) + [n] + [1] * (d - 2 - i)) for i in range(d - 1)]
                T = star_phase(u, [np.full(1, qi).reshape([1] * d)] + cs)
                for i, c in enumerate(cs): T = T * Wc[u, c]
                Mn[qi] = T.reshape(n, -1).sum(1)
        M = Mn
    # root: sum over a_v and its d neighbours of w(a_v) O(a_v^0; nbrs^0) phase_v prod w(u) M[v, u]
    Wu = w[None, :] * M
    tot = 0
    us = [I.reshape([1] * i + [n] + [1] * (d - 1 - i)) for i in range(d)]
    for vi in range(n):
        T = w[vi] * star_phase(np.full(1, vi).reshape([1] * d), us)
        T = T * (sum((P[u, zero] != P[vi, zero]).astype(int) for u in us) >= k)
        for u in us: T = T * Wu[vi, u]
        tot += T.sum()
    return float(np.real(tot))

if __name__ == "__main__":
    import qaoa_tree
    for d, g, b in [(3, 0.7, 0.3), (3, 5.6473, 1.2248), (4, 5.6978232, 1.27641089), (4, 1.1, 0.4)]:
        a, c = value(d, [g], [b]), qaoa_tree.value(d, g, b)
        c2 = qaoa_tree.value(d, -g, b)
        print(d, g, b, a, c, c2); assert min(abs(a - c), abs(a - c2)) < 1e-10
    print("p=2 zero mixer second layer", value(3, [5.6473, 0.0], [1.2248, 0.0]))
