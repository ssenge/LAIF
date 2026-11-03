"""Numerical checks for the modular model of Section 6 of the write-up.

Model: weights A in Z_M^E, M = 2^k. Oracle phase omega^(z cut_A(S)). A uniform on {deg(A) = d}.

check_lemma: if sum_s Z_s delta_{x^s} = beta_u + beta_v (mod M) on all pairs u != v, then
    #{v : 2 beta_v != 0 mod M} <= T + 2.  Tested by exhaustive small search. T singletons give |Y| = T, so the bound is close to sharp there.
check_effective: the averaged final density matrix of a random algorithm equals the one from the
    effective model on quotient labels, |S,z>|L> -> omega^(beta.d) |S,z>|L + [z delta_S]>.

Limits: only small n, M and T are tried, so a pass is evidence for the identities and proves nothing. The proofs are the
Lean files.
"""
import itertools
import sys

import numpy as np


def pairs(n):
    return list(itertools.combinations(range(n), 2))


def delta(x, E):
    return np.array([x[u] ^ x[v] for u, v in E], dtype=np.int64)


def image_C(n, E, M):
    """dict: label vector F in Im C -> one phi with F = C(phi)."""
    out = {}
    for phi in itertools.product(range(M), repeat=n):
        F = tuple((phi[u] + phi[v]) % M for u, v in E)
        out.setdefault(F, phi)
    return out


def check_lemma(n, M, T, samples, rng):
    """Random and exhaustive search over T-term combinations for F in Im C; verify the bound."""
    E = pairs(n)
    imC = image_C(n, E, M)
    sets = [np.array(x) for x in itertools.product((0, 1), repeat=n)]
    worst, hits = 0, 0
    def test(F):
        nonlocal worst, hits
        key = tuple(int(v) for v in F % M)
        if key in imC:
            hits += 1
            phi = imC[key]
            y = sum(1 for p in phi if (2 * p) % M)
            worst = max(worst, y)
            assert y <= T + 2, (phi, y, T)
    if len(sets) ** T * (M - 1) ** T <= samples:
        for choice in itertools.product(range(len(sets)), repeat=T):
            for zs in itertools.product(range(1, M), repeat=T):
                test(sum(z * delta(sets[c], E) for c, z in zip(choice, zs)))
    else:
        for _ in range(samples):
            choice = rng.integers(0, len(sets), T)
            zs = rng.integers(1, M, T)
            test(sum(int(z) * delta(sets[c], E) for c, z in zip(choice, zs)))
    return worst, hits


def check_effective(n, M, t, seed):
    """Compare brute force average over A with the effective label model, for a random algorithm."""
    rng = np.random.default_rng(seed)
    E = pairs(n)
    omega = np.exp(2j * np.pi / M)
    sets = [np.array(x) for x in itertools.product((0, 1), repeat=n)]
    # one query register S, z with a small random subset, to keep the dimension low
    basis = [(i, z) for i in rng.choice(len(sets), 5, replace=False) for z in range(M)]
    dim = len(basis)
    def haar():
        q, _ = np.linalg.qr(rng.normal(size=(dim, dim)) + 1j * rng.normal(size=(dim, dim)))
        return q
    Us = [haar() for _ in range(t + 1)]
    F_of = [(int(z) * delta(sets[i], E)) % M for i, z in basis]
    cut_of = [delta(sets[i], E) for i, z in basis]
    zs = np.array([z for _, z in basis])
    # degree vector and all A in the coset, by brute force
    d = np.zeros(n, dtype=np.int64)
    d[0] = 2
    d = (d + 2) % M
    coset = []
    for A in itertools.product(range(M), repeat=len(E)):
        deg = np.zeros(n, dtype=np.int64)
        for (u, v), a in zip(E, A):
            deg[u] += a
            deg[v] += a
        if ((deg - d) % M == 0).all():
            coset.append(np.array(A))
    rho = np.zeros((dim, dim), dtype=complex)
    psi0 = np.zeros(dim, dtype=complex)
    psi0[0] = 1
    for A in coset:
        psi = Us[0] @ psi0
        for s in range(t):
            phases = omega ** ((zs * np.array([c @ A for c in cut_of])) % M)
            psi = Us[s + 1] @ (phases * psi)
        rho += np.outer(psi, psi.conj())
    rho /= len(coset)
    # effective model: labels F with section sigma(L) = first label seen in the coset
    imC = image_C(n, E, M)
    elements = {tuple((np.array(F)) % M): phi for F, phi in imC.items()}
    section = {}  # canonical key of coset -> representative
    def canon(F):
        return min(tuple((F + np.array(G)) % M) for G in elements)
    def rep(F):
        key = canon(F)
        return section.setdefault(key, np.array(F) % M)
    zero = np.zeros(len(E), dtype=np.int64)
    rep(zero)
    state = {canon(zero): Us[0] @ psi0}
    for s in range(t):
        new = {}
        for key, vec in state.items():
            sig = section[key]
            for i in range(dim):
                if vec[i] == 0:
                    continue
                G = (sig + F_of[i]) % M
                k2 = canon(G)
                sig2 = rep(G)
                beta = elements[tuple((G - sig2) % M)]
                ph = omega ** (int(np.dot(beta, d)) % M)
                new.setdefault(k2, np.zeros(dim, dtype=complex))
                new[k2][i] += ph * vec[i]
        state = {k: Us[s + 1] @ v for k, v in new.items()}
    rho2 = sum(np.outer(v, v.conj()) for v in state.values())
    return np.abs(rho - rho2).max(), abs(np.trace(rho2) - 1), len(coset), len(state)


if __name__ == "__main__":
    rng = np.random.default_rng(0)
    # tightness: T singletons give |Y| = T
    n, M = 6, 4
    E = pairs(n)
    imC = image_C(n, E, M)
    F = sum(delta(np.eye(n, dtype=int)[v], E) for v in range(4)) % M
    phi = imC[tuple(int(a) for a in F)]
    assert sum(1 for p in phi if (2 * p) % M) == 4
    print("singletons: T = 4 gives |Y| = 4")
    for n, M, T, samples in ((5, 4, 2, 10**6), (5, 4, 3, 200000), (6, 4, 3, 300000), (6, 4, 4, 300000),
                             (6, 8, 3, 300000), (5, 8, 4, 300000), (6, 4, 6, 300000), (7, 4, 5, 200000)):
        w, h = check_lemma(n, M, T, samples, rng)
        print(f"lemma n={n} M={M} T={T}: hits in Im C = {h:7d}, max |Y| = {w}, bound T+2 = {T + 2}", flush=True)
    for n, M, t, seed in ((4, 4, 1, 1), (4, 4, 3, 2), (4, 4, 4, 3), (5, 4, 2, 4), (5, 4, 3, 5)):
        err, tr, size, labels = check_effective(n, M, t, seed)
        print(f"effective n={n} M={M} t={t}: coset size {size}, reachable labels {labels}, max |rho - rho_eff| = {err:.2e}, trace error {tr:.2e}", flush=True)
        assert err < 1e-9
    print("all checks passed")
