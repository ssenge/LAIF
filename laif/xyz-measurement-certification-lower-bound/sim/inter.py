"""Interleaved strategies on T stored copies (README, Theorem 2): random adaptive trees over all nT qubits, each node
measuring one not yet measured qubit of any copy along X, Y or Z, chosen from the outcomes so far.
Asserts, with q = (2/3)^{n/2}, for (n, T) in {(1,2),(1,3),(1,4),(2,2),(2,3),(3,2)}:
  (1) sum_leaves |<e|p_s>| |<e|p_s'>| = q^{d(s,s')} for the product pattern states p_s (copy t in a^n or abar^n);
  (2) L1(P_{psi^T}, P_{rho^T}) <= (1+q)^T - 1;
  (3) L1(P_{psi^T}, P_{sigma_eps^T}) <= (1+2 eps q)^T - 1, sigma_eps = (1-2eps) psi + 2 eps rho;
  (4) L1(P_{rho_s^T}, P_{rho^T}) <= (1+s q)^T - 1, rho_s = (1-s) rho + s psi;
  (5) for every set A of copies and patterns s, s' on A: with U_s = <e| (p_s on A, psi^n on the other copies)>,
      sum_leaves |U_s| |U_s'| <= q^{d(s,s')}, the step used for sigma_eps^T.
The phase of abar is the one returned by numpy.linalg.eigh."""
import itertools, numpy as np
rng = np.random.default_rng(2)
r = np.ones(3) / np.sqrt(3)
X = np.array([[0, 1], [1, 0]]); Y = np.array([[0, -1j], [1j, 0]]); Z = np.diag([1., -1])
w, V = np.linalg.eigh((np.eye(2) + r[0] * X + r[1] * Y + r[2] * Z) / 2); a, b = V[:, 1], V[:, 0]
BAS = {nm: np.linalg.eigh(P)[1].T.conj() for nm, P in (('X', X), ('Y', Y), ('Z', Z))}
def kron(vs):
    out = np.array([1.0 + 0j])
    for v in vs: out = np.kron(out, v)
    return out
def leaves(N):
    """one random adaptive tree on N qubits: list of leaf product vectors (qubit order 0..N-1 in the tensor)"""
    out = []
    def rec(fixed):
        if len(fixed) == N:
            out.append(kron([fixed[i] for i in range(N)])); return
        free = [i for i in range(N) if i not in fixed]; qb = free[rng.integers(len(free))]; ax = 'XYZ'[rng.integers(3)]
        for x in range(2):
            f = dict(fixed); f[qb] = BAS[ax][x].conj(); rec(f)      # |e> with <e| = row x
    rec({}); return out
for n, T in [(1, 2), (1, 3), (1, 4), (2, 2), (2, 3), (3, 2)]:
    q = (2 / 3) ** (n / 2); A1, B1 = kron([a] * n), kron([b] * n)
    psi1 = (A1 + B1) / np.sqrt(2); rho1 = (np.outer(A1, A1.conj()) + np.outer(B1, B1.conj())) / 2; P1 = np.outer(psi1, psi1.conj())
    def tens(m):
        out = np.array([[1.0 + 0j]])
        for _ in range(T): out = np.kron(out, m)
        return out
    pats = {s: kron([A1 if si == 0 else B1 for si in s]) for s in itertools.product((0, 1), repeat=T)}
    for _ in range(40):
        L = np.array(leaves(n * T))
        assert np.allclose(np.sum(np.abs(L) ** 2, axis=1), 1) and np.allclose(L.conj() @ L.T, np.eye(len(L)))
        amp = {s: L.conj() @ v for s, v in pats.items()}
        for s, t in itertools.product(pats, repeat=2):
            d = sum(x != y for x, y in zip(s, t)); assert abs(np.sum(np.abs(amp[s]) * np.abs(amp[t])) - q ** d) < 1e-10
        for A in itertools.chain.from_iterable(itertools.combinations(range(T), k) for k in range(1, T)):
            for s, t in itertools.product(itertools.product((0, 1), repeat=len(A)), repeat=2):
                def vec(pat):
                    it = iter(pat); return kron([(A1 if next(it) == 0 else B1) if c in A else psi1 for c in range(T)])
                d = sum(x != y for x, y in zip(s, t))
                assert np.sum(np.abs(L.conj() @ vec(s)) * np.abs(L.conj() @ vec(t))) <= q ** d + 1e-10
        prob = lambda R: np.real(np.einsum('li,ij,lj->l', L.conj(), R, L))
        Ppsi, Prho = prob(tens(P1)), prob(tens(rho1))
        assert abs(Ppsi.sum() - 1) < 1e-10 and abs(Prho.sum() - 1) < 1e-10
        assert np.abs(Ppsi - Prho).sum() <= (1 + q) ** T - 1 + 1e-10
        for eps in (0.02, 0.1, 0.3, 0.5):
            Ps = prob(tens((1 - 2 * eps) * P1 + 2 * eps * rho1)); assert np.abs(Ppsi - Ps).sum() <= (1 + 2 * eps * q) ** T - 1 + 1e-10
        for s in (0.05, 0.25, 0.5, 1.0):
            Ps = prob(tens((1 - s) * rho1 + s * P1)); assert np.abs(Ps - Prho).sum() <= (1 + s * q) ** T - 1 + 1e-10
    print(f"n={n}, T={T}: 40 interleaved trees, all asserts passed; q = {q:.4f}, (1+q)^T - 1 = {(1 + q) ** T - 1:.4f}")
