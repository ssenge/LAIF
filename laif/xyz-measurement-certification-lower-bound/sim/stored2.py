"""Second moment for stored copies (README, Theorem 2): for random fully adaptive trees on all nT qubits of T stored
copies (any order), asserts chi^2(P_{rho_s^T} || P_{rho^T}) <= (1 + s^2 q)^T - 1, q = (2/3)^{n/2}, with both outcome
laws computed from the density matrices, for s in {0.05, 0.2, 0.5, 1} and
(n, T) in {(1,1),(1,2),(1,3),(1,4),(2,1),(2,2),(2,3),(3,1),(3,2)}. Also asserts the product form
P_s / P_0 = prod_t (1 + s r_t) at every leaf. Prints the largest ratio chi^2 / ((1 + s^2 q)^T - 1).
The phase of abar is the one returned by numpy.linalg.eigh."""
import numpy as np
rng = np.random.default_rng(5)
r = np.ones(3) / np.sqrt(3)
X = np.array([[0, 1], [1, 0]]); Y = np.array([[0, -1j], [1j, 0]]); Z = np.diag([1., -1])
w, V = np.linalg.eigh((np.eye(2) + r[0] * X + r[1] * Y + r[2] * Z) / 2); a, b = V[:, 1], V[:, 0]
BAS = {nm: np.linalg.eigh(P)[1].T.conj() for nm, P in (('X', X), ('Y', Y), ('Z', Z))}
def kron(vs):
    out = np.array([1.0 + 0j])
    for v in vs: out = np.kron(out, v)
    return out
def kronm(ms):
    out = np.array([[1.0 + 0j]])
    for m in ms: out = np.kron(out, m)
    return out
def leaves(N):
    out = []
    def rec(fixed):
        if len(fixed) == N: out.append([fixed[i] for i in range(N)]); return
        free = [i for i in range(N) if i not in fixed]; qb = free[rng.integers(len(free))]; ax = 'XYZ'[rng.integers(3)]
        for x in range(2):
            f = dict(fixed); f[qb] = BAS[ax][x].conj(); rec(f)
    rec({}); return out
worst = 0
for n, T in [(1, 1), (1, 2), (1, 3), (1, 4), (2, 1), (2, 2), (2, 3), (3, 1), (3, 2)]:
    q = (2 / 3) ** (n / 2); A1, B1 = kron([a] * n), kron([b] * n)
    psi = (A1 + B1) / np.sqrt(2); rho = (np.outer(A1, A1.conj()) + np.outer(B1, B1.conj())) / 2
    for _ in range(40):
        Lv = leaves(n * T); L = np.array([kron(e) for e in Lv])
        prob = lambda R: np.real(np.einsum('li,ij,lj->l', L.conj(), R, L))
        P0 = prob(kronm([rho] * T))
        for s in (0.05, 0.2, 0.5, 1.0):
            Ps = prob(kronm([(1 - s) * rho + s * np.outer(psi, psi.conj())] * T))
            for l, e in enumerate(Lv):                      # product form of the likelihood ratio
                ratio = 1.0
                for t in range(T):
                    u = np.prod([e[t * n + i].conj() @ a for i in range(n)]); v = np.prod([e[t * n + i].conj() @ b for i in range(n)])
                    m = (abs(u) ** 2 + abs(v) ** 2) / 2; ratio *= 1 + s * (u * np.conj(v)).real / m
                assert abs(Ps[l] - P0[l] * ratio) < 1e-12
            chi = np.sum((Ps - P0) ** 2 / P0); bound = (1 + s * s * q) ** T - 1
            assert chi <= bound + 1e-12; worst = max(worst, chi / bound)
    print(f"n={n}, T={T}: all asserts passed", flush=True)
print(f"largest chi^2 / ((1 + s^2 q)^T - 1) = {worst:.4f}")
