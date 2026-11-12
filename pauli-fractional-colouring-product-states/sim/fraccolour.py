# Checks for fractional colourings of the anticommutation graph of B_eps(rho) = {P : |tr(rho P)| >= eps}, with asserts.
#  (1) product states of single qubits (random mixed or pure, n <= 3): chi_f(G(B_eps)) <= eps^-2 (Proposition 1),
#      computed exactly by linear programming over all maximal commuting sets, and the product-basis colouring of the
#      proof covers every P in B_eps with weight at least 1;
#  (2) for comparison, chi_f eps^2 for random pure states on 2 and 3 qubits, with the linear programming duality bound
#      chi_f eps^2 <= sum_P y_P tr(rho P)^2 for an optimal dual solution y (weight at most 1 on every commuting set);
#  (3) the constant 1 of Proposition 1 is attained: one qubit with <X> = <Z> = 1/sqrt2 at eps = 1/sqrt2.
# python -I fraccolour.py
import itertools
import numpy as np
from scipy.optimize import linprog

rng = np.random.default_rng(3)
I2 = np.eye(2); X = np.array([[0, 1], [1, 0]]); Y = np.array([[0, -1j], [1j, 0]]); Z = np.diag([1.0, -1])
PAULI = [I2, X, Y, Z]


def mat(word):
    M = np.array([[1.0 + 0j]])
    for a in word:
        M = np.kron(M, PAULI[a])
    return M


def commute(p, q):
    return sum(1 for a, b in zip(p, q) if a and b and a != b) % 2 == 0


def maximal_commuting_sets(V):
    """Maximal independent sets of the anticommutation graph = maximal cliques of the commutation graph."""
    n = len(V)
    adj = [{j for j in range(n) if j != i and commute(V[i], V[j])} for i in range(n)]
    out = []

    def bk(R, P, Xs):
        if not P and not Xs:
            out.append(R); return
        u = max(P | Xs, key=lambda v: len(adj[v] & P))
        for v in list(P - adj[u]):
            bk(R | {v}, P & adj[v], Xs & adj[v]); P = P - {v}; Xs = Xs | {v}

    bk(set(), set(range(n)), set())
    return out


def chi_f(V):
    """Fractional chromatic number and an optimal dual vertex weighting y."""
    sets = maximal_commuting_sets(V)
    A = np.zeros((len(V), len(sets)))
    for j, S in enumerate(sets):
        for i in S:
            A[i, j] = 1
    primal = linprog(np.ones(len(sets)), A_ub=-A, b_ub=-np.ones(len(V)), bounds=(0, None), method="highs")
    dual = linprog(-np.ones(len(V)), A_ub=A.T, b_ub=np.ones(len(sets)), bounds=(0, None), method="highs")
    assert primal.status == 0 and dual.status == 0
    assert abs(primal.fun + dual.fun) < 1e-7
    return primal.fun, dual.x, sets


def B_eps(rho, n, eps):
    V, ex = [], []
    for w in itertools.product(range(4), repeat=n):
        e = np.trace(rho @ mat(w)).real
        if abs(e) >= eps - 1e-12:
            V.append(w); ex.append(e)
    return V, np.array(ex)


def rand_qubit(pure):
    v = rng.normal(size=3); v /= np.linalg.norm(v)
    if not pure:
        v *= rng.random() ** 0.5
    return (I2 + v[0] * X + v[1] * Y + v[2] * Z) / 2, v


worst = 0.0
for n in (1, 2, 3):
    for trial in range(12 if n < 3 else 6):
        qs = [rand_qubit(pure=trial % 2 == 0) for _ in range(n)]
        rho = qs[0][0]
        for q in qs[1:]:
            rho = np.kron(rho, q[0])
        for eps in (0.2, 0.35, 0.5, 0.7):
            V, ex = B_eps(rho, n, eps)
            cf, y, _ = chi_f(V)
            assert cf * eps ** 2 <= 1 + 1e-7, (n, eps, cf)
            worst = max(worst, cf * eps ** 2)
            # the colouring of the proof: product bases sigma with q_i(sigma) = <sigma>^2 / |v_i|^2
            cover = np.zeros(len(V))
            for bases in itertools.product((1, 2, 3), repeat=n):
                pr = 1.0
                for (r, v), b in zip(qs, bases):
                    s = (v ** 2).sum()
                    pr *= v[b - 1] ** 2 / s if s > 1e-15 else 1 / 3
                for i, w in enumerate(V):
                    if all(a == 0 or a == b for a, b in zip(w, bases)):
                        cover[i] += pr
            assert np.all(cover * eps ** -2 >= 1 - 1e-9)
            # duality: chi_f eps^2 = eps^2 sum y <= sum y <P>^2, and y is feasible (every commuting set has weight <= 1)
            assert cf * eps ** 2 <= (y * ex ** 2).sum() + 1e-7
print(f"product states, n <= 3: chi_f eps^2 <= 1 in all cases (largest {worst:.4f})")

# (2) entangled states for comparison
for n in (2, 3):
    vals = []
    for trial in range(6):
        g = rng.normal(size=(2 ** n,)) + 1j * rng.normal(size=(2 ** n,)); g /= np.linalg.norm(g)
        rho = np.outer(g, g.conj())
        for eps in (0.2, 0.35, 0.5):
            V, ex = B_eps(rho, n, eps)
            cf, y, sets = chi_f(V)
            assert cf * eps ** 2 <= (y * ex ** 2).sum() + 1e-7
            assert np.all(np.array([[1.0 if i in S else 0.0 for i in range(len(V))] for S in sets]) @ y <= 1 + 1e-7)
            vals.append(cf * eps ** 2)
    print(f"random pure states, n = {n}: chi_f eps^2 in [{min(vals):.3f}, {max(vals):.3f}]")
rho = (I2 + (X + Z) / np.sqrt(2)) / 2
V, ex = B_eps(rho, 1, 1 / np.sqrt(2))
cf, _, _ = chi_f(V)
assert sorted(V) == [(0,), (1,), (3,)] and abs(cf * 0.5 - 1) < 1e-9
print("one qubit, <X> = <Z> = 1/sqrt2, eps = 1/sqrt2: chi_f eps^2 = 1")
print("fractional colouring checks: ok")
