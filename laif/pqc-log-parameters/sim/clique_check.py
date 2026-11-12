"""Checks ../README.md: the circuit of the reduction from M-Clique to PQC optimization with M parameters.

Register j has s qubits, starts in the uniform superposition, gets the gates exp(-i theta_j 2^q n_q) on its qubits
(n_q = |1><1| on qubit q, integer spectra), then the quantum frequency transform |x> -> sum_u e^{2 pi i x u / m} |u> / sqrt(m). The observable is the fraction of the
pairs j < j' whose outcomes u_j, u_j' are equal or not adjacent in the graph.

1. A state vector simulation agrees with the closed form: outcome u of register j has probability
   F_m(theta_j - 2 pi u / m), with F_m(t) = sin^2(m t / 2) / (m^2 sin^2(t / 2)) and m = 2^s.
2. With an M-clique (v_1, ..., v_M), theta_j = 2 pi v_j / m gives f = 0.
3. Without an M-clique, f(theta) >= 1 / C(M, 2) at every theta (checked on random points and after local
   minimization; the proof is one line: every outcome has a bad pair).
4. The outcome law is a product of M laws on m values, so it can be sampled classically: the empirical mean of
   O over classical samples matches f.
"""
import itertools
import numpy as np
from scipy.optimize import minimize


def kernel(m, t):
    t = np.asarray(t, dtype=float)
    s = np.sin(t / 2)
    out = np.ones_like(t)
    nz = np.abs(s) > 1e-12
    out[nz] = np.sin(m * t[nz] / 2) ** 2 / (m ** 2 * s[nz] ** 2)
    return out


def probs(m, theta):
    return kernel(m, theta - 2 * np.pi * np.arange(m) / m)


def f_closed(adj, theta):
    M, m = len(theta), adj.shape[0]
    P = [probs(m, t) for t in theta]
    bad = 1 - adj                                           # adj has zero diagonal, so equal outcomes are bad
    return sum(P[j] @ bad @ P[k] for j, k in itertools.combinations(range(M), 2)) / (M * (M - 1) / 2)


def f_statevector(adj, theta, s):
    """Simulate the circuit on M * s qubits."""
    m = 2 ** s
    regs = []
    for t in theta:
        psi = np.ones(m, dtype=complex) / np.sqrt(m)           # gate H on each qubit
        for q in range(s):                                    # exp(-i t 2^q n_q), qubit q = bit q of the index
            bit = (np.arange(m) >> q) & 1
            psi = psi * np.exp(-1j * t * 2 ** q * bit)
        idft = np.exp(2j * np.pi * np.outer(np.arange(m), np.arange(m)) / m) / np.sqrt(m)
        regs.append(idft @ psi)                               # quantum frequency transform
    state = regs[0]
    for r in regs[1:]:
        state = np.kron(state, r)
    p = np.abs(state) ** 2
    M = len(theta)
    val = 0.0
    for idx, pr in enumerate(p):
        if pr < 1e-15:
            continue
        u = [(idx >> (s * (M - 1 - j))) & (m - 1) for j in range(M)]
        val += pr * sum(1 - adj[u[j], u[k]] for j, k in itertools.combinations(range(M), 2))
    return val / (M * (M - 1) / 2)


rng = np.random.default_rng(0)
s, M = 3, 3
m = 2 ** s
for trial in range(3):
    A = np.triu((rng.random((m, m)) < 0.5).astype(int), 1); A = A + A.T
    th = rng.uniform(-np.pi, np.pi, M)
    assert abs(f_closed(A, th) - f_statevector(A, th, s)) < 1e-12
print(f"1. state vector simulation on {M * s} qubits agrees with the closed form (3 random graphs and angles)")

# graph on 8 vertices with a 4-clique {0, 2, 5, 7}
M = 4
A = np.zeros((m, m), dtype=int)
for u, v in itertools.combinations([0, 2, 5, 7], 2):
    A[u, v] = A[v, u] = 1
A[1, 3] = A[3, 1] = A[3, 4] = A[4, 3] = 1
theta = 2 * np.pi * np.array([0, 2, 5, 7]) / m
assert f_closed(A, theta) < 1e-15
print(f"2. graph with a 4-clique: f = {f_closed(A, theta):.1e} at theta = 2 pi (0, 2, 5, 7) / 8")

# a graph on 8 vertices without a 4-clique: the 8-cycle with its chords of length 2 (clique number 3)
B = np.zeros((m, m), dtype=int)
for u in range(m):
    for d in (1, 2):
        B[u, (u + d) % m] = B[(u + d) % m, u] = 1
assert not any(all(B[u, v] for u, v in itertools.combinations(S, 2)) for S in itertools.combinations(range(m), 4))
assert any(all(B[u, v] for u, v in itertools.combinations(S, 2)) for S in itertools.combinations(range(m), 3))
low = 1 / (M * (M - 1) / 2)
vals = [f_closed(B, rng.uniform(-np.pi, np.pi, M)) for _ in range(2000)]
mins = [minimize(lambda t: f_closed(B, t), rng.uniform(-np.pi, np.pi, M), method="Nelder-Mead",
                 options={"xatol": 1e-10, "fatol": 1e-12, "maxiter": 4000}).fun for _ in range(100)]
assert min(vals) >= low - 1e-12 and min(mins) >= low - 1e-9
print(f"3. graph without a 4-clique: min f over 2000 random points {min(vals):.4f}, after 100 local minimizations "
      f"{min(mins):.4f}, bound 1/C(4,2) = {low:.4f}")
th = rng.uniform(-np.pi, np.pi, M)
P = [probs(m, t) for t in th]
S = np.array([rng.choice(m, size=200000, p=p / p.sum()) for p in P])
emp = np.mean(sum(1 - B[S[j], S[k]] for j, k in itertools.combinations(range(M), 2))) / (M * (M - 1) / 2)
assert abs(emp - f_closed(B, th)) < 5e-3
print(f"4. classical sampling: mean of O over 200000 samples {emp:.4f}, f = {f_closed(B, th):.4f}")
print("reduction checks pass")
