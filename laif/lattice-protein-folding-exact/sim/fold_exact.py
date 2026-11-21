"""Exact ground state of the lattice protein-folding Hamiltonian of the dense tetrahedral encoding (main chain only, no side
chains), term by term as in the qiskit-nature 0.4.5 ProteinFoldingProblem (qubit_op_builder.py, distance_map.py,
qubit_fixing.py), with the residue pair contact energies of mj_matrix.txt from that package (Apache-2.0,
LICENSE-mj_matrix.txt).

Variables. Turn t_k in {0,1,2,3} after bead k (k = 0..N-2), two qubits (b0, b1) per turn with indicators
f0 = (1-b0)(1-b1), f1 = b1(1-b0), f2 = b0(1-b1), f3 = b0 b1. Fixed: t_0 = 1, t_1 = 0, t_2 in {1, 3} (qubits 0..3 and 5),
so 2N - 7 free turn qubits. One contact qubit q_ij in {0,1} per pair of beads (1-indexed) with 1 <= i <= N-4,
j >= i + 5 and j - i odd.
Energy.  H = H_back + sum_ij q_ij B_ij(t), with
  H_back = pb * sum_{k=0}^{N-3} [t_k == t_{k+1}],
  P_m = sum_{k=1}^{m} (-1)^k e_{t_{k-1}} in Z^4, x(i,j) = |P_{j-1} - P_{i-1}|^2,
  B_ij = l0 (x(i,j) - 1) + 0.1 e_ij + sum_{(k,l) in {(i-1,j),(i+1,j),(i,j-1),(i,j+1)}, 1 <= k < l <= N} [l1 (2 - x(k,l)) + 0.1 e_kl],
  l0 = 7 (j - i + 1) l1, e = contact energy of the residue pair.
B_ij depends on the turns only, so min over contacts is sum_ij min(0, B_ij): the ground state is the minimum over the
2^(2N-7) turn assignments of H_back + sum min(0, B_ij). This is computed by depth-first enumeration of all of them.
Usage: python -I fold_exact.py SEQ [pb l1]   |   python -I fold_exact.py test"""
import os, sys, itertools, time
import numpy as np
from numba import njit

AA = "CMFILVWYAGTSNQDEHRKP"

def mj():
    p = os.path.join(os.path.dirname(os.path.abspath(__file__)), "mj_matrix.txt")
    rows = [l.split() for l in open(p) if l.strip()]
    sym = rows[0]; assert "".join(sym) == AA
    M = np.zeros((20, 20))
    for r, row in enumerate(rows[1:]):
        for c in range(r, 20): M[r, c] = float(row[c])          # upper triangle including the diagonal
    return M

def pair_energies(seq):
    """e[i, j] for 1-indexed i < j, as calculate_energy_matrix: mj[min(a_i, a_j), max(a_i, a_j)]."""
    M = mj(); N = len(seq); e = np.zeros((N + 2, N + 2))
    for i in range(1, N + 1):
        for j in range(i + 1, N + 1):
            a, b = AA.index(seq[i - 1]), AA.index(seq[j - 1]); e[i, j] = M[min(a, b), max(a, b)]
    return e

def contacts(N):
    return [(i, j) for i in range(1, N - 3) for j in range(i + 5, N + 1) if (j - i) % 2 == 1]

def tables(seq, l1):
    """For each contact: l0, the constant part 0.1 (e_ij + sum e_kl) + l1 * 2 * (number of neighbour pairs), and the pairs."""
    N = len(seq); e = pair_energies(seq); C = contacts(N); K = len(C)
    pairs = np.zeros((K, 5, 2), np.int64); npair = np.zeros(K, np.int64); l0 = np.zeros(K); const = np.zeros(K)
    for c, (i, j) in enumerate(C):
        l0[c] = 7 * (j - i + 1) * l1; const[c] = 0.1 * e[i, j]; pairs[c, 0] = (i, j); n = 1
        for k, l in ((i - 1, j), (i + 1, j), (i, j - 1), (i, j + 1)):
            if 1 <= k < l <= N:                                 # the other cases raise and are skipped there
                pairs[c, n] = (k, l); const[c] += 0.1 * e[k, l] + 2 * l1; n += 1
        npair[c] = n
    return C, pairs, npair, l0, const

@njit(cache=True)
def energy_of_turns(t, pairs, npair, l0, const, pb, l1):
    N = t.shape[0] + 1; P = np.zeros((N, 4), np.int64)
    for m in range(1, N):
        for a in range(4): P[m, a] = P[m - 1, a]
        P[m, t[m - 1]] += 1 if m % 2 == 0 else -1
    E = 0.0
    for k in range(N - 2):
        if t[k] == t[k + 1]: E += pb
    for c in range(pairs.shape[0]):
        B = const[c]
        for n in range(npair[c]):
            i, j = pairs[c, n, 0], pairs[c, n, 1]; x = 0
            for a in range(4):
                d = P[j - 1, a] - P[i - 1, a]; x += d * d
            B += l0[c] * (x - 1) if n == 0 else -l1 * x
        if B < 0: E += B
    return E

@njit(cache=True)
def search(N, pairs, npair, l0, const, pb, l1):
    """All 2 * 4^(N-4) turn sequences with t0 = 1, t1 = 0, t2 in {1, 3}: minimum, its turns, how many attain it."""
    M = N - 1; t = np.zeros(M, np.int64); t[0] = 1; t[1] = 0
    best = 1e18; arg = np.zeros(M, np.int64); cnt = 0; total = 0
    rest = M - 3
    for t2 in (1, 3):
        t[2] = t2
        for code in range(4 ** rest):
            x = code
            for k in range(rest): t[3 + k] = x % 4; x //= 4
            E = energy_of_turns(t, pairs, npair, l0, const, pb, l1); total += 1
            if E < best - 1e-9: best = E; arg[:] = t; cnt = 1
            elif abs(E - best) <= 1e-9: cnt += 1
    return best, arg, cnt, total

def positions(t):
    """Real diamond-lattice positions in the same convention: P_m in Z^4; two beads coincide iff their P are equal."""
    N = len(t) + 1; P = np.zeros((N, 4), np.int64)
    for m in range(1, N): P[m] = P[m - 1]; P[m, t[m - 1]] += 1 if m % 2 == 0 else -1
    return P

def analyse(seq, t, pb, l1):
    C, pairs, npair, l0, const = tables(seq, l1); P = positions(t); e = pair_energies(seq)
    selfavoid = len({tuple(p) for p in P}) == len(P)
    backtrack = sum(t[k] == t[k + 1] for k in range(len(t) - 1))
    on = []
    for c, (i, j) in enumerate(C):
        B = const[c]
        for n in range(npair[c]):
            a, b = pairs[c, n]; x = int(((P[b - 1] - P[a - 1]) ** 2).sum()); B += l0[c] * (x - 1) if n == 0 else -l1 * x
        if B < 0: on.append((i, j, round(B, 4)))
    return dict(selfavoid=selfavoid, backtrack=int(backtrack), contacts=on)

def brute(seq, pb, l1):
    """Independent check: minimum over all turn qubits and all contact qubits jointly (small N only)."""
    N = len(seq); C, pairs, npair, l0, const = tables(seq, l1); best = 1e18
    for t2 in (1, 3):
        for rest in itertools.product(range(4), repeat=N - 4):
            t = np.array([1, 0, t2, *rest], np.int64); P = positions(t)
            hb = pb * sum(t[k] == t[k + 1] for k in range(N - 2))
            Bs = []
            for c in range(len(C)):
                B = const[c]
                for n in range(npair[c]):
                    a, b = pairs[c, n]; x = int(((P[b - 1] - P[a - 1]) ** 2).sum()); B += l0[c] * (x - 1) if n == 0 else -l1 * x
                Bs.append(B)
            for q in itertools.product((0, 1), repeat=len(C)):
                best = min(best, hb + sum(qq * B for qq, B in zip(q, Bs)))
    return best

def run(seq, pb=10.0, l1=10.0):
    N = len(seq); C, pairs, npair, l0, const = tables(seq, l1); t0 = time.perf_counter()
    best, arg, cnt, total = search(N, pairs, npair, l0, const, pb, l1)
    return dict(seq=seq, N=N, qubits=2 * N - 7 + len(C), n_geom=2 * N - 7, n_contact=len(C), pb=pb, l1=l1, E=best,
                turns=arg.tolist(), degenerate=int(cnt), enumerated=int(total), t=time.perf_counter() - t0, **analyse(seq, arg, pb, l1))

if __name__ == "__main__":
    if sys.argv[1] == "test":
        for N, nc in ((14, 25), (15, 30), (16, 36)): assert len(contacts(N)) == nc and 2 * N - 7 + nc == {14: 46, 15: 53, 16: 61}[N]
        rng = np.random.default_rng(0)
        for N in (8, 9):                                          # 3 and 6 contact qubits
            for _ in range(3):
                seq = "".join(rng.choice(list(AA), N)); r = run(seq)
                assert abs(r["E"] - brute(seq, 10.0, 10.0)) < 1e-9, seq
        P = positions(np.array([1, 0, 1, 0], np.int64)); assert len({tuple(p) for p in P}) == 5
        P = positions(np.array([1, 1], np.int64)); assert (P[2] == P[0]).all()              # backtracking returns to bead 0
        print("fold_exact self-checks passed"); sys.exit()
    a = sys.argv[2:]; import json; print(json.dumps(run(sys.argv[1], *map(float, a))))
