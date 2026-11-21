"""The post-processing of arXiv:2506.07866 applied to uniform random samples instead of quantum samples: S = 2000 uniform
random bitstrings over the free turn and contact qubits, the best 5% by energy, then up to three sweeps of zero-temperature
single-flip descent (a flip is kept when it does not raise the energy) on each. Energy: fold_exact (the Hamiltonian of the
qiskit-nature ProteinFoldingProblem, main chain only). Reports, over R independent repetitions, how often the best
post-processed energy equals the exact ground state.
Usage: python -I pp_random.py SEQ R [S frac sweeps]   |   python -I pp_random.py test"""
import os, sys, json
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import numpy as np
from numba import njit
from fold_exact import tables, run

@njit(cache=True)
def full_energy(tb, q, pairs, npair, l0, const, pb, l1):
    """tb: free turn qubits (b0 of turn 2, then (b0, b1) of turns 3..N-2); q: contact qubits."""
    M = (tb.shape[0] + 1) // 2 + 2; N = M + 1; t = np.zeros(M, np.int64); t[0] = 1; t[1] = 0     # 2N - 7 free turn qubits, N - 1 turns
    t[2] = 2 * tb[0] + 1                                        # (b0, b1) = (free, 1): turn 1 or 3
    for k in range(3, M): t[k] = 2 * tb[1 + 2 * (k - 3)] + tb[2 + 2 * (k - 3)]     # indicators f0..f3 of (b0, b1)
    P = np.zeros((N, 4), np.int64)
    for m in range(1, N):
        for a in range(4): P[m, a] = P[m - 1, a]
        P[m, t[m - 1]] += 1 if m % 2 == 0 else -1
    E = 0.0
    for k in range(N - 2):
        if t[k] == t[k + 1]: E += pb
    for c in range(pairs.shape[0]):
        if q[c] == 0: continue
        B = const[c]
        for n in range(npair[c]):
            i, j = pairs[c, n, 0], pairs[c, n, 1]; x = 0
            for a in range(4):
                d = P[j - 1, a] - P[i - 1, a]; x += d * d
            B += l0[c] * (x - 1) if n == 0 else -l1 * x
        E += B
    return E

@njit(cache=True)
def descend(tb, q, pairs, npair, l0, const, pb, l1, sweeps):
    E = full_energy(tb, q, pairs, npair, l0, const, pb, l1)
    for _ in range(sweeps):
        moved = False
        for k in range(tb.shape[0] + q.shape[0]):
            if k < tb.shape[0]: tb[k] ^= 1
            else: q[k - tb.shape[0]] ^= 1
            E2 = full_energy(tb, q, pairs, npair, l0, const, pb, l1)
            if E2 <= E:
                if E2 < E: moved = True
                E = E2
            elif k < tb.shape[0]: tb[k] ^= 1
            else: q[k - tb.shape[0]] ^= 1
        if not moved: break
    return E

@njit(cache=True)
def one_rep(seed, ng, nc, S, keep, sweeps, pairs, npair, l0, const, pb, l1):
    np.random.seed(seed); T = np.random.randint(0, 2, (S, ng)); Q = np.random.randint(0, 2, (S, nc)); E = np.empty(S)
    for s in range(S): E[s] = full_energy(T[s], Q[s], pairs, npair, l0, const, pb, l1)
    order = np.argsort(E); best = 1e18; raw = E[order[0]]
    for r in range(keep):
        s = order[r]; e = descend(T[s].copy(), Q[s].copy(), pairs, npair, l0, const, pb, l1, sweeps)
        if e < best: best = e
    return raw, best

def main(seq, R, S=2000, frac=0.05, sweeps=3, pb=10.0, l1=10.0):
    ex = run(seq, pb, l1); C, pairs, npair, l0, const = tables(seq, l1); N = len(seq); ng, nc = 2 * N - 7, len(C)
    keep = int(round(frac * S)); raws, bests = [], []
    for r in range(R):
        raw, best = one_rep(r, ng, nc, S, keep, sweeps, pairs, npair, l0, const, pb, l1); raws.append(raw); bests.append(best)
    bests = np.array(bests); hit = np.abs(bests - ex["E"]) < 1e-9
    return dict(seq=seq, qubits=ng + nc, E_exact=ex["E"], R=R, S=S, keep=keep, sweeps=sweeps, hits=int(hit.sum()),
                best_raw_median=float(np.median(raws)), best_pp_median=float(np.median(bests)), best_pp_min=float(bests.min()))

if __name__ == "__main__":
    if sys.argv[1] == "test":                                   # full_energy minimized over contacts = fold_exact's energy
        from fold_exact import energy_of_turns
        rng = np.random.default_rng(0); seq = "GYDPETGTWG"; C, pairs, npair, l0, const = tables(seq, 10.0); ng, nc = 13, len(C)
        for _ in range(200):
            tb = rng.integers(0, 2, ng); M = 9; t = [1, 0, 3 if tb[0] else 1] + [int(2 * tb[1 + 2 * k] + tb[2 + 2 * k]) for k in range(M - 3)]
            e_min = energy_of_turns(np.array(t, np.int64), pairs, npair, l0, const, 10.0, 10.0)
            best = min(full_energy(tb, np.array(qq), pairs, npair, l0, const, 10.0, 10.0)
                       for qq in np.ndindex(*(2,) * nc))
            assert abs(best - e_min) < 1e-9
        r = main(seq, 2); assert r["best_pp_min"] >= r["E_exact"] - 1e-9          # descent never goes below the ground state
        print("pp_random self-checks passed"); sys.exit()
    a = sys.argv[3:]; print(json.dumps(main(sys.argv[1], int(sys.argv[2]), *(float(x) if "." in x else int(x) for x in a))))
