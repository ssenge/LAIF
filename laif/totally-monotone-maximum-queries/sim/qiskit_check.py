"""The flat algorithm on small matrices, with every search a Qiskit circuit run in Aer.

Registers: index and value (the entry, as a rank among distinct entries). One oracle application is a QROM built
from multi-controlled X gates. Between compute and uncompute, a diagonal gate marks "value above the current best",
a classical test that costs no queries. Nothing peeks: each search spends its budget before giving up.
Also the hidden-bit family, showing the search finds a single raised diagonal entry among the n^(3/2) cells.
Limits: noiseless simulation of tiny instances, at most MAX_QUBITS. It tests the construction, not asymptotics.
Run with python qiskit_check.py (numpy, scipy, networkx; qiskit and qiskit-aer for the circuits)
"""
import math
import sys
import numpy as np
from qiskit import QuantumCircuit
from qiskit.circuit.library import DiagonalGate, XGate
from qiskit_aer import AerSimulator
from monge import random_monge, hard, convex_polygon, dist2

MAX_QUBITS = 14
SIM = AerSimulator(method="statevector")
used = {"qubits": 0, "circuits": 0, "applications": 0}


def bits(x):
    return max(1, math.ceil(math.log2(x))) if x > 1 else 1


def qrom(table, ni, nv):
    qc = QuantumCircuit(ni + nv)
    for i, val in enumerate(table):
        for b in range(nv):
            if val >> b & 1:
                qc.append(XGate().control(ni, ctrl_state=i), list(range(ni)) + [ni + b])
    return qc


def circuit(table, phase, ni, nv, j):
    q = qrom(table, ni, nv)
    mark = q.copy()
    mark.append(DiagonalGate(phase.tolist()), range(ni + nv))
    mark = mark.compose(q.inverse())
    diff = QuantumCircuit(ni + nv)
    diff.h(range(ni))
    diff.x(range(ni))
    if ni == 1:
        diff.z(0)
    else:
        diff.h(ni - 1)
        diff.mcx(list(range(ni - 1)), ni - 1)
        diff.h(ni - 1)
    diff.x(range(ni))
    diff.h(range(ni))
    qc = QuantumCircuit(ni + nv, ni)
    qc.h(range(ni))
    for _ in range(j):
        qc = qc.compose(mark).compose(diff)
    qc.measure(range(ni), range(ni))
    return qc


def dh_max(vals, rng, budget=24):
    """Durr-Hoyer maximum over vals, each search a circuit. Returns the index found."""
    N = len(vals)
    if N == 1:
        return 0
    distinct = np.unique(vals)
    ni, nv = bits(N), bits(len(distinct))
    assert ni + nv <= MAX_QUBITS, f"would need {ni + nv} qubits"
    used["qubits"] = max(used["qubits"], ni + nv)
    ranks = np.searchsorted(distinct, vals).tolist()
    table = ranks + [0] * (2 ** ni - N)
    cur = int(rng.integers(N))
    limit = budget * math.sqrt(N)
    spent = 1
    while spent <= limit:
        phase = np.ones(2 ** (ni + nv), dtype=complex)
        for i in range(N):
            if ranks[i] > ranks[cur]:
                phase[i | (ranks[i] << ni)] = -1
        m, found = 1.0, None
        while found is None and spent <= limit:
            j = int(rng.integers(0, int(m)))
            r = SIM.run(circuit(table, phase, ni, nv, j), shots=1, seed_simulator=int(rng.integers(1 << 31))).result()
            x = int(next(iter(r.get_counts())), 2)
            used["circuits"] += 1
            spent += 2 * j + 1
            if x < N and ranks[x] > ranks[cur]:
                found = x
            m = min(m * 8 / 7, math.sqrt(N) + 1)
        if found is not None:
            cur = found
    used["applications"] += spent
    return cur


def flat(M, rng):
    n, c = M.shape
    k = max(1, round(math.sqrt(n)))
    segs, best = [], -np.inf

    def rec(a, b, l, u, k):
        nonlocal best
        if a > b:
            return
        if k <= 0:
            segs.append((a, b, l, u))
            return
        i = (a + b) // 2
        p = l + dh_max(M[i, l:u + 1], rng)
        best = max(best, M[i, p])
        rec(a, i - 1, l, p, (k - 1) // 2)
        rec(i + 1, b, p, u, k - 1 - (k - 1) // 2)

    rec(0, n - 1, 0, c - 1, k)
    if segs:
        cells = np.concatenate([M[a:b + 1, l:u + 1].ravel() for a, b, l, u in segs])
        best = max(best, cells[dh_max(cells, rng)])
    return best


def main():
    rng = np.random.default_rng(11)
    runs = wrong = 0
    print(f"{'instance':16} {'n':>2} {'found':>9} {'true':>9} {'classical reads':>15}")
    insts = []
    for n, s in ((4, 0), (6, 1), (8, 2), (8, 3)):
        insts.append(("monge", n, random_monge(n, s)))
    for n, b in ((6, 2), (8, 0), (8, 5), (8, 7)):
        insts.append(("hidden bit", n, hard(n, (np.arange(n) == b).astype(np.int64))))
    insts.append(("hidden bit none", 8, hard(8, np.zeros(8, dtype=np.int64))))
    P = convex_polygon(12, 3)
    insts.append(("polygon chains", len(P) // 2, dist2(P[: len(P) // 2], P[len(P) // 2:])))
    for name, n, M in insts:
        for seed in range(3):
            v = flat(M, rng)
            runs += 1
            wrong += v != M.max()
            print(f"{name:16} {n:2} {int(v):9} {int(M.max()):9} {M.size:15}", flush=True)
    print(f"\n{runs} runs, {wrong} wrong; at most {used['qubits']} qubits; {used['circuits']} circuits; {used['applications']} oracle applications")
    return wrong


if __name__ == "__main__":
    sys.exit(1 if main() else 0)
