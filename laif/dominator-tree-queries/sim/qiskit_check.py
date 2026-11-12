"""The dominator algorithm on small graphs, with every search and minimum finding a Qiskit circuit run in Aer.

One iteration computes the marked bit by a QROM (one oracle application in the count, as in dom.py), applies Z and
uncomputes. Nothing peeks: each call spends its budget before giving up. Marks are built from the classical values.
Limits: noiseless simulation of tiny instances, at most MAX_QUBITS. It tests the construction, not asymptotics.
Run with python qiskit_check.py (numpy; qiskit and qiskit-aer for the circuits)
"""
import math
import sys
import numpy as np
import networkx as nx
from qiskit import QuantumCircuit
from qiskit.circuit.library import XGate
from qiskit_aer import AerSimulator
from dom import G, dominators, strong

MAX_QUBITS = 6
SIM = AerSimulator(method="statevector")
used = {"qubits": 0, "circuits": 0}


def circuit(marked, ni, j):
    oracle = QuantumCircuit(ni + 1)
    for i in np.flatnonzero(marked):
        oracle.append(XGate().control(ni, ctrl_state=int(i)), list(range(ni + 1)))
    mark = oracle.copy()
    mark.z(ni)
    mark = mark.compose(oracle.inverse())
    diff = QuantumCircuit(ni + 1)
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
    qc = QuantumCircuit(ni + 1, ni)
    qc.h(range(ni))
    for _ in range(j):
        qc = qc.compose(mark).compose(diff)
    qc.measure(range(ni), range(ni))
    return qc


class CircuitG(G):
    def _bbht(self, marked, limit, spent):
        N = len(marked)
        ni = max(1, math.ceil(math.log2(N)))
        assert ni + 1 <= MAX_QUBITS, f"would need {ni + 1} qubits"
        used["qubits"] = max(used["qubits"], ni + 1)
        table = np.zeros(2 ** ni, dtype=bool)
        table[:N] = marked
        m = 1.0
        while spent <= limit:
            j = int(self.rng.integers(0, int(m)))
            r = SIM.run(circuit(table, ni, j), shots=1, seed_simulator=int(self.rng.integers(1 << 31))).result()
            x = int(next(iter(r.get_counts())), 2)
            used["circuits"] += 1
            spent += 2 * j + 1
            if x < N and marked[x]:
                return x, spent
            m = min(m * 8 / 7, math.sqrt(N) + 1)
        return None, spent

    def search(self, v, d, good):
        c, present = self.candidates(v, d)
        if len(c) == 0:
            return None
        x, spent = self._bbht(present & good[c], self.budget * math.sqrt(len(c)), 0)
        self.apps += spent
        return None if x is None else int(c[x])

    def minimum(self, v, d, value):
        c, present = self.candidates(v, d)
        N = len(c)
        if N == 0:
            return None
        f = np.where(present, value[c], np.inf)
        cur, spent, limit = int(self.rng.integers(N)), 1, self.budget * math.sqrt(N)
        while spent <= limit:
            x, spent = self._bbht(f < f[cur], limit, spent)
            if x is not None:
                cur = x
        self.apps += spent
        return f[cur] if np.isfinite(f[cur]) else None


def main():
    rng = np.random.default_rng(3)
    runs = wrong = apps = 0
    print(f"{'graph':22} {'n':>2} {'mode':>7} {'dominators ok':>14} {'strong ok':>10} {'queries':>8}")
    insts = []
    C = np.zeros((6, 6), dtype=bool)
    for i in range(6):
        C[i, (i + 1) % 6] = True
    insts.append(("directed cycle", C))
    D = C.copy()
    D[0, 2] = D[3, 5] = True
    insts.append(("cycle with chords", D))
    for s in range(3):
        r = np.random.default_rng(s)
        A = r.random((7, 7)) < 0.3
        np.fill_diagonal(A, False)
        insts.append((f"random {s}", A))
    for name, A in insts:
        n = len(A)
        H = nx.from_numpy_array(A.astype(int), create_using=nx.DiGraph)
        want = {int(k): int(v) for k, v in nx.immediate_dominators(H, 0).items()}
        want[0] = 0
        base = nx.number_strongly_connected_components(H)
        wb = set()
        for e in list(H.edges):
            K = H.copy()
            K.remove_edge(*e)
            if nx.number_strongly_connected_components(K) > base:
                wb.add((int(e[0]), int(e[1])))
        wp = set()
        for v in list(H.nodes):
            K = H.copy()
            K.remove_node(v)
            if nx.number_strongly_connected_components(K) > base:
                wp.add(int(v))
        for mode in ("matrix", "array"):
            g = CircuitG(A, rng, mode, 24)
            idom, _ = dominators(g, 0)
            ok1 = {v: int(idom[v]) for v in range(n) if idom[v] != -1} == want
            g2 = CircuitG(A, rng, mode, 24)
            b, p = strong(g2)
            ok2 = b == wb and p == wp
            runs += 2
            wrong += (not ok1) + (not ok2)
            apps += g.apps + g2.apps
            print(f"{name:22} {n:2} {mode:>7} {str(ok1):>14} {str(ok2):>10} {g.apps + g2.apps:8}", flush=True)
    print(f"\n{runs} runs, {wrong} wrong; at most {used['qubits']} qubits; {used['circuits']} circuits; {apps} oracle applications")
    return wrong


if __name__ == "__main__":
    sys.exit(1 if main() else 0)
