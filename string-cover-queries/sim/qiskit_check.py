"""Covers of small strings, with every search a Qiskit circuit run in Aer.

One iteration computes the marked bit by a QROM, applies Z and uncomputes. Nothing peeks: a search spends its budget
before reporting none. Each inner predicate is also run on every block, with its own searches as circuits.
The outer search's table holds the predicate values, so the circuits are not nested: that part is a table, not a
composition. Limits: noiseless simulation of tiny instances, at most MAX_QUBITS. It tests the construction, not asymptotics.
Run with python qiskit_check.py (numpy; qiskit and qiskit-aer for the circuits)
"""
import math
import sys
import numpy as np
from qiskit import QuantumCircuit
from qiskit.circuit.library import XGate
from qiskit_aer import AerSimulator
from covers import *
from check import brute, codes

MAX_QUBITS = 9
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


class CircuitQ(Q):
    def search(self, marked, w=2):
        N = marked.size
        if N == 0:
            return None
        ni = max(1, math.ceil(math.log2(N)))
        assert ni + 1 <= MAX_QUBITS, f"would need {ni + 1} qubits"
        used["qubits"] = max(used["qubits"], ni + 1)
        table = np.zeros(2 ** ni, dtype=bool)
        table[:N] = marked
        limit = self.budget * math.sqrt(N)
        m, spent = 1.0, 0
        while spent <= limit:
            j = int(self.rng.integers(0, int(m)))
            r = SIM.run(circuit(table, ni, j), shots=1, seed_simulator=int(self.rng.integers(1 << 31))).result()
            x = int(next(iter(r.get_counts())), 2)
            used["circuits"] += 1
            spent += 2 * j + 1
            if x < N and marked[x]:
                self.spent += spent * w
                return x
            m = min(m * 8 / 7, math.sqrt(N) + 1)
        self.spent += spent * w
        return None


def main():
    rng = np.random.default_rng(3)
    budget = 24
    runs = wrong = inner = 0
    print(f"{'string':34} {'want':>10} {'got':>10} {'queries':>8}")
    u = "abaababa"
    for s in ("aabaabaaabaabaa", "a" * 40, "a" * 20 + "b" + "a" * 19, u + u[3:] + u[3:] + u, (u + "b") * 4 + u, "abcabcabcabcabcabcabcabcabcabcab",
              "abaabaabaabaabaabaabaabaabaabaab"):
        want = brute(s)
        for _ in range(3):
            q = CircuitQ(codes(s), rng, budget)
            got = all_covers(q)
            runs += 1
            wrong += got != want
            print(f"{s[:34]:34} {str(want)[:10]:>10} {str(got)[:10]:>10} {q.spent:8}", flush=True)
        for l in want[:3]:
            if l < len(s) and l >= 8:
                q = CircuitQ(codes(s), rng, budget)
                c = prepare(q, l)
                t = pred_truth(q, l)
                for j in range(len(t)):
                    wrong += pred(q, c, j) != t[j]
                    inner += 1
    print(f"\n{runs} runs and {inner} predicates, {wrong} wrong; at most {used['qubits']} qubits; {used['circuits']} circuits")
    return wrong


if __name__ == "__main__":
    sys.exit(1 if main() else 0)
