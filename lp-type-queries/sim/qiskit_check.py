"""Quantum Clarkson on small point sets, with every search a Qiskit circuit run in Aer.

One iteration computes the marked bit by a QROM, applies Z and uncomputes. Nothing peeks: a search spends its budget
before reporting none. Limits: noiseless simulation of tiny instances, at most MAX_QUBITS, and n this small is in the
range where a real run would read everything. rounds and thresholds are forced so that the loop still runs.
It tests the construction, not asymptotics. Run with python qiskit_check.py (numpy; qiskit and qiskit-aer for the circuits)
"""
import math
import sys
import numpy as np
from qiskit import QuantumCircuit
from qiskit.circuit.library import XGate
from qiskit_aer import AerSimulator
import lptype
from lptype import *
from check import families

MAX_QUBITS = 8
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
    def search(self, marked):
        N = marked.size
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
                self.spent += 2 * spent
                return x
            m = min(m * 8 / 7, math.sqrt(N) + 1)
        self.spent += 2 * spent
        return None


def main():
    rng = np.random.default_rng(4)
    runs = wrong = unfinished = 0
    print(f"{'family':14} {'n':>3} {'want r2':>9} {'got r2':>9} {'rounds':>6} {'queries':>8}")
    for n in (40, 64):  # above the n <= 4 s cutoff of clarkson only for d = 1
        for name, P in families(n, 1, 7):
            for _ in range(2):
                q = CircuitQ(P, rng, 24)
                ball, t, big = clarkson(q)
                want = solve(P)[1]
                runs += 1
                unfinished += ball is None
                wrong += ball is not None and abs(ball[1] - want) > 1e-5 * max(1, want)
                print(f"{name:14} {n:3} {want:9.4f} {ball[1] if ball else float('nan'):9.4f} {t:6} {q.spent:8}", flush=True)
    print(f"\n{runs} runs, {wrong} wrong, {unfinished} ran out of rounds; at most {used['qubits']} qubits; {used['circuits']} circuits")
    return wrong


if __name__ == "__main__":
    sys.exit(1 if main() else 0)
