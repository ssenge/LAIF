"""The recognizer on small inputs, with every search a Qiskit circuit run in Aer.

One iteration computes the marked bit by a QROM (one oracle application in the count, as in grover_stats.py), applies
Z and uncomputes. Nothing peeks: a search spends its budget before reporting none. Reads are classical.
Limits: noiseless simulation of tiny instances, at most MAX_QUBITS. It tests the construction, not asymptotics.
Run with python qiskit_check.py (numpy; qiskit and qiskit-aer for the circuits)
"""
import math
import sys
import numpy as np
from qiskit import QuantumCircuit
from qiskit.circuit.library import XGate
from qiskit_aer import AerSimulator
from threshold import *

MAX_QUBITS = 12
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
        marked = marked.ravel()
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
                self.apps += spent
                return x
            m = min(m * 8 / 7, math.sqrt(N) + 1)
        self.apps += spent
        return None


def nested(M, rng, budget):
    q = CircuitQ(M, rng, budget)
    H = np.zeros_like(M)
    a, b = M.shape
    learn_nested(q, H, np.arange(a), np.arange(b))
    return is_nested(H) and q.search((H != M).ravel()) is None, q


def threshold(A, rng, budget):
    q = CircuitQ(A, rng, budget)
    H = np.zeros_like(A)
    n = len(A)
    learn_threshold(q, H, np.arange(n))
    return is_threshold(H) and q.search((H != A)[np.triu_indices(n, 1)]) is None, q


def main():
    rng = np.random.default_rng(5)
    budget = 24
    runs = wrong = apps = 0
    print(f"{'instance':24} {'want':>5} {'got':>5} {'queries':>8} {'all entries':>12}")
    insts = []
    for tokens in ("rc" * 9, "r" * 8 + "rc" + "c" * 8, "r" * 9 + "c" * 9, "c" * 9 + "r" * 9, "ccccrrrrcrcrrrrccc"):
        insts.append((f"nested {tokens[:12]}", True, nested_from_tokens(tokens, runs), nested))
    M = nested_from_tokens("rc" * 9, 1)
    M = M.copy()
    M[np.argsort(M.sum(1))[1], np.argsort(M.sum(0))[1]] ^= 1
    insts.append(("nested with a flip", is_nested(M), M, nested))
    P = np.zeros((9, 9), dtype=np.int8)
    P[0, 0] = P[1, 1] = 1
    insts.append(("two hidden ones", False, P, nested))
    insts.append(("alternating sequence", True, from_sequence([i % 2 for i in range(12)], rng.permutation(12)), threshold))
    insts.append(("random sequence", True, from_sequence(rng.integers(0, 2, 12), rng.permutation(12)), threshold))
    A = from_sequence([i % 2 for i in range(12)])
    A[0, 7] = A[7, 0] = 0
    insts.append(("threshold with a flip", is_threshold(A), A, threshold))
    for name, want, X, f in insts:
        for _ in range(3):
            ans, q = f(X, rng, budget)
            runs += 1
            wrong += ans != want
            apps += q.total()
            print(f"{name:24} {str(want):>5} {str(ans):>5} {q.total():8} {X.size:12}", flush=True)
    print(f"\n{runs} runs, {wrong} wrong; at most {used['qubits']} qubits; {used['circuits']} circuits; {apps} queries")
    return wrong


if __name__ == "__main__":
    sys.exit(1 if main() else 0)
