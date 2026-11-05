"""The quantum walk on search trees of Vertex Cover instances, as Qiskit circuits in Aer: phase estimation of U = R_B R_A on
the root, accepting if the phase register reads zero. A marked vertex gives acceptance at least about 1/2, and no marked vertex
a smaller value, so repeating and comparing with a threshold decides. The gates are dense unitaries computed classically from
the tree, with no reversible circuit for the branching rule. Noiseless. It tests the walk on tiny trees, not an exponent.
Run with python qiskit_check.py, with qiskit and qiskit-aer installed."""
import math
import random
import sys
import numpy as np
from qiskit import QuantumCircuit, transpile
from qiskit.circuit.library import QFTGate, UnitaryGate
from qiskit_aer import AerSimulator
from tree import Tree, reflections, random_regular, minimum_cover

SIM = AerSimulator(method="statevector")


def accept_probability(t, bits):
    """Probability that phase estimation with the given number of bits reads phase 0, from the root."""
    RA, RB = reflections(t)
    node = math.ceil(math.log2(t.T))
    dim = 2**node
    U = np.eye(dim, dtype=complex)
    U[:t.T, :t.T] = RB @ RA
    qc = QuantumCircuit(bits + node)
    qc.h(range(bits))
    power = U
    for j in range(bits):
        qc.append(UnitaryGate(power).control(1), [j] + list(range(bits, bits + node)))
        power = power @ power
    qc.append(QFTGate(bits).inverse(), range(bits))
    qc.save_statevector()
    state = np.asarray(SIM.run(transpile(qc, SIM)).result().get_statevector())
    probs = np.abs(state)**2
    return float(probs[::1][np.arange(len(probs)) % 2**bits == 0].sum()), bits + node


def exact_accept(t, bits):
    """The same probability with no circuit: the norm squared of the average of U^j on the root, over j below 2^bits."""
    RA, RB = reflections(t)
    U = RB @ RA
    v = np.eye(t.T, dtype=complex)[0]
    total = np.zeros(t.T, complex)
    for _ in range(2**bits):
        total += v
        v = U @ v
    return float(np.linalg.norm(total/2**bits)**2)


if __name__ == "__main__":
    rng = random.Random(4)
    print(f"{'graph':14} {'k':>3} {'T':>4} {'n':>3} {'marked':>6} {'bits':>4} {'qubits':>6} {'accept':>7} {'spectrum':>8} {'search once':>11}")
    bad = yes = no = 0
    worst_yes, worst_no = 1.0, 0.0
    for d, sizes in ((3, (12, 16, 20)), (4, (10, 14, 18)), (6, (14, 18))):
        for size in sizes:
            adj = random_regular(size, d, rng)
            m = minimum_cover(adj)
            for k in (m - 1, m):
                t = Tree(adj, k)
                if t.T < 3 or t.T > 64:
                    continue
                bits = max(4, min(7, math.ceil(math.log2(4*math.sqrt(t.T*t.n)))))
                p, q = accept_probability(t, bits)
                ex = exact_accept(t, bits)
                bad += abs(p - ex) > 1e-6 or q > 20
                if t.has_marked():
                    yes += 1
                    worst_yes = min(worst_yes, p)
                else:
                    no += 1
                    worst_no = max(worst_no, p)
                print(f"{d}-reg n={size:<6} {k:3} {t.T:4} {t.n:3} {sum(t.marked):6} {bits:4} {q:6} {p:7.3f} {ex:8.3f} {sum(t.marked)/t.T:11.3f}", flush=True)
    bad += worst_yes <= worst_no
    print(f"{yes} instances with a cover: acceptance at least {worst_yes:.3f}. {no} without: at most {worst_no:.3f}. {bad} failed checks")
    sys.exit(1 if bad else 0)
