"""Simon's algorithm as Qiskit circuits in Aer, on the toy schemes of toy.py with 3-bit blocks.

The circuit uses only the encryption oracle |x>|z> -> |x>|z xor C(x)>, built from the truth table of C, one
multi-controlled X per point and output bit. CNOTs from x into the output give g = C xor x. For HCTR++ with a one-block
rest, the output qubits of the first block start in |+>, which the XOR leaves unchanged, so only the rest of g acts.
Each shot gives one y; the shots are used in order
until they span a space of dimension D - dim S, and the orthogonal complement of that span is compared with S, and
the hash key with the one recovered from it. Noiseless; at most 18 qubits.
Run with python qiskit_check.py, with qiskit and qiskit-aer installed."""
import sys
import numpy as np
from qiskit import QuantumCircuit, transpile
from qiskit_aer import AerSimulator
import toy

SIM = AerSimulator(method="statevector")


def simon_circuit(C, D, plus):
    qc = QuantumCircuit(2 * D, D)
    qc.h(range(D))
    for j in plus:
        qc.h(D + j)
    for x in range(1 << D):
        for j in range(D):
            if C[x] >> j & 1:
                qc.mcx(list(range(D)), D + j, ctrl_state=x)
    for j in range(D):
        qc.cx(j, D + j)
    qc.h(range(D))
    qc.measure(range(D), range(D))
    return qc


def run(name, scheme, n, shots=200):
    C, parts, S, keys, recover, _, gmask = scheme(n)
    D = sum(parts)
    plus = [] if gmask == -1 else list(range(parts[0]))
    counts = SIM.run(transpile(simon_circuit(C, D, plus), SIM), shots=shots, memory=True).result().get_memory()
    ys = [int(b, 2) for b in counts]
    Sset = set(int(s) for s in S)
    orth = all(bin(y & s).count("1") % 2 == 0 for y in ys for s in Sset)
    dimS = len(S).bit_length() - 1
    basis, used = [], 0
    for y in ys:
        if len(basis) == D - dimS:
            break
        toy.rank_add(basis, y)
        used += 1
    Srec = toy.complement(basis, D)
    el = next(s for s in Srec if s & ((1 << parts[0]) - 1)) if Srec == Sset else None
    good = Srec == Sset and recover(el) == keys
    print(f"{name:8s} n={n} qubits={2 * D:2d} shots={shots} all y orthogonal to S={orth} "
          f"samples used={used} (need {D - dimS}) S recovered={Srec == Sset} keys={good}")
    return orth and good


if __name__ == "__main__":
    ok = run("HCTR2", toy.scheme_hctr2, 3)
    ok &= run("CHCTR", toy.scheme_chctr, 3)
    ok &= run("HCTR++1", lambda n: toy.scheme_hctrpp(n, 1), 3)
    ok &= run("HCTR++d", lambda n: toy.scheme_hctrpp(n, 1, True), 3)
    print("all checks passed" if ok else "SOME CHECK FAILED")
    sys.exit(0 if ok else 1)
