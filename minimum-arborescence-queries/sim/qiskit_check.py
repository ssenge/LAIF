"""The whole algorithm on small graphs with every Grover search run as a Qiskit circuit in Aer.

Registers: index (the items of one call, padded to a power of 2) and value (the weight, as a rank among
the distinct weights). One oracle application is the QROM |i>|0> -> |i>|w_i>, built from multi-controlled X
gates. Between compute and uncompute a diagonal gate marks the good items. It depends only on classical
state (held list, offsets, contracted set), so it costs no queries. No ancillas; at most MAX_QUBITS.
Nothing peeks at the state: when no good element is left, a call spends its whole budget of
32*sqrt(d*N) applications before it stops, as a real device would.

Checks: final answers against the exact back end and the dual certificate; Grover success frequency against
sin^2((2j+1)theta). Limits: noiseless simulation on tiny instances. It tests the construction, not any
asymptotics, and Aer runs multi-controlled and diagonal gates natively, so gate counts mean nothing here.
Run with python qiskit_check.py (numpy; qiskit and qiskit-aer for the circuits)
"""
import math
import sys
import numpy as np
from qiskit import QuantumCircuit
from qiskit.circuit.library import DiagonalGate, XGate
from qiskit_aer import AerSimulator
from arb import INF, Run
import instances as I

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


def grover_circuit(table, phase, ni, nv, j):
    """j iterations from the uniform superposition over indices, then measure the index register."""
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


def run_once(qc, rng):
    r = SIM.run(qc, shots=1, seed_simulator=int(rng.integers(1 << 31))).result()
    return int(next(iter(r.get_counts())), 2)


def top_k_circuit(Wsub, ysub, excluded, d, rng, stats, budget=32):
    A, B = Wsub.shape
    N = A * B
    ni = bits(N)
    distinct = np.unique(Wsub)
    nv = bits(len(distinct))
    assert ni + nv <= MAX_QUBITS, f"would need {ni + nv} qubits"
    used["qubits"] = max(used["qubits"], ni + nv)
    w = Wsub.ravel()
    table = np.searchsorted(distinct, w).tolist() + [0] * (2 ** ni - N)
    rows, cols = np.repeat(np.arange(A), B), np.tile(np.arange(B), A)
    f = np.where((w >= INF) | excluded[rows], INF, w - ysub[cols])
    rank_key = lambda i: (int(f[i]), int(i))
    rep = {}  # row -> index held for that type
    limit = budget * math.sqrt(d * N)
    spent = 0
    while spent <= limit:
        worst = max((rank_key(x) for x in rep.values()), default=None) if len(rep) >= d else None

        def good(i):
            if i >= N or f[i] >= INF:
                return False
            key = rank_key(i)
            bound = rep.get(int(rows[i]))
            if bound is not None:
                return key < rank_key(bound)
            return worst is None or key < worst

        # phase table over index and value; index decides goodness, and value is checked to agree with it
        flags = np.array([good(i) for i in range(2 ** ni)])
        phase = np.ones(2 ** (ni + nv), dtype=complex)
        for i in np.flatnonzero(flags):
            phase[int(i) | (table[i] << ni)] = -1
        m, found = 1.0, None
        while found is None and spent <= limit:
            j = int(rng.integers(0, int(m)))
            x = run_once(grover_circuit(table, phase, ni, nv, j), rng)
            used["circuits"] += 1
            spent += 2 * j + 1
            if flags[x]:
                found = x
            m = min(m * 8 / 7, math.sqrt(N) + 1)
        if found is None:
            break
        r = int(rows[found])
        if r in rep or len(rep) < d:
            rep[r] = found
        else:
            del rep[max(rep, key=lambda k: rank_key(rep[k]))]
            rep[r] = found
    used["applications"] += spent
    return sorted((int(f[x]), int(rows[x]), int(cols[x])) for x in rep.values())


def law_check():
    """Measured success frequency of one Grover circuit against sin^2((2j+1)theta)."""
    rng = np.random.default_rng(3)
    table = [5, 1, 7, 2, 6, 3, 4, 0]
    ni, nv = 3, 3
    good = {1, 3, 7}
    phase = np.ones(2 ** (ni + nv), dtype=complex)
    for i in good:
        phase[i | (table[i] << ni)] = -1
    theta = math.asin(math.sqrt(len(good) / 8))
    for j in range(4):
        qc = grover_circuit(table, phase, ni, nv, j)
        counts = SIM.run(qc, shots=20000, seed_simulator=int(rng.integers(1 << 31))).result().get_counts()
        got = sum(c for k, c in counts.items() if int(k, 2) in good) / 20000
        want = math.sin((2 * j + 1) * theta) ** 2
        assert abs(got - want) < 0.02, (j, got, want)
        print(f"  j={j}: success {got:.3f}, formula {want:.3f}")


def main():
    print("Grover circuit against the formula, 3 index + 3 value qubits")
    law_check()
    runs = wrong = 0
    print("\nfull algorithm, every search a circuit")
    print(f"{'family':11} {'n':>2} {'seed':>4} {'cost':>7} {'exact':>7} {'applications':>12} {'circuits':>8}")
    for name, n in (("random", 4), ("random", 5), ("random", 6), ("chain", 5), ("chain", 7), ("blocks2", 7), ("bidirected", 6), ("hierarchy", 6)):
        W = I.FAMILIES[name](n)
        # small value range keeps the value register short
        top = np.unique(W[W < INF])
        W = np.where(W < INF, np.searchsorted(top, W) + 1, INF)
        ex = Run(W.copy())
        _, exact = ex.solve()
        for seed in range(3):
            a0, c0 = used["applications"], used["circuits"]
            r = Run(W.copy(), mode=top_k_circuit, seed=seed)
            out = r.solve()
            runs += 1
            ok = out is not None and out[1] == exact
            if ok:
                r.verify(*out)
            wrong += not ok
            print(f"{name:11} {n:2} {seed:4} {(out[1] if out else -1):7} {exact:7} {used['applications'] - a0:12} {used['circuits'] - c0:8}", flush=True)
    print(f"\n{runs} runs, {wrong} wrong; at most {used['qubits']} qubits; {used['circuits']} circuits executed")
    return wrong


if __name__ == "__main__":
    sys.exit(1 if main() else 0)
