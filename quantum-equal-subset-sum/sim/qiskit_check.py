"""The nested search of the base procedure on small instances, as Qiskit circuits run in Aer.

Layers: amplitude amplification over a coin (here a short list of partitions, each with its own prime), quantum
search over residues, and a quantum walk for the claw in the two windows, on the Johnson graphs of r-subsets.
A subset is a bit string, and a step swaps two of its bits under the walk's coin, so one step is plain gates.

Replaced: the table and the windows are read through a diagonal gate computed classically, so there is no
quantum memory and no data register. r-subset states are prepared by a dense gate. The coin holds no iteration
count: j and k are drawn classically for each run. P and T are set to fit the qubits, not to the balance in the
proof. Claw finding is not repeated, so its error is not small here, and its step counts are fixed for one claw.
Limits: noiseless simulation of tiny instances. It tests the construction, not the exponent.
Run with python qiskit_check.py, with qiskit and qiskit-aer installed.
"""
import math
import random
import sys
from collections import Counter
from itertools import combinations
import numpy as np
from qiskit import QuantumCircuit
from qiskit.circuit.library import DiagonalGate, UnitaryGate
from qiskit_aer import AerSimulator
from check import is_prime, layout, plant, good_partition, side, vector

SIM = AerSimulator(method="statevector")
used = Counter()
WALKS = ((4, 2, 4, 3, [(0, 0)]), (4, 2, 4, 3, [(0, 0), (1, 1)]), (8, 2, 3, 3, [(0, 0)]))
GRID_J, GRID_K, RUNS, BUDGET = 3, 2, 50, 200


def bits(x):
    return max(1, math.ceil(math.log2(x)))


def subset_prep(T, r):
    """A dense unitary sending |0> to the uniform superposition of the r-subsets of [T]."""
    v = np.zeros(2**T, dtype=complex)
    for S in combinations(range(T), r):
        v[sum(1 << i for i in S)] = 1
    v /= np.linalg.norm(v)
    e = np.zeros(2**T, dtype=complex)
    e[0] = 1
    w = v - e
    return UnitaryGate(np.eye(2**T) - 2*np.outer(w, w.conj())/np.vdot(w, w))


def walk_layout(T):
    return 1 + 2*bits(T)


def reflect_uniform(qc, q):
    qc.h(q)
    qc.x(q)
    if len(q) == 1:
        qc.z(q[0])
    else:
        qc.h(q[-1])
        qc.mcx(list(q[:-1]), q[-1])
        qc.h(q[-1])
    qc.x(q)
    qc.h(q)


def shift(qc, sx, sy, coin, T):
    """Swap bits u, v of the side's subset under the coin |side, u, v>; u = v does nothing."""
    b = bits(T)
    for s, reg in enumerate((sx, sy)):
        for u in range(T):
            for v in range(T):
                if u != v:
                    val = s | u << 1 | v << (1 + b)
                    qc.cx(reg[v], reg[u])
                    flips = [coin[i] for i in range(len(coin)) if not val >> i & 1]
                    if flips:
                        qc.x(flips)
                    qc.mcx(list(coin) + [reg[u]], reg[v])
                    if flips:
                        qc.x(flips)
                    qc.cx(reg[v], reg[u])


def walk(n_qubits, sx, sy, coin, T, r, t1, t2, diag, diag_q):
    """Prepare the subsets and the coin, then t1 rounds of a phase flip and t2 walk steps."""
    qc = QuantumCircuit(n_qubits)
    p = subset_prep(T, r)
    qc.append(p, list(sx))
    qc.append(p, list(sy))
    qc.h(list(coin))
    step = QuantumCircuit(n_qubits)
    reflect_uniform(step, list(coin))
    shift(step, sx, sy, coin, T)
    for _ in range(t1):
        qc.append(diag, diag_q)
        for _ in range(t2):
            qc.compose(step, inplace=True)
    return qc


def state(qc):
    qc = qc.copy()
    qc.save_statevector()
    return np.asarray(SIM.run(qc).result().get_statevector())


def marked_mass(sv, mask, low):
    """Probability of a marked outcome, with the walk's coin traced out."""
    p = (np.abs(sv)**2).reshape(-1, 2**low).sum(axis=0)
    return p, float(p[mask].sum())


def claw_only(T, r, t1, t2, claws):
    """The walk alone on windows with the given pairs of equal values."""
    w = walk_layout(T)
    sx, sy, coin = list(range(T)), list(range(T, 2*T)), list(range(2*T, 2*T + w))
    mask = np.zeros(2**(2*T), dtype=bool)
    idx = np.arange(2**(2*T))
    for i, j in claws:
        mask |= ((idx >> i & 1) & (idx >> (T + j) & 1)).astype(bool)
    diag = DiagonalGate(np.where(mask, -1.0, 1.0).tolist())
    qc = walk(2*T + w, sx, sy, coin, T, r, t1, t2, diag, sx + sy)
    used["qubits"] = max(used["qubits"], 2*T + w)
    return marked_mass(state(qc), mask, 2*T)[1]


class Instance:
    """The windows of each coin value on a real instance, and the diagonal that marks a claw in them."""

    def __init__(self, name, y, L, labs, T, r_bits, c_bits, rng):
        self.name, self.y, self.L, self.T, self.r_bits, self.c_bits = name, y, L, T, r_bits, c_bits
        self.n = len(y)
        self.low = c_bits + r_bits + 2*T
        self.mask = np.zeros(2**self.low, dtype=bool)
        idx = np.arange(2**(2*T))
        self.labs, self.windows, self.primes, self.capped, good_res = labs, {}, [], 0, 0
        for c, lab in enumerate(labs):
            X, Y = list(side(y, lab, L, False)), list(side(y, lab, L, True))
            lo = max(3, 2**(r_bits - 1) + 1)
            P = rng.choice([q for q in range(lo, 2**r_bits + 1) if is_prime(q)])
            self.primes.append(P)
            for rho in range(P):
                wx, wy = [t for t in X if t[0] % P == rho], [t for t in Y if t[0] % P == rho]
                self.capped += (len(wx) > T) + (len(wy) > T)
                wx, wy = wx[:T], wy[:T]
                self.windows[c, rho] = wx, wy
                sub = np.zeros(2**(2*T), dtype=bool)
                for i, a in enumerate(wx):
                    for j, b in enumerate(wy):
                        if a[0] == b[0]:
                            sub |= ((idx >> i & 1) & (idx >> (T + j) & 1)).astype(bool)
                good_res += bool(sub.any())
                base = c | rho << c_bits
                self.mask[base | idx << (c_bits + r_bits)] = sub
        self.good_res = good_res
        self.total_res = 2**(c_bits + r_bits)
        self.diag = DiagonalGate(np.where(self.mask, -1.0, 1.0).tolist())
        self.w = walk_layout(T)
        self.qubits = self.low + self.w

    def circuit(self, r, t1, t2, j, k):
        c, rr, T = self.c_bits, self.r_bits, self.T
        cq = list(range(c))
        rq = list(range(c, c + rr))
        sx = list(range(c + rr, c + rr + T))
        sy = list(range(c + rr + T, c + rr + 2*T))
        coin = list(range(self.low, self.low + self.w))
        all_q = list(range(self.qubits))
        U = walk(self.qubits, sx, sy, coin, T, r, t1, t2, self.diag, list(range(self.low)))
        Ui = U.inverse()
        A = QuantumCircuit(self.qubits)
        A.h(cq)
        A.h(rq)
        for _ in range(j):
            A.compose(U, inplace=True)
            A.append(self.diag, list(range(self.low)))
            A.compose(Ui, inplace=True)
            reflect_uniform(A, rq)
        A.compose(U, inplace=True)
        qc = A.copy()
        if k:
            Ai = A.inverse()
            for _ in range(k):
                qc.append(self.diag, list(range(self.low)))
                qc.compose(Ai, inplace=True)
                qc.x(all_q)
                qc.h(all_q[-1])
                qc.mcx(all_q[:-1], all_q[-1])
                qc.h(all_q[-1])
                qc.x(all_q)
                qc.compose(A, inplace=True)
        used["qubits"] = max(used["qubits"], self.qubits)
        used["circuits"] += 1
        used["walks"] += (2*j + 1)*(2*k + 1)
        return qc

    def prob(self, r, t1, t2, j, k):
        return marked_mass(state(self.circuit(r, t1, t2, j, k)), self.mask, self.low)

    def output(self, x):
        """Step 3 of the procedure: read a solution from a measured outcome, checked against y."""
        c, rho = x & (2**self.c_bits - 1), x >> self.c_bits & (2**self.r_bits - 1)
        if (c, rho) not in self.windows:
            return None
        S = x >> (self.c_bits + self.r_bits)
        wx, wy = self.windows[c, rho]
        for i, a in enumerate(wx):
            for j, b in enumerate(wy):
                if S >> i & 1 and S >> (self.T + j) & 1 and a[0] == b[0]:
                    lab = self.labs[c]
                    return [p - q for p, q in zip(vector(self.n, lab, False, a[1], a[2]),
                                                  vector(self.n, lab, True, b[1], b[2]))]
        return None


def empty_layout(n):
    z = round(n/3)
    minus = (n - z)//2
    plus = n - z - minus
    b1, b0 = minus//2, z//2
    return dict(z=z, plus=plus, minus=minus, A=(0, 0, plus - minus), B=(b1, b0, b1), C=(minus - b1, z - b0, minus - b1))


def partitions(D, L, count, rng):
    """One good partition and count-1 uniform ones with the same label sizes."""
    labs = [good_partition(D, L, rng)]
    n = len(D)
    sizes = {c: sum(L[c]) for c in "ABC"}
    for _ in range(count - 1):
        order = list(range(n))
        rng.shuffle(order)
        cuts = iter(order)
        labs.append({next(cuts): c for c in "ABC" for _ in range(sizes[c])})
    return labs


def plant_with(n, L, rng):
    D = [1]*L["plus"] + [-1]*L["minus"] + [0]*L["z"]
    y = [rng.getrandbits(3*n) for _ in range(n)]
    y[0] = 0
    y[0] = -sum(d*v for d, v in zip(D, y))
    order = list(range(n))
    rng.shuffle(order)
    return [y[i] for i in order], [D[i] for i in order]


def is_solution(d, y):
    return d is not None and set(d) <= {-1, 0, 1} and any(d) and sum(a*b for a, b in zip(d, y)) == 0


def instances():
    rng = random.Random(7)
    out = []
    L = layout(10)
    y, D, _ = plant(10, "random", rng)
    out.append(Instance("labels", y, L, partitions(D, L, 4, rng), 4, 4, 2, rng))
    y, D, _ = plant(10, "heavy", rng)
    out.append(Instance("labels, equal sums", y, L, partitions(D, L, 4, rng), 4, 4, 2, rng))
    L = empty_layout(12)
    y, D = plant_with(12, L, rng)
    out.append(Instance("empty label", y, L, partitions(D, L, 4, rng), 4, 6, 2, rng))
    L = layout(10)
    D = [1]*L["plus"] + [-1]*L["minus"] + [0]*L["z"]
    out.append(Instance("no solution", [2**i for i in range(10)], L, partitions(D, L, 4, rng), 4, 4, 2, rng))
    return out


def main():
    bad = 0
    print("the walk alone: probability that the measured subsets hold a claw")
    print(f"{'T':>2} {'r':>2} {'t1':>3} {'t2':>3} {'claws':>6} {'qubits':>7} {'no walk':>8} {'walk':>7}")
    for T, r, t1, t2, claws in WALKS:
        base = claw_only(T, r, 0, 0, claws)
        p = claw_only(T, r, t1, t2, claws)
        bad += p <= base and len(claws) == 1
        print(f"{T:2} {r:2} {t1:3} {t2:3} {len(claws):6} {2*T + walk_layout(T):7} {base:8.3f} {p:7.3f}", flush=True)

    T, r, t1, t2 = 4, 2, 4, 3
    print("\nall three layers: probability of a real solution in one run")
    print(f"{'instance':20} {'n':>2} {'qubits':>6} {'marked':>9} {'blind':>6} {'+walk':>6} {'+residues':>9} {'+coin':>6}  j k {'capped':>6} {'amp err':>8}  runs to a solution")
    rs = np.random.default_rng(3)
    for I in instances():
        table = {(j, k): I.prob(r, t1, t2, j, k)[0] for j in range(GRID_J) for k in range(GRID_K)}
        blind = I.prob(r, 0, 0, 0, 0)[1]
        mass = {key: float(p[I.mask].sum()) for key, p in table.items()}
        walk_p = mass[0, 0]
        res_p = max(mass[j, 0] for j in range(GRID_J))
        j, k = max(mass, key=mass.get)
        amp = max(abs(mass[a, 1] - math.sin(3*math.asin(math.sqrt(mass[a, 0])))**2) for a in range(GRID_J))
        bad += amp > 1e-6
        counts, wrong, gave_up = [], 0, 0
        for _ in range(RUNS):
            for t in range(1, BUDGET + 1):
                key = (int(rs.integers(GRID_J)), int(rs.integers(GRID_K)))
                pr = table[key]
                x = int(rs.choice(len(pr), p=pr/pr.sum()))
                d = I.output(x)
                if d is not None:
                    wrong += not is_solution(d, I.y)
                    counts.append(t)
                    break
            else:
                gave_up += 1
        bad += wrong
        expected = bool(I.mask.any())
        bad += (gave_up > 0) if expected else (bool(counts) or blind > 0 or mass[j, k] > 1e-12)
        runs = f"mean {np.mean(counts):.1f}, gave up {gave_up}/{RUNS}, wrong {wrong}" if counts else f"none flagged in {RUNS}x{BUDGET} runs"
        print(f"{I.name:20} {I.n:2} {I.qubits:6} {I.good_res:4}/{I.total_res:<4} {blind:6.3f} {walk_p:6.3f} {res_p:9.3f} {mass[j, k]:6.3f}  {j} {k} {I.capped:6} {amp:8.1e}  {runs}", flush=True)
    print(f"\nat most {used['qubits']} qubits; {used['circuits']} circuits; {used['walks']} walks in them; {bad} failed checks")
    return bad


if __name__ == "__main__":
    sys.exit(1 if main() else 0)
