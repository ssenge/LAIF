"""The nested search of the base procedure on small instances over [-d:d], as Qiskit circuits run in Aer.

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
from itertools import combinations, product
import numpy as np
from qiskit import QuantumCircuit
from qiskit.circuit.library import DiagonalGate, UnitaryGate
from qiskit_aer import AerSimulator
from check import is_prime, table, perms, min_support
from opt import Scheme, wide_labels, profile

SIM = AerSimulator(method="statevector")
used = Counter()
WALKS = ((4, 2, 4, 3, [(0, 0)]), (4, 2, 4, 3, [(0, 0), (1, 1)]))
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

    def __init__(self, name, d, y, coins, T, r_bits, c_bits, rng):
        self.d = d
        self.name, self.y, self.T, self.r_bits, self.c_bits = name, y, T, r_bits, c_bits
        self.n = len(y)
        self.low = c_bits + r_bits + 2*T
        self.mask = np.zeros(2**self.low, dtype=bool)
        idx = np.arange(2**(2*T))
        self.windows, self.primes, self.capped, good_res = {}, [], 0, 0
        for c, (X, Y) in enumerate(coins):
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
                    return [p - q for p, q in zip(a[1], b[1])]
        return None


def coin_lists(S, nu, D, y, rng, count):
    """Typed lists for one good partition and count-1 uniform ones, with one pinned coordinate. X[pin] = D[pin], Y[pin] = 0."""
    n = len(D)
    pin = next(i for i, c in enumerate(D) if c)
    rest = [i for i in range(n) if i != pin]
    D0 = [D[i] for i in rest]
    nu = table(S, S.q, D0)
    by_c = {}
    for i in rest:
        by_c.setdefault(D[i], []).append(i)
    coords = {}
    tx, ty = {}, {}
    for c, idx in by_c.items():
        rng.shuffle(idx)
        it = iter(idx)
        for cell, k in nu.items():
            if S.c[cell] == c and k:
                L = int(S.L[cell])
                coords.setdefault(L, []).extend(next(it) for _ in range(k))
                tx.setdefault(L, Counter())[int(S.x[cell])] += k
                ty.setdefault(L, Counter())[int(S.y[cell])] += k

    def build(coords, types, pinned):
        out = []
        parts = [[(coords[L], p) for p in perms(types[L])] for L in sorted(coords)]
        for choice in product(*parts):
            vec = [0]*n
            vec[pin] = pinned
            for I, p in choice:
                for i, v in zip(I, p):
                    vec[i] = v
            out.append((sum(a*b for a, b in zip(vec, y)), tuple(vec)))
        return out

    coins = [(build(coords, tx, D[pin]), build(coords, ty, 0))]
    sizes = {L: len(I) for L, I in coords.items()}
    for _ in range(count - 1):
        order = rest[:]
        rng.shuffle(order)
        it = iter(order)
        other = {L: [next(it) for _ in range(sizes[L])] for L in sorted(sizes)}
        coins.append((build(other, tx, D[pin]), build(other, ty, 0)))
    return coins


def planted(d, n, w, rng):
    """y with a planted D of the profile w, of minimum support."""
    D = []
    for k in range(d + 1):
        m = round(w[k]*n)
        D += [0]*m if k == 0 else [k]*(m//2) + [-k]*(m - m//2)
    D = (D + [1, -1]*n)[:n]
    while True:
        y = [rng.getrandbits(3*n) for _ in range(n)]
        p = D.index(1)
        y[p] = 0
        y[p] = -sum(a*b for a, b in zip(D, y))
        order = list(range(n))
        rng.shuffle(order)
        yy, DD = [y[i] for i in order], [D[i] for i in order]
        if min_support(yy, d) == sum(1 for c in DD if c):
            return yy, DD


def is_solution(v, y, d):
    return v is not None and any(v) and max(map(abs, v)) <= d and sum(a*b for a, b in zip(v, y)) == 0


def instances():
    rng = random.Random(7)
    out = []
    for name, d, w, n, rb in (("d=2, uniform", 2, [.2, .4, .4], 9, 5), ("d=2, worst profile", 2, [.14, .3, .56], 9, 5),
                              ("d=3, uniform", 3, [1/7, 2/7, 2/7, 2/7], 8, 5), ("d=2, many zeros", 2, [.3, .4, .3], 9, 4)):
        S = Scheme(d, wide_labels(d))
        S.q = S.solve(profile(d, w), starts=4)[1]
        y, D = planted(d, n, w, rng)
        coins = coin_lists(S, None, D, y, rng, 4)
        print(f"# {name}: list sizes {len(coins[0][0])}, {len(coins[0][1])}", flush=True)
        out.append(Instance(name, d, y, coins, 4, rb, 2, rng))
    d = 2
    S = Scheme(d, wide_labels(d))
    S.q = S.solve(profile(d, [.2, .4, .4]), starts=4)[1]
    D = planted(d, 9, [.2, .4, .4], rng)[1]
    y = [5**i for i in range(9)]        # base 2d+1 digits are unique, so there is no solution
    out.append(Instance("no solution", d, y, coin_lists(S, None, D, y, rng, 4), 4, 5, 2, rng))
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

    print("\nthe walk at T = 4, r = 2, t2 = 3, with t1 uniform below 8")
    print(f"{'claws':14} {'no walk':>8} {'mean':>7}")
    for name, claws in (("one pair", [(0, 0)]), ("two disjoint", [(0, 0), (1, 1)]),
                        ("star 1x4", [(0, b) for b in range(4)]),
                        ("block 2x2", [(a, b) for a in range(2) for b in range(2)])):
        ps = [claw_only(4, 2, t, 3, claws) for t in range(8)]
        bad += sum(ps)/8 < 1/4
        print(f"{name:14} {ps[0]:8.3f} {sum(ps)/8:7.3f}", flush=True)

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
                    wrong += not is_solution(d, I.y, I.d)
                    counts.append(t)
                    break
            else:
                gave_up += 1
        bad += wrong
        expected = I.name != "no solution"
        bad += (gave_up > 0 or not I.mask.any()) if expected else (bool(counts) or blind > 0 or mass[j, k] > 1e-12)
        runs = f"mean {np.mean(counts):.1f}, gave up {gave_up}/{RUNS}, wrong {wrong}" if counts else f"none flagged in {RUNS}x{BUDGET} runs"
        print(f"{I.name:20} {I.n:2} {I.qubits:6} {I.good_res:4}/{I.total_res:<4} {blind:6.3f} {walk_p:6.3f} {res_p:9.3f} {mass[j, k]:6.3f}  {j} {k} {I.capped:6} {amp:8.1e}  {runs}", flush=True)
    print(f"\nat most {used['qubits']} qubits; {used['circuits']} circuits; {used['walks']} walks in them; {bad} failed checks")
    return bad


if __name__ == "__main__":
    sys.exit(1 if main() else 0)
