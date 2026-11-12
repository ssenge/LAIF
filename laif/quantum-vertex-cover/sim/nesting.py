"""Two parts of Theorem 1 that the walk tests do not cover. First, the recursion of the costs, in units of log N: with B = N^m, Q^2
<= N^{e(m)} B, a tree with (M1) tight, value calls at (3/4) j + C at nodes of measure j, and the pebbled classical base below W. The
exponent stays below the A of the proof at every measure, and stops growing, so the factors of the levels do not multiply. Second,
the error reduction in place: on a register in one Jordan block, the bits X_i (outcome i equals outcome i - 1, with outcome 0 = 1)
are independent with mean p, by exact enumeration of the outcome strings of the alternating projections."""
import sys
import numpy as np

Q = C = 1
W = 22*Q + 3
A = 7*Q + 4*W + 1


def exponents(mmax, step=.25):
    """e(m), from the sum over the measures j of the nodes: N^{q + m - j} nodes, each at cost N^{q + C + e(3j/4 + C) + 3j/4}, over N^m."""
    e = [0.0]*(int(mmax/step) + 1)
    for i in range(len(e)):
        m = i*step
        if m <= W:
            e[i] = (2*1.585 - 1)*m + Q
            continue
        best = Q
        for k in range(i + 1):
            j = k*step
            best = max(best, Q + C - j/4 + e[min(round((.75*j + C)/step), i - 1)])
        e[i] = 2*Q + best
    return e


def outcomes(V, accept, r):
    """Probabilities of the outcome strings of r alternating tests, from the all-zero start."""
    d = V.shape[0]
    tests = V.conj().T @ np.diag(accept) @ V, np.diag([1.0] + [0.0]*(d - 1))
    start = np.zeros(d, complex)
    start[0] = 1
    out = {}

    def walk(psi, i, bits):
        pr = np.vdot(psi, psi).real
        if pr < 1e-14:
            return
        if i == r:
            out[bits] = pr
            return
        kept = tests[i % 2] @ psi
        walk(kept, i + 1, bits + (1,))
        walk(psi - kept, i + 1, bits + (0,))
    walk(start, 0, ())
    return out


def with_acceptance(p, accept, rng):
    """A random unitary whose first column accepts with probability p."""
    d = len(accept)
    z = rng.normal(size=d) + 1j*rng.normal(size=d)
    on = accept > 0
    z[on] *= np.sqrt(p)/np.linalg.norm(z[on])
    z[~on] *= np.sqrt(1 - p)/np.linalg.norm(z[~on])
    M = np.eye(d, dtype=complex)
    M[:, 0] = z
    V, _ = np.linalg.qr(M)
    V[:, 0] = z
    return V


if __name__ == "__main__":
    bad = 0
    e = exponents(800)
    half, whole = max(e[:len(e)//2]), max(e)
    top = max(e[int(W/.25) + 1:])
    print(f"costs: q = C = {Q}, W = {W}, A = {A}; largest exponent up to m = 400: {half:.2f}, up to m = 800: {whole:.2f}; final {e[-1]:.2f}")
    bad += whole > A or whole > half + 1e-9
    rng = np.random.default_rng(1)
    accept = np.array([1.0]*4 + [0.0]*12)
    r = 12
    for p in (.5, .25, .1):
        out = outcomes(with_acceptance(p, accept, rng), accept, r)
        joint = {}
        for bits, pr in out.items():
            prev, x = 1, []
            for b in bits:
                x.append(int(b == prev))
                prev = b
            joint[tuple(x)] = joint.get(tuple(x), 0.0) + pr
        gap = max(abs(pr - np.prod([p if xi else 1 - p for xi in x])) for x, pr in joint.items())
        count = sum(pr for x, pr in joint.items() if sum(x) >= 3*r/8)
        print(f"bits: p = {p}, largest gap between the joint law and the product {gap:.1e}, Pr[count >= 3r/8] = {count:.4f}")
        bad += gap > 1e-9
    print(f"{bad} failed checks")
    sys.exit(1 if bad else 0)
