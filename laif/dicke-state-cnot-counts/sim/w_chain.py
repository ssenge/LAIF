"""Exact check: the W state on n qubits with 2n - 3 CNOTs (n >= 3).
Step 1 (one CNOT): Ry(a) on q0, CNOT(q0 -> q1), X on q1, with sin(a/2) = 1/sqrt(n).
Step i = 1..n-2 (two CNOTs on q_i, q_{i+1}): Ry(phi/2) on q_{i+1}, CNOT(q_i -> q_{i+1}), Ry(-phi/2) on q_{i+1},
CNOT(q_{i+1} -> q_i), with sin(phi/2) = 1/sqrt(n - i). The first three gates act as a controlled rotation because
q_{i+1} is still |0>. Every amplitude is compared with the target exactly (minimal polynomial of the difference is x).
Run: python -I w_chain.py"""
import sympy as sp

X = sp.Symbol("x")

def run(n):
    psi = [sp.Integer(0)] * 2 ** n; psi[0] = sp.Integer(1)
    bit = lambda i, q: (i >> (n - 1 - q)) & 1
    def ry(psi, q, c, s):                          # c, s = cos, sin of half the angle
        out = list(psi)
        for i in range(2 ** n):
            if not bit(i, q):
                j = i | (1 << (n - 1 - q)); out[i] = c * psi[i] - s * psi[j]; out[j] = s * psi[i] + c * psi[j]
        return out
    def cx(psi, a, b):
        return [psi[i ^ (1 << (n - 1 - b))] if bit(i, a) else psi[i] for i in range(2 ** n)]
    def x(psi, q):
        return [psi[i ^ (1 << (n - 1 - q))] for i in range(2 ** n)]
    cnots = 0
    s = 1 / sp.sqrt(n); psi = ry(psi, 0, sp.sqrt(1 - s ** 2), s); psi = cx(psi, 0, 1); psi = x(psi, 1); cnots += 1
    for i in range(1, n - 1):
        sh = 1 / sp.sqrt(n - i); ch = sp.sqrt(1 - sh ** 2)          # sin, cos of phi/2, phi/2 in (0, pi/2]
        c4, s4 = sp.sqrt((1 + ch) / 2), sp.sqrt((1 - ch) / 2)      # cos, sin of phi/4
        psi = ry(psi, i + 1, c4, s4); psi = cx(psi, i, i + 1); psi = ry(psi, i + 1, c4, -s4); psi = cx(psi, i + 1, i)
        cnots += 2
    for idx in range(2 ** n):
        want = 1 / sp.sqrt(n) if bin(idx).count("1") == 1 else 0
        d = sp.nsimplify(sp.expand(psi[idx] - want))
        assert d == 0 or sp.minimal_polynomial(d, X) == X, (n, idx, d)
    assert cnots == 2 * n - 3
    return cnots

if __name__ == "__main__":
    for n in range(3, 8):
        print("n = %d: W state exact with %d CNOTs" % (n, run(n)))
