"""Checks for the note on the doped chain (README.md).

1. Every generator X_kX_{k+1}, Y_kY_{k+1}, X_kY_{k+2} commutes with Z^n and has #Y + #{odd i : P_i in {X, Y}} odd
   (n <= 30), and the phase gates on odd qubits map them to the stated forms.
2. The base case: on 4 qubits the mapped generators give every odd string commuting with Z^4 (56 strings).
3. Direct closure for 3 <= n <= 8: the strings of g are exactly the set F of the theorem, dim g = 4^(n-1) - 2^(n-1)
   for n >= 4, no diagonal (Z-type) string, and |F| from the counting formula.
4. The odd chord (path plus chord (1, 3)): dim g and d_Z for 4 <= n <= 8, and the strings of g are those commuting
   with X^n and Z^n other than the symmetry group itself.
"""
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from closure import closure
from pauli import anticommute, show


def P(s):
    return (sum(1 << i for i, c in enumerate(s) if c in "XY"), sum(1 << i for i, c in enumerate(s) if c in "ZY"))


def two(i, j, a, b, n):
    s = ["I"] * n
    s[i], s[j] = a, b
    return P("".join(s))


def gens(n):
    return ([two(k, k + 1, "X", "X", n) for k in range(n - 1)] + [two(k, k + 1, "Y", "Y", n) for k in range(n - 1)]
            + [two(k, k + 2, "X", "Y", n) for k in range(n - 2)])


def oddsites(n):  # qubits 1, 3, 5, ... (0-based 0, 2, 4, ...)
    return sum(1 << i for i in range(0, n, 2))


def ycount(p):
    return bin(p[0] & p[1]).count("1")


def inF(p, n):
    allz = (0, (1 << n) - 1)
    return not anticommute(p, allz) and (ycount(p) + bin(p[0] & oddsites(n)).count("1")) % 2 == 1


def W(p, n):
    """Phase gate on every odd qubit: X <-> Y there (signs dropped), Z fixed."""
    x, z = p
    return x, z ^ (x & oddsites(n))


def check_generators():
    for n in range(3, 31):
        for g in gens(n):
            assert inF(g, n)
        mapped = {show(W(g, n), n) for g in gens(n)}
        want = set()
        for k in range(n - 1):
            want |= {show(two(k, k + 1, "X", "Y", n), n), show(two(k, k + 1, "Y", "X", n), n)}
        for k in range(n - 2):  # 0-based k even is qubit k + 1 odd
            want.add(show(two(k, k + 2, "Y", "X", n) if k % 2 == 0 else two(k, k + 2, "X", "Y", n), n))
        assert mapped == want
    print("1. generators lie in F and map to XY, YX on bonds and XY or YX on next-nearest bonds (n <= 30)")


def oddZ(n):
    allz = (0, (1 << n) - 1)
    return {(x, z) for x in range(1 << n) for z in range(1 << n)
            if ycount((x, z)) % 2 == 1 and not anticommute((x, z), allz)}


def check_base():
    S = closure([W(g, 4) for g in gens(4)])
    target = oddZ(4)
    assert S == target and len(S) == 56
    print("2. base case: the mapped generators on 4 qubits give all 56 odd strings commuting with Z^4")


def check_closure():
    print("3. n, dim g, 4^(n-1) - 2^(n-1), |F|, d_Z:")
    for n in range(3, 9):
        S = closure(gens(n))
        F = {(x, z) for x in range(1 << n) for z in range(1 << n) if inF((x, z), n)}
        assert len(F) == 4 ** (n - 1) - 2 ** (n - 1)
        assert S <= F and (n == 3 or S == F)
        dz = sum(1 for p in S if p[0] == 0)
        assert dz == 0
        print(f"   n={n}: {len(S)}  {4 ** (n - 1) - 2 ** (n - 1)}  {len(F)}  {dz}", flush=True)


def check_chord():
    print("4. odd chord: n, dim g, d_Z, 2^(n-1) - 2 (n even) or 2^(n-1) - 1 (n odd):")
    for n in range(4, 9):
        E = [(k, k + 1) for k in range(n - 1)] + [(0, 2)]
        S = closure([two(i, j, "X", "X", n) for i, j in E] + [two(i, j, "Y", "Y", n) for i, j in E])
        X, Z = ((1 << n) - 1, 0), (0, (1 << n) - 1)
        sym = {(0, 0), X, Z, ((1 << n) - 1, (1 << n) - 1)}
        com = {(x, z) for x in range(1 << n) for z in range(1 << n)
               if not anticommute((x, z), X) and not anticommute((x, z), Z)} - sym
        assert S == com
        dz = sum(1 for p in S if p[0] == 0)
        assert dz == 2 ** (n - 1) - (2 if n % 2 == 0 else 1)
        print(f"   n={n}: {len(S)}  {dz}", flush=True)


if __name__ == "__main__":
    check_generators()
    check_base()
    check_closure()
    check_chord()
    print("all checks passed")
