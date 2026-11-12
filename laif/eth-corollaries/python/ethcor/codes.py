"""N11: the distance of a quantum CSS code, deterministic, in C·2^{δn}.

A CSS code on n qubits is given by two lists of checks H1, H2 (each a list of qubits). The logical
operators counted are the x ∈ ker H1 outside the row space of H2 (Z-type for H1 = H_X, H2 = H_Z).
The input is `unary s ++ enc(codeCNF H1 H2)` (H1 as positive clauses, H2 as negative ones). The
front end `preQ w e` writes `cssF w n ψ e` on 5n + 2 variables: the checks (one clause per odd
pattern), the chain c_0 = 0, c_{i+1} = c_i ⊕ x_i y_i, c_n = e, and the complements of y and c.
Anthropic's `SIZED` counts K (e = false, target 2n + 1) = |ker H2| and N (e = true, target
s + 2n + 1) = |ker H2|·L_s/2, and the machine writes 2N/K = L_s (`Code.numLog_eq`,
`CodeTM.css_counts`; lean/EthCor/CodeFormula.lean, lean/EthCor/CodeTM.lean).
"""

from __future__ import annotations

from itertools import product
from typing import Sequence

from .cnf import Fml
from .connected import _sized, compF, enc_free, read_free
from .graphs import unary
from .hamcycle import ones, rest

Checks = list[list[int]]


def pats(w: int) -> list[list[bool]]:
    """All Bool lists of length at most w, in the order of Lean's `Code.pats`."""
    if w == 0:
        return [[]]
    return [[]] + [c for b in pats(w - 1) for c in ([False] + b, [True] + b)]


def pos(n: int, l: tuple[int, bool]) -> int:
    """x_j = j for (j, true), y_j = n + j for (j, false) (Lean: `Code.pos`)."""
    return l[0] if l[1] else n + l[0]


def rowF(w: int, n: int, C: list[tuple[int, bool]]) -> Fml:
    """One clause forbidding each odd pattern of the check (Lean: `Code.rowF`)."""
    return [[(pos(n, q), not b) for q, b in zip(C, p)] for p in pats(w)
            if len(p) == len(C) and p.count(True) % 2 == 1]


def xorC(a: int, b: int, c: int, d: int) -> Fml:
    """x_d = x_c ⊕ (x_a ∧ x_b) (Lean: `Code.xorC`)."""
    return [[(a, not al), (b, not be), (c, not ga), (d, ga != (al and be))]
            for al in (False, True) for be in (False, True) for ga in (False, True)]


def chainF(n: int, e: bool) -> Fml:
    """c_0 = 0, c_{i+1} = c_i ⊕ x_i y_i, c_n = e, with c_i = 2n + i (Lean: `Code.chainF`)."""
    return ([[(2 * n, False)]] + [C for i in range(n) for C in xorC(i, n + i, 2 * n + i, 2 * n + i + 1)]
            + [[(3 * n, e)]])


def cssF(w: int, n: int, psi: Fml, e: bool) -> Fml:
    """Lean: `Code.cssF w n ψ e = rowsF w n ψ ++ chainF n e ++ compF n (2n + 1)`."""
    return [D for C in psi for D in rowF(w, n, C)] + chainF(n, e) + compF(n, 2 * n + 1)


def codeCNF(H1: Checks, H2: Checks) -> Fml:
    """The checks of H1 as positive clauses, those of H2 as negative ones (Lean: `Code.codeCNF`)."""
    return [[(j, True) for j in r] for r in H1] + [[(j, False) for j in r] for r in H2]


def code_word(s: int, n: int, H1: Checks, H2: Checks) -> list[bool]:
    """The input `unary s ++ SatFree.enc (codeCNF H1 H2)`."""
    return unary(s) + enc_free(n, codeCNF(H1, H2))


def preQ(w: int, e: bool, x: Sequence[bool]) -> tuple[int, int, Fml]:
    """The front end (Lean: `CodeTM.preQ`)."""
    n, psi = read_free(rest(x))
    return (5 * n + 2, (ones(x) if e else 0) + 2 * n + 1, cssF(w, n, psi, e))


def css_word(w: int, x: Sequence[bool]) -> int:
    """The machine `codeM`: K = SIZED(preQ false), N = SIZED(preQ true), then 2N/K."""
    return 2 * _sized(preQ(w, True, x)) // _sized(preQ(w, False, x))


def num_log(H1: Checks, H2: Checks, n: int, s: int) -> int:
    """The number of logical operators of weight s, by the machine (Lean: `CodeTM.css_counts`)."""
    w = max((len(r) for r in H1 + H2), default=0)
    return css_word(w, code_word(s, n, H1, H2))


def distance(H1: Checks, H2: Checks, n: int) -> int | None:
    """The least weight of a logical operator, None if there is none."""
    return next((s for s in range(1, n + 1) if num_log(H1, H2, n, s) > 0), None)


# ---------------------------------------------------------------------------------------------
# brute force


def in_ker(H: Checks, x: Sequence[int]) -> bool:
    return all(sum(x[j] for j in r) % 2 == 0 for r in H)


def in_rowspace(H: Checks, x: Sequence[int], n: int) -> bool:
    """x ∈ the span over 𝔽₂ of the rows of H (Gaussian elimination on bitmasks)."""
    basis: dict[int, int] = {}
    for r in H:
        v = 0
        for j in r:
            v ^= 1 << j
        while v:
            h = v.bit_length() - 1
            if h not in basis:
                basis[h] = v
                break
            v ^= basis[h]
    v = sum(1 << j for j in range(n) if x[j])
    while v:
        h = v.bit_length() - 1
        if h not in basis:
            return False
        v ^= basis[h]
    return True


def brute_num_log(H1: Checks, H2: Checks, n: int, s: int) -> int:
    """#{x : |x| = s, x ∈ ker H1, x ∉ rowspace H2} (Lean: `Code.numLog`)."""
    return sum(1 for x in product((0, 1), repeat=n)
               if sum(x) == s and in_ker(H1, x) and not in_rowspace(H2, x, n))
