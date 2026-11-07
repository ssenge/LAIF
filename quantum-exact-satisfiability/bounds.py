"""Quantum bases for Exact Satisfiability: square roots of the classical branching bases."""
import math

for name, b in (("XSAT, DPLL with a nonstandard measure", 1.1674),):
    q = math.ceil(math.sqrt(b) * 1e4) / 1e4
    assert math.sqrt(b) <= q
    # crossover with the bound 2^((n - M')/2) of the subspace search: equal when M' = (1 - 2 log2 q) n
    print(f"{name}: sqrt({b}) = {math.sqrt(b):.6f} <= {q}; crossover M'/n = {1 - 2 * math.log2(q):.4f}")
