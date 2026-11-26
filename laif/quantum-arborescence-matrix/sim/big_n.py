import math, random, sys
from grouped_cost import grouped
from contraction_cost import chain_family
from hard_families import block_chain
rng = random.Random(21)
for n in (129, 257, 513):
    for name, W in (("chain", chain_family(n, rng)), ("b8", block_chain(n, 8, rng)), ("b2", block_chain(n, 2, rng))):
        _, cost = grouped(W); L = 1 + math.log2(n)
        print(f"{name} n={n} raw/n^1.5={cost / n ** 1.5:8.1f} /(n^1.5 L)={cost / (n ** 1.5 * L):6.2f} /(n^1.5 L^2)={cost / (n ** 1.5 * L * L):6.3f}", flush=True)
