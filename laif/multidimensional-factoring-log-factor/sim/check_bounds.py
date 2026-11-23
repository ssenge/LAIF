"""Numeric checks for the second-moment bound with primes up to X = e^{21d}.

* the character-sum bound: 2A (d^2 + 21 d)^3 e^{-10.5 d} <= e^{-10 d} once d >= d1(A), for several A;
* the sum over at most e^{d^2} characters: e^{d^2} 30^{d/2} e^{-5 d^2} <= d^{-2d} for every d >= 2;
* the cost of the product of d primes with m bits: m d log d log(m d), for m = log2(d^{1000 d}) and m = log2(e^{21 d}),
  compared over d = sqrt(n); their ratio grows like log d.
"""
import math

# (1) the bound on E[psi(b)] beats e^{-10d} from some d on, for any fixed constant A
for A in [1, 10, 1e3, 1e6]:
    d1 = next(d for d in range(2, 10**4)
              if all(math.log(2 * A) + 3 * math.log(e * e + 21 * e) - 10.5 * e <= -10 * e for e in range(d, d + 200)))
    print(f"A={A:g}: 2A (d^2+21d)^3 e^(-10.5d) <= e^(-10d) for all checked d >= {d1}")
    assert d1 < 10**4

# (2) the union over all characters, in logs: d^2 + (d/2) log 30 - 5 d^2 <= -2 d log d
for d in range(2, 5000):
    assert d * d + d / 2 * math.log(30) - 5 * d * d <= -2 * d * math.log(d)
print("e^{d^2} 30^{d/2} e^{-5d^2} <= d^{-2d} for 2 <= d < 5000")

# (3) product cost m d log d log(md), with d = sqrt(n): old m = 1000 d log2 d, new m = 21 d / ln 2
for n in [2**10, 2**12, 2**14, 2**16]:
    d = math.isqrt(n)
    T = lambda m: m * d * math.log(d) * math.log(m * d)
    old, new = T(1000 * d * math.log2(d)), T(21 * d / math.log(2))
    r = old / new / math.log2(d)
    print(f"n={n}: product cost old/new divided by log2 d = {r:.1f}")
    assert r >= 30  # the saving is at least a constant times log d
