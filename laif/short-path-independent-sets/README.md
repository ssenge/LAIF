# Maximum independent set on random regular graphs: generalized short-path search against listing maximal independent sets

_24 November 2026_

The generalized short-path algorithm of [1] finds a maximum independent set in time O*(T^(1/2 − c)). Here T = 1/π_λ(X*) is the expected number of samples that classical Markov chain search needs. That search draws independent sets x with probability λ^|x| / Z from the single-site heat-bath chain at fugacity λ until it hits the set X* of maximum independent sets. The constant c > 0 measures the gain over a quadratic speedup. It was noted in [1] that it is still unclear how Markov chain search compares with the best classical algorithms for this problem, and [1, Remark 5.23] compares its runtime guarantee 2^(κn) [1, Proposition 5.22] with the generic bound 1.1996^n [9]. A survey [2, Sec. 8.1] lists the problem: for maximum independent set on regular graphs of sufficiently high degree, the short-path algorithm is stated to give a super-quadratic speedup over all known algorithms.

For short-path algorithms for constraint satisfaction, classical algorithms with the same gain were given in [5]. This folder compares the algorithm for maximum independent set with a plain classical algorithm: listing all maximal independent sets with polynomial delay [3, 4] and keeping the largest.

## Results

**Theorem 1 (every graph).** For every graph G and every 0 < λ ≤ 1, the number i(G) of independent sets satisfies i(G) ≤ |X*| · T. So Markov chain search at any fugacity λ ≤ 1 draws at least as many samples as there are independent sets, up to the number of maximum independent sets. Proof: T = Σ_x λ^(|x| − |x*|) / |X*|, and every term is at least 1.

**Theorem 2 (listing, random d-regular graphs).** With probability 1 − o(1), listing the maximal independent sets of a random d-regular graph on n vertices takes time poly(n) · e^(ψ(d) n). Here ψ(d) is the maximum over a of the first-moment exponent of the number of maximal independent sets of size a·n. Each such set must be independent and its d·a·n edges must reach every other vertex. Markov's inequality applied to the first moment gives the high-probability bound.

**Theorem 3 (the constant c, every graph).** In [1, Theorem 4.2], used in [1, Theorem 5.17] for 0 < λ ≤ (1 − ξ)λ_c with λ_c = (d − 1)^(d−1) / (d − 2)^d and a constant ξ > 0, the constant is c = η(1 − η)|E*| b / (2Δ_P ln T) with b < (2/3) γ ω ln T. For this chain:

- the stability constant obeys Δ_P ≥ |x*| / (n(1 + λ)), from its definition at a maximum independent set, where only removals are possible (if instead Δ_P > η|x*|, then c < 1/(3n));
- the entropy constant obeys ω ≤ δ/2 ≤ 1/(2n): the first inequality holds for every reversible chain in the normalization of [1, Definition 2.4], and the second follows from the test function 1{v ∈ x} and the bound λ/(1 + λ) on a vertex marginal;
- the spectral-density exponent obeys γ ≤ 1, since π(E ≤ (1 − η)E*) ≥ π(E*).

Since |E*| = |x*| and η(1 − η) ≤ 1/4, these give c < (1 + λ)/24 on every graph. This is at most 0.0482 for d ≥ 20, and tends to 1/24 as d grows. In [1, Theorem 4.3], used in [1, Theorems 5.19 and 5.21] and so at λ = λ_c, b < δ/4 gives c = O(1/n).

**Corollary (no super-quadratic speedup over listing).** With high probability, ln T ≥ n · L(d, λ), where L = α_g ln(1/λ) − max_(a ≥ α_g) φ(a) comes from the term of the empty set, the bound |x*| ≥ α_g n with α_g the limit of the greedy algorithm [8], and a first-moment bound on |X*| [6]. Whenever ψ(d) ≤ (1 − 2c) L(d, λ), the listing time is at most the square of the short-path runtime bound. Then that bound gives no super-quadratic speedup over listing.

- For 0 < λ ≤ λ_c, L decreases and the bound on c increases with λ, so λ = λ_c is the worst case. Numerically, the inequality holds for every integer d in [76, 449] and for every sampled d in [449, 10⁷] (log-spaced degrees), with a relative margin of at least 0.23%, reached at d = 76. It fails at every d ≤ 75 with the greedy bound used here. The guarantee 2^(κn) of [1, Proposition 5.22] lies below 1.1996^n for d ≥ 307.
- For every sufficiently large d, both regimes of [1] are covered, including λ up to 1/(2√(d − 1) − 1) [1, Theorem 5.21], if the independence ratio of random d-regular graphs is (2/d)(ln d − ln ln d + 1 − ln 2 + o(1)) [7], used in place of α_g. Then (1 − 2c) L grows like (11/6) ln²d / d at λ_c and like (11/12) ln²d / d at the larger fugacity, while ψ(d) ≤ (ln d + ln²d / 2) / d.

This hints at a possible gap in the entry of [2, Sec. 8.1]: on random regular graphs of high degree, the proved runtime of the short-path algorithm does not appear to be super-quadratically faster than listing maximal independent sets.

| d | Listing maximal sets, e^(ψ n) | Search guarantee [1, Prop. 5.22], 2^(κ n) | Bound on c | Square of the short-path bound, at least | Listing within the square |
|---|---|---|---|---|---|
| 20 | 1.16607^n | 1.9109^n | 0.0481 | 1.07795^n | no |
| 76 | 1.08591^n | 1.4896^n | 0.0432 | 1.08612^n | yes |
| 100 | 1.07356^n | 1.4147^n | 0.0428 | 1.07819^n | yes |
| 200 | 1.04854^n | 1.2657^n | 0.0422 | 1.05694^n | yes |
| 449 | 1.02882^n | 1.1532^n | 0.0419 | 1.03602^n | yes |
| 10 000 | 1.00305^n | 1.0154^n | 0.0417 | 1.00408^n | yes |
| 100 000 | 1.00049^n | 1.0024^n | 0.0417 | 1.00065^n | yes |
| 1 000 000 | 1.00007^n | 1.0004^n | 0.0417 | 1.00010^n | yes |

All rows are at λ = λ_c, the supremum of the range of [1, Theorem 5.17]. ψ is rounded up by a relative 10⁻⁴. The "square" column is e^((1 − 2c)L n), a lower bound on the square of the short-path runtime. "No" means only that the bounds used here are not strong enough.

**Estimates.** An annealed estimate takes |x*| at the first-moment threshold and the number of independent sets of each size at its first moment. With this estimate, listing stays within the square of the short-path runtime whenever c < c*, with c* between 0.31 and 0.38 at both fugacities for 20 ≤ d ≤ 10⁷. These values are not proved bounds.

## Scope

- **Graphs.** Random d-regular graphs, the family of [1, Proposition 5.22] and [2, Sec. 8.1], with high probability over the graph. Worst-case regular graphs are not covered.
- **Lean.** Theorem 1, for any finite family of configurations with a size function (`ChainSearch.card_le_card_opt_mul_samples`) and in its form for the independent sets of a finite simple graph (`ChainSearch.indepSets_card_le`). Only the standard axioms are used (`lean/axioms.txt`).
- **Assuming.** The greedy limit α_g = (1 − (d − 1)^(−2/(d−2)))/2 for random d-regular graphs [8], polynomial-delay listing of maximal independent sets [3, 4], and, for the statement for every sufficiently large d, the asymptotic independence ratio of [7].
- **Not formalized.** Theorems 2 and 3 and the corollary are written proofs with numerical evaluation of the exponents (`sim/mis_exponents.py`). Above d = 449 the range up to 10⁷ is sampled, not checked for every integer d.
- **Short-path runtime.** Only the bound of [1] is compared. The true runtime of the short-path algorithm may be smaller than that bound.

## Files

- `sim/mis_exponents.py`: the exponents φ, ψ, the bound on c, the guarantee κ, the annealed estimates and the table (`python -I mis_exponents.py out.json`). `python -I mis_exponents.py test` checks the closed forms against exact first moments, the limit ψ against exact counts of maximal sets for n = 200 and 400, Theorem 1 and the count of maximal sets by brute force on small graphs, and the spectral gap ≤ 1/n and the stability bound on the exact chain of small graphs.
- `lean/ChainSearch/Basic.lean`: Theorem 1. `lean/Axioms.lean` prints the axioms of both theorems.
- `data/exponents.json`: all quantities for 624 degrees from 6 to 10⁷.

## Use of AI

The analysis, code and text were produced with Claude Opus 5.5.

## References

1. S. Chakrabarti, D. Herman, G. Ozgul, S. Zhu, B. Augustino, T. Hao, Z. He, R. Shaydulin, M. Pistoia. Generalized short path algorithms: towards super-quadratic speedup over Markov chain search for combinatorial optimization. arXiv:2410.23270 (v2).
2. The compendium of super-quadratic computational quantum advantages. arXiv:2610.32595.
3. S. Tsukiyama, M. Ide, H. Ariyoshi, I. Shirakawa. A new algorithm for generating all the maximal independent sets. SIAM Journal on Computing 6, 505 (1977).
4. D. S. Johnson, M. Yannakakis, C. H. Papadimitriou. On generating all maximal independent sets. Information Processing Letters 27, 119 (1988).
5. F. Le Gall, S. Tamaki. Dequantizing short-path quantum algorithms. arXiv:2604.12131.
6. B. Bollobás. The independence ratio of regular graphs. Proceedings of the American Mathematical Society 83, 433 (1981).
7. A. M. Frieze, T. Łuczak. On the independence and chromatic numbers of random regular graphs. Journal of Combinatorial Theory, Series B 54, 123 (1992).
8. N. C. Wormald. Differential equations for random processes and random graphs. Annals of Applied Probability 5, 1217 (1995).
9. M. Xiao, H. Nagamochi. Exact algorithms for maximum independent set. Information and Computation 255, 126 (2017).
