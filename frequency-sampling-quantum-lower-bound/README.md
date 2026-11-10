# Sampling frequency coefficients on a set of K characters needs Ω(√(M/K)) quantum queries

Written 10 Nov 2026.

## Problem

Let S ⊆ {0,1}^m be a nonempty set of K characters, M = 2^m, and for a Boolean function f: {0,1}^m → {±1} let Z_s(f) = M^{−1/2} Σ_σ f(σ)χ_s(σ). In [1, Definition 3.7], the task Samp_S(ε) is to output, from queries to f, a sample within total variation distance ε of the distribution p_f on S ∪ {⊥} that gives ⊥ probability 1/D_f and s ∈ S probability Z_s(f)²/(K D_f), where D_f = 1 + K^{−1} Σ_{s∈S} Z_s(f)². [1, Theorem 3.10] solves it with O(√(M/K)(1 + log(1/ε))) quantum queries, and [1, Theorem 3.9] shows that classical algorithms need Ω(M/log K) queries at ε = 1/100. [1, Section 6.4, problem 3] asks whether Ω(√(M/K)) quantum queries are needed for every S. For S = {0,1}^m this is the frequency sampling task of [3] with ⊥ added.

## Result

**Theorem 1.** There is an absolute constant c_0 > 0 such that for every m ≥ 1, every nonempty S ⊆ {0,1}^m and every ε ≤ 1/5, every quantum algorithm for Samp_S(ε) makes at least c_0 √(M/K) queries to f, in the oracle model of [1, Section 2.5].

With [1, Theorem 3.10], the quantum query complexity of Samp_S(ε) is Θ(√(M/K)) for every S and every constant ε ∈ (0, 1/5], which includes the error 1/100 at which [1, Theorem 3.9] states the classical bound.

## Proof

**Large K.** If K > M/400 then √(M/K) < 20, and it suffices that one query is needed. Without queries the output law q is fixed. If K ≥ 2, take s ≠ t in S and f = χ_s, f′ = χ_t. Then p_f(s) = p_{f′}(t) = M/(K + M) ≥ 1/2, so p_f and p_{f′} are at total variation at least 1/2, and q is at distance at least 1/4 > ε from one of them. If K = 1 and S = {s}, compare f = χ_s with f′ = χ_t for some t ≠ s: then Z_s(f′) = 0, and the targets give ⊥ probability 1/(1 + M) and 1, again at distance at least 1/2.

**Small K.** Let K ≤ M/400 (so M ≥ 512), c = 99, fix s_0 ∈ S, and let Σ* = 2⌈√(cKM)/2⌉. This is an even integer with Σ*² ≥ cKM and Σ* ≤ √(99/400) M + 2 ≤ M/√2, so Σ*² ≤ M²/2.

*Counting problem.* Given g: {0,1}^m → {±1} with Σ_σ g(σ) ∈ {0, Σ*}, decide which, with error below 1/2 − δ for a fixed δ > 0. The numbers of −1 values are M/2 and t = (M − Σ*)/2. They differ by Δ = Σ*/2, t is the one farther from M/2, and t(M − t) = (M² − Σ*²)/4 ≥ M²/8. By [2, Corollary 1.2], which allows randomized algorithms with any error below 1/2, every quantum algorithm needs Ω(√(t(M − t))/Δ) = Ω(M/Σ*) = Ω(√(M/(cK))) queries to g, with the constant depending on δ.

*Reduction.* Draw a uniformly random permutation π of {0,1}^m and put f(σ) = g(π(σ)) χ_{s_0}(σ). A query O_f|σ, b⟩ = |σ, b ⊕ (1 − f(σ))/2⟩ is O_g applied to |π(σ), b⟩ followed by a fixed bit flip where χ_{s_0}(σ) = −1, with fixed circuits for π before and after; the same holds for its inverse and its controlled version, so each costs one query to g. Run the sampler for Samp_S(ε) once on f, and answer Σ* if the output is s_0 and 0 otherwise. For every fixed g, the function h = g∘π is uniform among the functions with the same sum, and

Z_{s_0}(f) = M^{−1/2} Σ_σ h(σ),  Z_s(f) = Z_{s⊕s_0}(h) for all s.

Write R = Σ_{u∈U} Z_u(h)², where U = {s ⊕ s_0: s ∈ S, s ≠ s_0} has K − 1 nonzero elements, so that p_f(s_0) = Z_{s_0}(f)²/(K + Z_{s_0}(f)² + R). For h uniform with sum Σ and u ≠ 0, E[h(σ)h(τ)] = (Σ² − M)/(M(M − 1)) for σ ≠ τ, and Σ_σ χ_u(σ) = 0, so E Z_u(h)² = 1 − (Σ² − M)/(M(M − 1)) ≤ M/(M − 1). Hence E R ≤ K, and R ≤ 20K with probability at least 19/20 over π by the mean bound.

- If Σ g = 0, then Z_{s_0}(f) = 0, so p_f(s_0) = 0 and the sampler outputs s_0 with probability at most ε ≤ 1/5.
- If Σ g = Σ*, then Z_{s_0}(f)² = Σ*²/M ≥ cK. When R ≤ 20K, p_f(s_0) ≥ cK/(cK + K + 20K) = 99/120, since x/(K + x + R) increases in x, and the sampler outputs s_0 with probability at least 99/120 − 1/5 = 0.625.

So the procedure is correct with probability at least 4/5 for every g with sum 0 and at least (19/20) · 0.625 > 0.59 for every g with sum Σ*. If the sampler makes Q queries, the counting bound with δ = 0.09 gives Q = Ω(√(M/(cK))), so Q ≥ c_0 √(M/K).

## Remarks

- The hard inputs place a large coefficient on one fixed character, so the bound holds already when S and s_0 are known in advance. The remaining K − 1 coefficients only need to stay of typical size, which the random relabelling π ensures.
- For S = {0,1}^m, D_f = 2 for every f, so ⊥ has probability 1/2, and the bound is the trivial Ω(1).

## Check

`sim/check.py` (about 5 seconds) checks the reduction identities, the formula for E Z_u(h)² (exactly for M = 8 and by sampling for M = 64), the bound p_f(s_0) ≥ 99/120 with probability at least 19/20 on sampled instances with sum Σ*, the inequalities cKM ≤ Σ*² ≤ M²/2 for K ≤ M/400 and 2^9 ≤ M ≤ 2^39, and the total variation distances used for large K. Output in `sim/out.txt`.

## References

1. S. Chakrabarti, D. Herman, J. L. Kim, G. Ozgul. The Quartic Gap Between Quantum and Dequantized Algorithms for Linear Algebra Is Tight. arXiv:2610.42069 (2026).
2. A. Nayak, F. Wu. The quantum query complexity of approximating the median and related statistics. Proc. 31st ACM Symposium on Theory of Computing, 384-393 (1999), arXiv:quant-ph/9804066.
3. S. Aaronson, A. Ambainis. Forrelation: A Problem that Optimally Separates Quantum from Classical Computing. SIAM Journal on Computing 47, 982-1038 (2018), arXiv:1411.5729.
