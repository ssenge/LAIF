# Sampling frequency coefficients on a set of K characters needs Ω(√(M/K)) quantum queries

Written 10 Nov 2026.

## Problem

Let S ⊆ {0,1}^m be a nonempty set of K characters, M = 2^m, and for a Boolean function f: {0,1}^m → {±1} let Z_s(f) = M^{−1/2} Σ_σ f(σ)χ_s(σ). In [1, Definition 3.7], the task Samp_S(ε) is to output, from queries to f, a sample within total variation distance ε of the distribution p_f on S ∪ {⊥} that gives ⊥ probability 1/D_f and s ∈ S probability Z_s(f)²/(K D_f), where D_f = 1 + K^{−1} Σ_{s∈S} Z_s(f)². [1, Theorem 3.10] solves it with O(√(M/K)(1 + log(1/ε))) quantum queries, and [1, Theorem 3.9] shows that classical algorithms need Ω(M/log K) queries at ε = 1/100. [1, Section 6.4, problem 3] asks whether Ω(√(M/K)) quantum queries are needed for every S. For S = {0,1}^m this is the frequency sampling task of [3] with ⊥ added.

## Result

**Theorem 1.** There is an absolute constant c_0 > 0 such that for every m, every nonempty S ⊆ {0,1}^m and every ε ≤ 1/100, every quantum algorithm for Samp_S(ε) makes at least c_0 √(M/K) queries to f, in the oracle model of [1, Section 2.5].

With [1, Theorem 3.10], the quantum query complexity of Samp_S(ε) is Θ(√(M/K)) for every S and every constant ε ≤ 1/100, the error at which [1, Theorem 3.9] states the classical bound.

## Proof

**Large K.** If K > M/400 then √(M/K) < 20, and it suffices that one query is needed. Without queries the output law q is fixed. If K ≥ 2, take s ≠ t in S and f = χ_s, f′ = χ_t. Then p_f(s) = p_{f′}(t) = M/(K + M) ≥ 1/2, so p_f and p_{f′} are at total variation at least 1/2, and q is at distance at least 1/4 from one of them. If K = 1, compare f = χ_s with a balanced f, whose targets give ⊥ probability 1/(1 + M) and 1.

**Small K.** Let K ≤ M/400, c = 99, fix s_0 ∈ S, and let Σ* = 2⌈√(cKM)/2⌉, an even integer with cKM ≤ Σ*² ≤ M²/2.

*Counting problem.* Given g: {0,1}^m → {±1} with Σ_σ g(σ) ∈ {0, Σ*}, decide which. The numbers of −1 values are M/2 and t = (M − Σ*)/2, which differ by Δ = Σ*/2, and t(M − t) = (M² − Σ*²)/4 ≥ M²/8. By the lower bound for approximate counting [2], every quantum algorithm needs Ω(√(t(M − t))/Δ) = Ω(M/Σ*) = Ω(√(M/(cK))) queries to g.

*Reduction.* Draw a uniformly random permutation π of {0,1}^m and put f(σ) = g(π(σ)) χ_{s_0}(σ). A query to f is one query to g together with fixed circuits for π and χ_{s_0}; query complexity does not count these. Run the sampler for Samp_S(ε) r = 1500 times on f, and answer Σ = 0 if at least 44 of the outputs are ⊥. For every fixed g, the function h = g∘π is uniform among the functions with the same sum, and

Z_{s_0}(f) = M^{−1/2} Σ_σ h(σ),  Z_s(f) = Z_{s⊕s_0}(h) for all s.

- If Σ g = Σ*, then D_f ≥ 1 + Z_{s_0}(f)²/K = 1 + Σ*²/(MK) ≥ 1 + c = 100, so p_f(⊥) ≤ 1/100 and each run outputs ⊥ with probability at most 1/100 + ε ≤ 0.02.
- If Σ g = 0, then Z_{s_0}(f) = 0 and D_f = 1 + R/K with R = Σ_{u∈U} Z_u(h)², where U = {s ⊕ s_0: s ∈ S, s ≠ s_0} has K − 1 nonzero elements. For h uniform with sum Σ and u ≠ 0, E[h(σ)h(τ)] = (Σ² − M)/(M(M − 1)) for σ ≠ τ, and Σ_σ χ_u(σ) = 0, so E Z_u(h)² = 1 − (Σ² − M)/(M(M − 1)). At Σ = 0 this is M/(M − 1), so E R ≤ K, and R ≤ 20K with probability at least 19/20 over π by the mean bound. Then D_f ≤ 21 and each run outputs ⊥ with probability at least 1/21 − 1/100 ≥ 0.0376.

The runs are independent given f. Binomial tails with r = 1500 and threshold 44 give error at most 0.036 when the per-run probability is at least 0.0376 and at most 0.01 when it is at most 0.02. So the procedure answers correctly with probability at least (19/20)(1 − 0.036) > 0.9 for every g with sum 0 and at least 0.99 for every g with sum Σ*. If the sampler makes Q queries, then 1500 Q = Ω(√(M/(cK))), so Q ≥ c_0 √(M/K).

## Remarks

- The hard inputs place a large coefficient on one fixed character, so the bound holds already when S and s_0 are known in advance; the remaining K − 1 coefficients only need to stay of typical size, which the random relabelling π ensures.
- The error level 1/100 and the constants c = 99, r = 1500 are chosen for a short proof and are not optimised.

## Check

`sim/check.py` (about 1 minute) checks the reduction identities, the formula for E Z_u(h)² (exactly for M = 8 and by sampling for M = 64), the tail P(D_f > 21) on sampled instances, the binomial error bounds for r = 1500, the inequalities cKM ≤ Σ*² ≤ M²/2 for K ≤ M/400 and 2^9 ≤ M ≤ 2^39, and the zero-query case. Output in `sim/out.txt`.

## References

1. S. Chakrabarti, D. Herman, J. L. Kim, G. Ozgul. The Quartic Gap Between Quantum and Dequantized Algorithms for Linear Algebra Is Tight. arXiv:2610.42069 (2026).
2. A. Nayak, F. Wu. The quantum query complexity of approximating the median and related statistics. Proc. 31st ACM Symposium on Theory of Computing, 384-393 (1999), arXiv:quant-ph/9804066.
3. S. Aaronson, A. Ambainis. Forrelation: A Problem that Optimally Separates Quantum from Classical Computing. SIAM Journal on Computing 47, 982-1038 (2018), arXiv:1411.5729.
