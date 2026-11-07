# Optimal quantum mean estimation for heavy-tailed random vectors

Written 6 Nov 2026.

## Problem

Let X be a random vector in R^d with mean μ and E‖X − μ‖^p ≤ σ^p, for a tail index p ∈ (1, 2]. Here ‖·‖ is the ℓ₂ norm. Given a quantum sampling oracle O_X and its inverse [1, Definition 2.2], the task is to output μ̃ with ‖μ̃ − μ‖ ≤ ε, with probability at least 2/3 (or 1 − δ), for ε ∈ (0, σ) [1, Problem 3.1].

Write

b = p/(2(p − 1)),  a = (3p − 4)/(4(p − 1)).

**Known bounds.**

- **Classical.** The optimal classical cost is Θ̃((σ/ε)^{2b}) = Θ̃((σ/ε)^{p/(p−1)}) samples.
- **Quantum upper bound.** [1, Theorem 3.4] estimates μ with Õ(√d (σ/ε)^b) queries. It truncates at the radius where the bias is ε/3, then applies the bounded-variance estimator of [2].
- **Quantum lower bounds** [1, Theorem 3.9]:
  - Ω((σ/ε)^b) for p ∈ (1, 4/3];
  - for p ∈ (4/3, 2]: Ω(d^a (σ/ε)^b) when 1 ≤ d ≤ (σ/ε)², and Ω((σ/ε)²) when d ≥ (σ/ε)².

Since a < 1/2 for p < 2, the bounds match only at p = 2 or for constant d. [1, Remark 3.11] leaves the joint dependence on d, σ and ε open.

## Results

**Theorem 1.** For every p ∈ (1, 2] and d ≥ 1, the problem can be solved with

N = Õ( (σ/ε)^b · max{ 1, min{ d^a, (σ/ε)^{2−b} } } )

queries to O_X and O_X^†, at failure probability δ. The hidden factors are powers of log(1/δ) and log(σ/ε), and log d where the estimator of [2] is used, which happens only for d ≤ 4^p(σ/ε)², so that log d = O(log(σ/ε)) there. Constants and log powers depend on p, for example through 3^{1/(p−1)}. By regime:

| tail index | dimension | queries |
|---|---|---|
| p ∈ (1, 4/3] | every d | Θ̃((σ/ε)^{p/(2(p−1))}) |
| p ∈ (4/3, 2] | d ≤ (σ/ε)² | Θ̃(d^{(3p−4)/(4(p−1))} (σ/ε)^{p/(2(p−1))}) |
| p ∈ (4/3, 2] | d ≥ (σ/ε)² | Θ̃((σ/ε)²) |

Each line matches the lower bound of [1, Theorem 3.9] up to logarithmic factors. So, for each fixed p, Theorem 1 settles the joint dependence on d, σ and ε for [1, Problem 3.1]. [1, Remark 3.6] states an advantage over classical estimators for d ≲ (σ/ε)^{p/(p−1)}; Theorem 1 gives one in every dimension for p < 2.

- For p ≤ 4/3 the cost is free of d.
- For all p < 2 it is below the classical (σ/ε)^{p/(p−1)} in every dimension.
- For p < 2, in each regime the √d of [1, Theorem 3.4] improves to d^a, with a < 1/2. At p ≤ 4/3 the factor goes away entirely, and in high dimension the cost is capped at (σ/ε)².

**Corollary 2 (nonconvex optimization).** Use the estimator of Theorem 1 inside the normalized gradient method of [1, Algorithm 3], with the parameters of [1, Theorem 4.4]. Assume heavy-tailed stochastic gradients with index p and scale σ, an L-smooth objective and Δ_f = f(x_0) − f*. Then iterates with (1/T) Σ_t ‖∇f(x_t)‖ ≤ ε with probability 1 − δ take

Õ( LΔ_f ε^{−2} · (σ/ε)^b · max{ 1, min{ d^a, (σ/ε)^{2−b} } } )

queries to the quantum stochastic gradient oracle. In every dimension this is at most Õ(LΔ_f ε^{−2} (σ/ε)^{max{b, 2}}). The classical lower bound Ω(ε^{−(3p−2)/(p−1)}) = Ω(ε^{−2−2b}) of [3] is proved for constant σ, L and Δ_f, by a construction in dimension of order LΔ_f ε^{−2} or more. Since max{b, 2} < 2b for p < 2, the quantum method beats it, by a polynomial factor, in the dimensions where it holds. [1, Theorem 4.4] gives Õ(√d ε^{−2}(σ/ε)^b), which improves on the classical bound only for d ≲ ε^{−p/(p−1)}.

## Algorithm

The idea is to treat each dyadic magnitude shell of X − μ by the cheaper of two methods:

- **Quantum.** Apply the bounded-variance estimator of [2] to the whole shell.
- **Classical after amplification.** Find the rare event of the shell by amplitude amplification, then average classical conditional samples, which costs no dimension factor.

Below a crossover radius the first is cheaper, above it the second.

1. **Centre.** Obtain ζ with ‖ζ − μ‖ ≤ σ from O(log(1/δ)) classical samples [1, Theorem 2.5]. Put Y = X − ζ. Then E‖Y‖^p ≤ S := 2^p σ^p, and E Y = μ − ζ.
2. **Truncate.** Put τ = (3S/ε)^{1/(p−1)}. Then ‖E[Y·1{‖Y‖ > ρ}]‖ ≤ E‖Y‖^p/ρ^{p−1} ≤ ε/3 for every ρ ≥ τ.
3. **Crossover radius.** Put r* = (S/(√d ε))^{1/(p−1)} and r_0 = min{max{r*, σ}, τ}.
4. **Inner part.** Let W = Y·1{‖Y‖ ≤ r_0}, so E‖W‖² ≤ S r_0^{2−p}. Estimate E W to error ε/3 by the cheaper of:
   - the estimator of [2], with Õ(√(d S r_0^{2−p})/ε) queries. As in [1, Theorem 3.4], it is used in the oracle model of [1, Definition 2.2], see [1, Lemma 3.3 and Appendix A.1]. Only the case d ≤ 4^p(σ/ε)² uses it;
   - the geometric median of means of classical samples [4], with O(S r_0^{2−p} log(1/δ)/ε²) samples.
5. **Shells.** For j = 0, …, J − 1 with J = ⌈log₂(τ/r_0)⌉, take the shell A_j = {r_j < ‖Y‖ ≤ 2r_j} with r_j = 2^j r_0. Its probability is π_j ≤ S/r_j^p. Put ε_1 = ε/(3J) and Δ_j = ε_1/(8r_j).
   1. Estimate π_j by amplitude estimation [5] to additive error Δ_j.
   2. If π̂_j < ε_1/(4r_j), set the shell estimate to 0.
   3. Otherwise π_j ≥ Δ_j. Draw n_j = ⌈C (r_j π̂_j/ε_1)² log(J/δ)⌉ samples of Y conditioned on A_j, each by fixed-point amplitude amplification [6] from the lower bound π̂_j/2. Let m̂_j be their geometric median of means [4], and set the shell estimate to π̂_j m̂_j.
6. **Output.** Return μ̃ = ζ + (estimate of E W) + Σ_j (shell estimates). The shells cover (r_0, r_J] with r_J = 2^J r_0 ≥ τ.

## Proofs

**Correctness.** The mean of Y splits as

E Y = E W + Σ_j E[Y 1_{A_j}] + E[Y 1{‖Y‖ > r_J}].

The last term is at most ε/3 in norm by step 2, since r_J ≥ τ, and the first is estimated to ε/3 by step 4. It remains to show that each shell estimate is within ε_1 of E[Y 1_{A_j}] = π_j m_j, where m_j = E[Y | A_j] and ‖m_j‖ ≤ 2r_j.

- **Zero branch.** π_j < ε_1/(4r_j) + Δ_j < ε_1/(2r_j), so ‖π_j m_j‖ < ε_1.
- **Sampling branch.** Here π_j ≥ ε_1/(4r_j) − Δ_j ≥ Δ_j, so π̂_j ≤ 2π_j. Then
  ‖π̂_j m̂_j − π_j m_j‖ ≤ |π̂_j − π_j| ‖m_j‖ + π̂_j ‖m̂_j − m_j‖ ≤ ε_1/4 + 2π_j ‖m̂_j − m_j‖.
  The conditional samples have E‖Y − m_j‖² ≤ 4r_j² given A_j, and π_j ≤ π̂_j + Δ_j ≤ 3π̂_j/2, so n_j ≥ (4C/9)(r_j π_j/ε_1)² log(J/δ). So by [4] the geometric median of means has ‖m̂_j − m_j‖ ≤ 3ε_1/(8π_j) with probability 1 − δ/(4J), for a suitable absolute constant C.
- **Exact conditioning.** Amplitude amplification acts in the plane spanned by the normalised marked and unmarked parts of O_X|0⟩. A marked outcome is therefore distributed exactly as Y given A_j.

The subroutines are the centring, the inner part, and two per shell. Giving each failure probability δ/(2J + 2), a union bound gives total error ≤ ε with probability 1 − δ.

**Cost.** Write Q(r) = √d √(S r^{2−p})/ε and C(r) = S^{3/2} r^{2−3p/2}/ε². Up to log factors and constants depending on p:

- the inner part costs min{Q(r_0), S r_0^{2−p}/ε²};
- shell j costs O(n_j/√π_j) = Õ(r_j² π_j^{3/2}/ε_1²) ≤ Õ(C(r_j)) for sampling, since r² π^{3/2} increases in π and π_j ≤ S r_j^{−p};
- amplitude estimation costs O(√π_j/Δ_j + 1/√Δ_j) per shell.

These terms are bounded as follows.

1. **Amplitude estimation.** Over all shells this is Õ(√S τ^{1−p/2}/ε + √(τ/ε)) = Õ((σ/ε)^b). Both terms reduce to exponent b by τ = Θ((σ/ε)^{1/(p−1)} σ).
2. **Crossover.** By the choice of r*, Q(r*) = C(r*). Q(r*) = Θ(d^a (σ/ε)^b), since

   1/2 − (2 − p)/(4(p − 1)) = a  and  1 + (2 − p)/(2(p − 1)) = b.
3. **Case p > 4/3, d ≤ 4^p(σ/ε)².** Then r_0 = r*, because r* ≥ σ in this range and r* ≤ τ always. C decreases in r, so the shells sum to Õ(C(r*)). The inner part costs at most Q(r*). The total is Õ(d^a (σ/ε)^b).
4. **Case p > 4/3, d > 4^p(σ/ε)².** Then r_0 = σ. The inner part costs O(Sσ^{2−p}/ε²) = O((σ/ε)²) classically, and the shells sum to Õ(C(σ)) = Õ((σ/ε)²).
5. **Case p ≤ 4/3.** C is nondecreasing in r, so the shells cost at most Õ(C(τ)) = Õ((σ/ε)^b). Indeed, 2 + (2 − 3p/2)/(p − 1) = b. The inner part costs at most:
   - Q(r*) = Θ(d^a (σ/ε)^b) ≤ Θ((σ/ε)^b) when r_0 = r*, since a ≤ 0;
   - O((σ/ε)²) ≤ O((σ/ε)^b) when r_0 = σ.

Together this is the bound of Theorem 1. For a worst-case bound, cap the attempts of each conditional sampler at 2n_j + O(log(J/δ)). On the success event of amplitude estimation each attempt succeeds with probability at least 1/2, so by a multiplicative tail bound for sums of independent indicators the cap is reached with probability at most δ/(2J + 2). □

**Corollary 2.** In [1, Theorem 4.4], the estimator enters only through its guarantee ‖g_t − ∇f(x_t)‖ ≤ ε/32 with probability 1 − δ/T, over T = ⌈36LΔ_f ε^{−2}⌉ iterations. Replace its cost by that of Theorem 1 at accuracy ε/32. Then use max{1, min{d^a, (σ/ε)^{2−b}}} ≤ (σ/ε)^{max{0, 2−b}}. □

## Remarks

1. **Why the shells.** One truncation at τ leaves a variance of S τ^{2−p}, set by the rare large values. For those values, amplitude amplification gives conditional samples at cost 1/√π, and classical averaging has no dimension factor [4]. The bounded-variance estimator of [2] is better only for the frequent small values. The crossover r* balances the two. Dyadic levels with amplitude estimation per level are the core of the univariate estimators of [7] and [8]. The multivariate part here is the combination, in each shell, of amplitude estimation of the mass with exact conditional samples and a dimension-free geometric median, and the crossover to the estimator of [2] below r*.
2. **Dimension free regime.** For d ≥ (σ/ε)² and bounded variance (p = 2), the cost Θ((σ/ε)²) is the classical one, in line with the known absence of a quantum advantage when the sample size is below the dimension [2]. For p < 2 there is still a polynomial gain, (σ/ε)^{max{b, 2}} against (σ/ε)^{2b}, which is quadratic for p ≤ 4/3.
3. **Scope.** Theorem 1 is for the high-probability problem [1, Problem 3.1]. The unbiased estimator of [1, Section 3.2] and the convex method of [1, Theorem 5.3] are not treated here. Their multilevel construction sums the cost over geometrically finer accuracies. That sum needs a cost growing slower than ε^{−2p/(3(p−1))}. In high dimension this fails for p > 3/2, by a log factor at p = 3/2: the sum is then dominated by the accuracy level ε_j with (σ/ε_j)² ≈ d.

## Check

`sim/heavytail_check.py` checks the following:

1. **Exponent identities.** It checks them exactly in rational arithmetic, over a grid of p.
2. **Cost against the closed form.** For p ∈ {1.1, 1.25, 4/3, 1.5, 1.75, 2} and d from 1 to 10^12, it sums the per-part cost bounds of the Cost paragraph, with π_j at its first moment bound and all constants set to 1. Divided by the closed form of Theorem 1 and by J³, the result does not grow with σ/ε: its slope in log(σ/ε) over ε from 10^{−2} to 10^{−8} is below 0.05 at every fixed d.
3. **Correctness by emulation.** It runs the estimator on finite-valued heavy-tailed laws in d = 50, 1000 and 5000, with p ∈ {1.2, 1.5, 1.8}. Conditional samples are drawn exactly, and the inner estimate gets an error of ℓ₂ norm exactly ε/3. The amplitude estimates are drawn at the ends ±Δ_j of their error bars, on either side of the zero threshold. The error of the shells and the tail, without the injected ε/3, stays below 2ε/3 on every run. The sampled shells carry up to 1.45ε of the mean.

```
exponent identities hold exactly for p = 1 + k/40, k = 1..40
p = 1.100: slope of log(cost / (closed form * J^3)) in log(sigma/eps) <= +0.0000, ratio <= 4.66e+03, over d = 1 .. 1e12
p = 1.333: slope of log(cost / (closed form * J^3)) in log(sigma/eps) <= +0.0018, ratio <= 41.4, over d = 1 .. 1e12
p = 2.000: slope of log(cost / (closed form * J^3)) in log(sigma/eps) <= +0.0000, ratio <= 18.2, over d = 1 .. 1e12
d = 1000, p = 1.2, eps = 0.1 sigma: max error over 20 runs = 0.334 eps (shells and tail 0.009 eps), sampled shells >= 13, their mean contribution >= 1.43 eps
d = 5000, p = 1.8, eps = 0.1 sigma: max error over 20 runs = 0.334 eps (shells and tail 0.019 eps), sampled shells >= 4, their mean contribution >= 1.00 eps
heavy-tailed shell estimator checks pass
```

## References

1. B. Luo, C. Liu, J. Allcock, S. Zhang, J. C. S. Lui. Quantum Speedups for Stochastic Optimization with Heavy-Tailed Noise. arXiv:2607.25492.
2. A. Cornelissen, Y. Hamoudi, S. Jerbi. Near-optimal quantum algorithms for multivariate mean estimation. STOC 2022, arXiv:2111.09787.
3. J. Zhang, S. P. Karimireddy, A. Veit, S. Kim, S. J. Reddi, S. Kumar, S. Sra. Why are adaptive methods good for attention models? NeurIPS 2020, arXiv:1912.03194.
4. S. Minsker. Geometric median and robust estimation in Banach spaces. Bernoulli 21(4), 2308 (2015), arXiv:1308.1334.
5. G. Brassard, P. Høyer, M. Mosca, A. Tapp. Quantum amplitude amplification and estimation. Contemporary Mathematics 305, 53 (2002), arXiv:quant-ph/0005055.
6. T. J. Yoder, G. H. Low, I. L. Chuang. Fixed-point quantum search with an optimal number of queries. Physical Review Letters 113, 210501 (2014), arXiv:1409.3305.
7. Y. Hamoudi. Quantum sub-Gaussian mean estimator. ESA 2021, arXiv:2108.12172.
8. J. Blanchet, M. Szegedy, G. Wang. Quadratic speed-up in infinite variance quantum Monte Carlo. arXiv:2401.07497.
