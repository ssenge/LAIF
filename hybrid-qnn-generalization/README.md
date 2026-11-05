# Generalization of hybrid quantum-classical models without width factors

Written 5 Nov 2026.

## Setting

A hybrid model, as in [1], computes h(x) = F(q_θ(x)). The quantum part q_θ(x) = tr(O ℰ_θ(ρ(x))) is the expectation of an observable with ‖O‖ ≤ β after a circuit with T trainable two-qubit gates, each used at most M times, on any fixed encoding ρ(x). The classical head F: [−β, β] → R is taken from a class 𝓗 of functions that are Λ-Lipschitz with |F| ≤ B.

For k-layer networks with L_σ-Lipschitz activations and layers of Frobenius norm at most α, as in [1], every head is (L_σ α)^k-Lipschitz, since the operator norm is at most the Frobenius norm. For such networks [1] proves a generalization gap of

Õ((α^k/√N)(k^{3/2}√(mn) + √(T log T))),

where m × n is the shape of the layers.

## Results

**Theorem 1 (upper bound).** For N inputs, the empirical Rademacher complexity of 𝓖 = {F ∘ q_θ : F ∈ 𝓗, θ} is at most

(C/√N) (√(ΛβB) + B √(T log(e + ΛβMT/B))),

with an absolute constant C. So for a loss that is ρ-Lipschitz in h and bounded by c₀, with probability 1 − δ every model in 𝓖 has generalization gap at most 2ρ times this plus 3c₀√(log(2/δ)/(2N)).

For heads with F(0) = 0, such as networks without biases, one can take B = Λβ, and the gap is O(ρΛβ(1 + √(T log(e + MT)))/√N + c₀√(log(1/δ)/N)). The width and the depth of the head enter only through its Lipschitz constant Λ, and Λ enters the quantum term only inside the logarithm.

**Theorem 2 (tightness).** Take the loss (1 − y h/B)/2 ∈ [0, 1] and assume Λβ ≥ B and β ≥ 1. Both terms of Theorem 1 are needed:

- *Head term.* If 𝓗 contains all Λ-Lipschitz functions with |F| ≤ B, there is a data distribution for which every empirical risk minimizer has expected gap at least (1/4)√(Λβ/(BN)) for N ≥ Λβ/B + 1.
- *Quantum term.* If 𝓗 contains the single head F(q) = Bq/β, there is a family of circuits and a data distribution for which every empirical risk minimizer has expected gap at least c√(T log((M + 1)T)/N) for T ≥ 200 and N ≥ m, with m as in Theorem 1 of [2] and an absolute c > 0.

So for this loss, the worst-case gap is Θ((√(Λβ/B) + √(T log((M + 1)T)))/√N), up to replacing log((M + 1)T) by log(e + ΛβMT/B).

## Proof of Theorem 1

For F, F′ ∈ 𝓗 and parameters θ, θ′, and every x,

|F(q_θ(x)) − F′(q_θ′(x))| ≤ ‖F − F′‖_∞ + Λ |q_θ(x) − q_θ′(x)|.

So a sup-norm cover of 𝓗 at scale δ/2 and a cover of the quantum outputs, uniform in x, at scale δ/(2Λ) together give a cover of 𝓖 at scale δ. Write N(·, η) for these covering numbers.

- *Heads.* Λ-Lipschitz functions on an interval of length 2β with values in [−B, B] have log N(𝓗, η) ≤ c(Λβ/η + log(2 + B/η)) for η ≤ B [3].
- *Circuits.* The covering argument of [4] nets each gate at scale η/(2βMT), and gives log N(Q, η) ≤ cT log(e + βMT/η) for the outputs q_θ, uniformly in x. Here Q is the set of maps x ↦ q_θ(x).

So log N(𝓖, δ) ≤ c(2Λβ/δ + log(2 + 2B/δ) + T log(e + 2ΛβMT/δ)). Every function in 𝓖 lies in [−B, B], and the Rademacher process is sub-Gaussian, so the entropy integral bound (Corollary 2.2.8 of [3]) gives

R̂_N(𝓖) ≤ (K/√N) ∫₀^B √(log N(𝓖, δ)) dδ

with an absolute constant K.

The three parts integrate to at most 2√(2cΛβB), c′B and c″B√(T log(e + ΛβMT/B)), using ∫₀¹ √(log(e + A/u)) du ≤ √(log(e + A)) + 1 for A ≥ 0. The generalization bound follows by the contraction and concentration steps in [5]. ∎

## Proof of Theorem 2

Both parts use Theorem 2 of [2]. It says: if a class with values in [−1, 1] shatters m inputs at margin γ, then for labels that are fair coins independent of a uniform input on those m points, every empirical risk minimizer for the loss (1 − y f)/2 has expected gap at least (γ/4)√(m/N) for N ≥ m. It is applied here to h/B.

*Head term.* Let m = ⌊Λβ/B⌋ + 1 and t_j = −β + 2jB/Λ for j = 0, …, m − 1, which lie in [−β, β]. Encode x_j in one qubit so that tr(Oρ(x_j)) = t_j with O = βZ, and use no trainable gate. For a sign pattern p, the piecewise linear F_p with F_p(t_j) = p_j B has slopes at most 2B/(2B/Λ) = Λ and |F_p| ≤ B. So h/B shatters the m inputs at margin 1, and the expected gap is at least (1/4)√(m/N) ≥ (1/4)√(Λβ/(BN)).

*Quantum term.* Take the circuits of Theorem 1 of [2] with observable O = βX, so q_θ(s) = β cos⟨s, θ⟩, and the head F(q) = Bq/β. It is Λ-Lipschitz since Λβ ≥ B, and h/B = cos⟨s, θ⟩. These shatter m ≥ T log₂((M + 1)T)/(8 log₂6) − 1 inputs at margin 1/2, so the expected gap is at least (1/8)√(m/N). ∎

## Scope

- The heads see the single expectation q_θ(x), as in [1]. If the head reads p > 1 expectations, then Lipschitz heads on [−β, β]^p have log N of order (Λβ/η)^p, and the entropy integral gives the rate 1/√N only up to a logarithm for p = 2, and not at all for p ≥ 3. Norm-based bounds for the head are then the better tool.
- The lower bounds are for worst-case data. The head term is shown for the class of all Λ-Lipschitz heads, and the quantum term already for one linear head.

## References

1. T. Wu, A. Sakhnenko. Generalization Bounds in Hybrid Quantum-Classical Machine Learning Models. arXiv:2504.08456.
2. [qnn-generalization-lower-bounds](../qnn-generalization-lower-bounds/), Theorems 1 and 2.
3. A. W. van der Vaart, J. A. Wellner. Weak Convergence and Empirical Processes. Springer, 1996, Theorem 2.7.1.
4. M. C. Caro, H.-Y. Huang, M. Cerezo, K. Sharma, A. Sornborger, L. Cincio, P. J. Coles. Generalization in quantum machine learning from few training data. Nature Communications 13, 4919 (2022). arXiv:2111.05292, Appendix C.
5. P. L. Bartlett, S. Mendelson. Rademacher and Gaussian complexities: risk bounds and structural results. Journal of Machine Learning Research 3 (2002), 463-482.
