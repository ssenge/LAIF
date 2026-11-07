# Generalization of hybrid quantum-classical models with a scalar quantum output

Written 5 Nov 2026.

## Setting

A hybrid model computes h(x) = F(q_θ(x)). The quantum part q_θ(x) = tr(O ℰ_θ(ρ(x))) is one expectation, of an observable with ‖O‖ ≤ β, after a circuit with T ≥ 1 trainable two-qubit gates (unitary or CPTP), each used at most M times, on any fixed encoding ρ(x). Fixed data re-uploading gates between the trainable gates are allowed. The classical head F: [−β, β] → R is taken from a class 𝓗 of functions with |F(a) − F(b)| ≤ Λ|a − b| (slope at most Λ) and |F| ≤ B.

For a k-layer network with activations of slope at most L_σ and layers of entrywise 2-norm at most α, the head has slope at most L_σ^{k−1} α^k, since the operator norm is at most the entrywise 2-norm and there are k − 1 activations. Any hidden widths are allowed.

[1] treats heads that read n expectations, with layers of shape m × n, and states a generalization gap of Õ((α^k/√N)(k^{3/2}√(mn) + √(T log T))). For one expectation, its covering argument gives a classical term that grows with the hidden widths. The results below are for one expectation and contain no width.

## Results

**Theorem 1 (upper bound).** For N inputs, the empirical random-sign complexity of 𝓖 = {F ∘ q_θ : F ∈ 𝓗, θ} is at most

(C/√N) (B + √(ΛβB) + B √(T log(e + MT))),

with an absolute constant C. So for a loss of slope at most ρ in h and bounded by c₀, with probability 1 − δ every model in 𝓖 has generalization gap at most 2ρ times this plus 3c₀√(log(2/δ)/(2N)) [5].

For heads with F(0) = 0, for example networks without biases and with σ(0) = 0, one can take B = Λβ. The gap is then O(ρΛβ√(T log(e + MT))/√N + c₀√(log(2/δ)/N)), with no dependence on the width or the depth of the head beyond its slope bound Λ.

**Theorem 2 (tightness).** Take the loss (1 − y h/B)/2 ∈ [0, 1] and assume Λβ ≥ B. Each term of Theorem 1 is needed:

- *Head term.* If 𝓗 contains all functions of slope at most Λ with |F| ≤ B, then for a suitable encoding and T = 0 there is a data distribution for which every empirical risk minimizer has expected gap at least (1/4)√(m/N) ≥ (1/4)√(max(1, Λβ/B)/N), for N ≥ m = ⌊Λβ/B⌋ + 1.
- *Quantum term.* If 𝓗 contains the head F(q) = Bq/β, there is a family of circuits and a data distribution for which every empirical risk minimizer has expected gap at least c√(T log((M + 1)T)/N), for T ≥ 200 and N ≥ m, with m as in Theorem 1 of [2] and an absolute c > 0.

In both constructions the empirical risk attains its infimum, by compactness, as Theorem 2 of [2] requires. So for this loss and the class of all heads of slope at most Λ, the worst-case gap is Θ((1 + √(Λβ/B) + √(T log((M + 1)T)))/√N) for T ≥ 200.

## Proof of Theorem 1

For F, F′ with F ∈ 𝓗 and parameters θ, θ′, and every x,

|F(q_θ(x)) − F′(q_θ′(x))| ≤ Λ |q_θ(x) − q_θ′(x)| + ‖F − F′‖_∞.

The slope bound is used for F, not for F′, so F′ may be any function. Hence a sup-norm cover of 𝓗 at scale δ/2 and a cover of the quantum outputs, uniform in x, at scale δ/(2Λ) together give a cover of 𝓖 at scale δ.

- *Heads.* Functions of slope at most Λ on an interval of length 2β with values in [−B, B] have log N(𝓗, η) ≤ c(Λβ/η + log(2 + B/η)) for η ≤ B [3]. For a grid of spacing η/Λ, a function is fixed up to η by its rounded value at the first grid point and by one of three rounded increments at each later point.
- *Circuits.* The nets of Appendix C of [4] consist of circuits of the same form, at scale η/(2βMT) per gate in operator norm for unitaries, or η/(βMT) in diamond norm for channels. They give log N(Q, η) ≤ cT log(e + βMT/η), uniformly in x, for the set Q of maps x ↦ q_θ(x).

So log N(𝓖, δ) ≤ c(2Λβ/δ + log(2 + 2B/δ) + T log(e + 2ΛβMT/δ)). Every function in 𝓖 lies in [−B, B], so the entropy integral bound for random-sign complexities gives

R̂_N(𝓖) ≤ (K/√N) ∫₀^B √(log N(𝓖, δ)) dδ

with an absolute constant K [6]. The first two parts integrate to at most 2√(2cΛβB) + c′B. For the third, ∫₀¹ √(log(e + A/u)) du ≤ √(log(e + A)) + 1 for A ≥ 0 gives at most c″B√(T log(e + ΛβMT/B)). Finally, with x = Λβ/B,

log(e + xMT) ≤ log(e + MT) + log(1 + T) + log(1 + x/T), and T log(1 + x/T) ≤ x,

so B√(T log(e + ΛβMT/B)) ≤ B√(T log(e + MT)) + B√(T log(1 + T)) + √(ΛβB). As log(1 + T) ≤ log(e + MT), the last expression is at most 2B√(T log(e + MT)) + √(ΛβB). ∎

## Proof of Theorem 2

Both parts use Theorem 2 of [2]. It says: if a class with values in [−1, 1] shatters m inputs at margin γ, then for labels that are fair coins independent of a uniform input on those m points, every empirical risk minimizer for the loss (1 − y f)/2 has expected gap at least (γ/4)√(m/N) for N ≥ m. It is applied here to h/B.

*Head term.* Let m = ⌊Λβ/B⌋ + 1 and t_j = −β + 2jB/Λ for j = 0, …, m − 1, which lie in [−β, β]. Encode x_j in one qubit so that tr(Oρ(x_j)) = t_j with O = βZ, and use no trainable gate. For a sign pattern p, the piecewise linear F_p with F_p(t_j) = p_j B has slopes at most 2B/(2B/Λ) = Λ and |F_p| ≤ B. So h/B shatters the m inputs at margin 1, and the expected gap is at least (1/4)√(m/N).

*Quantum term.* Take the circuits of Theorem 1 of [2] with observable O = βX, so q_θ(s) = β cos⟨s, θ⟩, and the head F(q) = Bq/β. Its slope is at most Λ since Λβ ≥ B, and h/B = cos⟨s, θ⟩. These shatter m ≥ T log₂((M + 1)T)/(8 log₂6) − 1 inputs at margin 1/2, so the expected gap is at least (1/8)√(m/N).

For the joint statement, the class of all heads of slope at most Λ contains F(q) = Bq/β, and the circuits of [2] with no trainable gate applied give the encoding of the head term. ∎

## Scope

- The heads see one expectation q_θ(x). If they read p > 1 expectations, heads of slope at most Λ on [−β, β]^p have log N of order (Λβ/η)^p, and for p ≥ 3 the worst-case rate over all such heads is of order N^{−1/p}. That case needs other assumptions on the head, such as norm bounds.
- The lower bounds are for worst-case data. The head term is shown for the class of all heads of slope at most Λ, not for networks of bounded width; the quantum term already for one linear head.
- The method combines a cover of one-dimensional functions of bounded slope with the circuit cover of [4], as for a bounded-slope link on a parametric scalar feature, and uses [2] for the lower bounds.

## References

1. T. Wu, A. Bentellis, A. Sakhnenko, J. M. Lorenz. Generalization Bounds in Hybrid Quantum-Classical Machine Learning Models. arXiv:2504.08456.
2. [qnn-generalization-lower-bounds](../qnn-generalization-lower-bounds/), Theorems 1 and 2.
3. A. N. Kolmogorov, V. M. Tikhomirov. ε-entropy and ε-capacity of sets in function spaces. Uspekhi Matematicheskikh Nauk 14 (1959), 3-86.
4. M. C. Caro, H.-Y. Huang, M. Cerezo, K. Sharma, A. Sornborger, L. Cincio, P. J. Coles. Generalization in quantum machine learning from few training data. Nature Communications 13, 4919 (2022). arXiv:2111.05292, Appendix C.
5. M. Mohri, A. Rostamizadeh, A. Talwalkar. Foundations of Machine Learning, 2nd edition. MIT Press, 2018, Theorem 3.3 and Lemma 5.7.
6. M. J. Wainwright. High-Dimensional Statistics. Cambridge University Press, 2019, Chapter 5.
