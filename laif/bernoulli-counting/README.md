# Quantum counting with coin oracles without the logarithmic factor

_25 November 2026_

We are given m coins with unknown biases p_1, …, p_m. Each coin is positive (p_i ≥ 1/2 + Δ) or negative (p_i ≤ 1/2 − Δ). The task is to estimate the fraction ρ of positive coins to within additive error ε. The quantum oracle (called a Bernoulli oracle in [1]) acts as O|i⟩|0⟩ = |i⟩(√p_i |1⟩|φ_i1⟩ + √(1 − p_i) |0⟩|φ_i0⟩), and O and its inverse are available. In [1] this problem gets the upper bound Õ(√ρ/(Δε) + 1/(Δ√ε)) · log(1/δ) and the lower bound Ω(√ρ/(Δε)). It is asked there whether the logarithmic factor can be removed, which would give a tight bound [1, Sec. 5]. Classically, the sample complexity Θ(ρ/(ε²Δ²) · log(1/δ)) has no such factor [2].

## Results

Write ρ* = min(ρ, 1 − ρ).

**Theorem 1 (upper bound).** With success probability 2/3, the fraction ρ can be estimated to within ±ε using

  O( √ρ*/(Δε) + 1/(Δ√ε) )

queries. The query bound holds with probability 2/3 jointly with correctness. With success probability 1 − δ, the same holds with a further factor log(1/δ). For ρ* ≥ ε the second term is dominated, and the bound reads O(√ρ*/(Δε)).

**Theorem 2 (matching lower bound).** For every ρ, every algorithm that estimates the fraction to within ±ε with probability 2/3 on all inputs makes Ω(√ρ*/(Δε) + 1/(Δ√ε)) queries on some input whose fraction lies within 3ε of ρ. So the bound of Theorem 1 is tight for every ρ.

The proof of Theorem 2 uses the composed adversary bound of [1, Theorem 4.8] for deciding between the fractions ρ' and ρ' + ε'. The adversary matrix of [1, Lemma 4.7] gives the value √((1 − ρ')(ρ' + ε'))/ε' for the outer decision before simplification. An estimator within ±ε separates fractions 3ε apart. For ρ ≤ 1/2 the pair ρ' = ρ, ε' = 3ε gives √((1 − ρ)(ρ + 3ε))/(3ε) ≥ (√ρ + √(3ε))/(6ε), which is both terms. For ρ > 1/2 the pair ρ' = ρ − 3ε, ε' = 3ε gives the same with 1 − ρ in place of ρ. The value √((1 − ρ)(ρ + ε))/ε is written as Ω(√ρ/ε) in [1, Lemma 4.7, Corollary 4.9]. That simplification holds for ρ bounded away from 1.

**Corollary 3 (bounded-error oracle).** For the bounded-error oracle, the case Δ = Θ(1) [1, Corollary 1.4], the complexity is Θ(√ρ*/ε + 1/√ε).

## Proof of Theorem 1

The quantum part follows from the log-free composition of bounded-error algorithms in [3].

1. **Inner decision.** For a fixed i, amplitude estimation [4, Theorem 12] uses M ≥ 2π/Δ applications of the amplitude amplification iterate, run coherently together with the comparison p̃ ≥ 1/2. It decides the sign of p_i − 1/2 with probability at least 8/π² > 4/5, using O(1/Δ) queries. Its error bound 2π√(p(1 − p))/M + π²/M² is below Δ.
2. **Outer decision.** For a threshold a and a gap e, amplitude estimation with M ≥ 8π√(a + e)/e decides whether the fraction of ones of an m-bit string is at most a or at least a + e. Every fraction at most a stays below a + e/2 after the error bound is added, and every fraction at least a + e stays above it. It uses O(√a/e + 1/√e) queries.
3. **Composition without error reduction.** By [3, Theorem 13.4], an algorithm with worst-case Las Vegas query complexity L that evaluates f composes with a bounded-error algorithm B for g. The composition evaluates f ∘ g with bounded error using O(L · Q(B)) queries. Its proof passes the inner algorithm and its inverse to the purifier of [3, Theorems 3.14 and 13.1], which holds for every state-generating oracle with a constant gap. Theorem 13.4 is stated for inner functions of bit strings. Its proof applies unchanged to the unitary oracles O_i, since it accesses them only through B and B⁻¹, and the inverse O_i† is available. Here L is at most the number of queries of step 2, and the gap of step 1 is 4/5 against 1/5. The threshold decision for the coins therefore takes O((√a/e + 1/√e)/Δ) queries with constant error.
4. **Orientation.** Flipping the output qubit of O exchanges positive and negative coins and turns ρ into 1 − ρ. One decision with a = 1/2, e = 1/4 costs O(1/Δ). If it answers no, then ρ < 3/4 and ρ ≤ 3ρ*, and the algorithm continues with O. Otherwise ρ > 1/2, it continues with the flipped oracle, and it outputs one minus the estimate.
5. **Estimation by geometric refinement.** Let e_j = 2^(−j) and J = ⌈log₂(1/ε)⌉. At stage j = 1, …, J the fraction lies in an interval [l, l + 4e_j), starting from [0, 2). Four threshold decisions at the points l + k·e_j, k = 0, …, 3, shrink it to width 2e_j. With k₁ the largest point answered yes, the fraction lies in [l + k₁e_j, l + k₁e_j + 2e_j), and in [l, l + 2e_j) if there is none. The output is the midpoint of the last interval.
   - Stage j repeats each decision O(J − j + 3 + log(1/δ)) times, which gives error probability δ · 2^(−(J−j+3)). These probabilities sum to at most δ/4.
   - If all earlier stages are correct, every point of stage j is at most ρ + 3e_j. Stage j then costs O((J − j + 3 + log(1/δ))(√ρ · 2^j + 2^(j/2))/Δ).
   - Since Σ_k (k + 3 + D) q^k ≤ q/(1 − q)² + (3 + D)/(1 − q) for q = 1/2 and q = 1/√2, the sum over all stages is O(log(1/δ)) times the cost of the last one. Success probability 2/3 is the case δ = 1, with the decision of step 4 included in the error budget.

## Scope

- **Claim.** Theorems 1 and 2 are written proofs.
- **Assuming.** The error bound of amplitude estimation [4, Theorem 12]. The purifier and the log-free composition of [3, Theorems 13.1 and 13.4], used for unitary inner oracles as explained in step 3. The composed adversary lower bound of [1, Theorem 4.8], proved there for sample access, and its transfer to the quantum oracle stated in [1, Sec. 4.1].
- **Not formalized.** No part is in Lean.
- **Constants.** The constant of Theorem 1 is not explicit, since the composition of [3] gives its overhead only up to a constant.

## Checks

`sim/check.py` (`python -I check.py`) computes the exact output distribution of amplitude estimation and compares it with a direct simulation of phase estimation on the amplitude amplification iterate. It then checks the following:

- the worst-case success probability of the inner decision over Δ from 0.001 to 0.5 (at least 0.943) and of the outer decision on a grid of thresholds and gaps (at least 0.955), both above 8/π²;
- the refinement on 8000 runs with decisions that are random or adversarial inside the gap and wrong with probability δ_j outside it. The error is at most ε whenever no decision errs, and the ratio of the cost to √ρ/ε + 1/√ε levels off as ε falls from 10⁻¹ to 10⁻⁵.

## Files

- `sim/check.py`: the checks above.

## Use of AI

The analysis, code and text were produced with Claude Opus 5.5.

## References

1. C. Gao, Y. Xu, L. Li. Quantum approximate counting with Bernoulli oracles. arXiv:2609.07604.
2. J. C. H. Lee, P. Valiant. Uncertainty about uncertainty: optimal adaptive algorithms for estimating mixtures of unknown coins. SODA 2021, arXiv:1904.09228.
3. A. Belovs, S. Jeffery, D. Yolcu. Taming quantum time complexity. Quantum 8, 1444 (2024), arXiv:2311.15873.
4. G. Brassard, P. Høyer, M. Mosca, A. Tapp. Quantum amplitude amplification and estimation. Contemporary Mathematics 305, 53 (2002).
