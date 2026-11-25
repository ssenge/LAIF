# Quantum counting with Bernoulli oracles without the logarithmic factor

_25 November 2026_

We are given m Bernoulli distributions with unknown biases p_1, …, p_m. Each is positive (p_i ≥ 1/2 + Δ) or negative (p_i ≤ 1/2 − Δ). The task is to estimate the fraction ρ of positive distributions to within additive error ε. The quantum oracle acts as O|i⟩|0⟩ = |i⟩(√p_i |1⟩|φ_i1⟩ + √(1 − p_i) |0⟩|φ_i0⟩), and O and its inverse are available. In [1] this problem gets the upper bound Õ(√ρ/(Δε) + 1/(Δ√ε)) · log(1/δ) and the lower bound Ω(√ρ/(Δε)). It is asked there whether the logarithmic factor can be removed, which would give a tight bound [1, Sec. 5]. Classically, the sample complexity Θ(ρ/(ε²Δ²) · log(1/δ)) has no such factor [2].

## Result

**Theorem 1.** With success probability 2/3, the fraction ρ can be estimated to within ±ε using

  O( √ρ/(Δε) + 1/(Δ√ε) )

queries, and with success probability 1 − δ using a further factor log(1/δ). The query bound holds with probability 2/3 jointly with correctness. For ρ ≥ ε it matches the lower bound Ω(√ρ/(Δε)) of [1, Corollary 4.9]. For ρ < ε it is O(1/(Δ√ε)), the value of that lower bound at ρ = ε.

**Corollary 2 (bounded-error oracle).** For the bounded-error oracle, the case Δ = Θ(1) [1, Corollary 1.4], the bound is O(√ρ/ε + 1/√ε), tight for ρ ≥ ε.

The proof has four steps. The quantum part follows from the log-free composition of bounded-error algorithms in [3].

1. **Inner decision.** For a fixed i, amplitude estimation [4, Theorem 12] with M ≥ 2π/Δ applications of the Grover iterate, run coherently with the comparison p̃ ≥ 1/2, decides the sign of p_i − 1/2 with probability at least 8/π² > 4/5. It uses O(1/Δ) queries. Its error bound 2π√(p(1 − p))/M + π²/M² is below Δ.
2. **Outer decision.** For a threshold a and a gap e, amplitude estimation with M ≥ 8π√(a + e)/e decides whether the fraction of ones of an m-bit string is at most a or at least a + e. Every fraction at most a stays below a + e/2 after the error bound is added, and every fraction at least a + e stays above it. It uses O(√a/e + 1/√e) queries.
3. **Composition without error reduction.** By [3, Theorems 3.14 and 3.15], an algorithm that makes L queries and calls a bounded-error subroutine composes with it without error reduction, at a cost of O(L) calls to the subroutine. Here the subroutine has gap 4/5 against 1/5 and the input oracle is a general unitary. The threshold decision for the composed problem therefore takes O((√a/e + 1/√e)/Δ) queries. This decision version already matches the lower bound of [1].
4. **Estimation by geometric refinement.** At stage j = 1, …, J with e_j = 2^(−j) and J = ⌈log₂(1/ε)⌉, the fraction ρ lies in an interval of width 4e_j. Four threshold decisions at spacing e_j shrink it to width 2e_j: with k₁ the largest threshold answered yes, ρ lies in [l + k₁e_j, l + k₁e_j + 2e_j). Stage j repeats each decision O(J − j + 3) times, so its error probability is at most 2^(−(J−j+3)). The error probabilities sum to at most 1/4. If all earlier stages are correct, stage j costs O((J − j + 3)(√ρ · 2^j + 2^(j/2))/Δ). Since Σ_k (k + 3) q^k is finite for q = 1/2 and q = 1/√2, the sum over all stages is a constant times the cost of the last one.

## Scope

- **Claim.** Theorem 1 is a written proof.
- **Assuming.** The error bound of amplitude estimation [4, Theorem 12], the purifier and the log-free composition of [3, Theorems 3.14 and 3.15], and the lower bound of [1, Corollary 4.9].
- **Not formalized.** No part is in Lean.
- **Constants.** The constant of Theorem 1 is not explicit, since the composition of [3] gives its overhead only up to a constant.

## Checks

`sim/check.py` (`python -I check.py`) computes the exact output distribution of amplitude estimation and compares it with a direct simulation of phase estimation on the Grover iterate. It then checks the following:

- the worst-case success probability of the inner decision over Δ from 0.001 to 0.5 (at least 0.943) and of the outer decision on a grid of thresholds and gaps (at least 0.955), both above 8/π²;
- the refinement on 8000 runs with decisions that are random or adversarial inside the gap and wrong with probability δ_j outside it. The error is at most ε whenever no decision errs, and the ratio of the cost to √ρ/ε + 1/√ε converges as ε falls from 10⁻¹ to 10⁻⁵.

## Files

- `sim/check.py`: the checks above.

## Use of AI

The analysis, code and text were produced with Claude Opus 5.5.

## References

1. C. Gao, Y. Xu, L. Li. Quantum approximate counting with Bernoulli oracles. arXiv:2609.07604.
2. J. C. H. Lee, P. Valiant. Uncertainty about uncertainty: optimal adaptive algorithms for estimating mixtures of unknown coins. SODA 2021, arXiv:1904.09228.
3. A. Belovs, S. Jeffery, D. Yolcu. Taming quantum time complexity. Quantum 8, 1444 (2024), arXiv:2311.15873.
4. G. Brassard, P. Høyer, M. Mosca, A. Tapp. Quantum amplitude amplification and estimation. Contemporary Mathematics 305, 53 (2002).
