# Shot cost of noise cancellation in quantum neural network approximation

Written 6 Nov 2026.

## Setting

[1] gives error bounds for a QNN under hardware noise. The QNN is the one of [2].

**Circuit and output.** For m accuracy blocks the circuit has q = ⌈log₂(4m + m₀)⌉ qubits; write D = 2^q. The ideal state is ρ = ρ(θ, x). A computational-basis readout {Π_o} gives outcome probabilities P_o = tr(Π_o ρ), and the output is

f_θ(x) = R(1 − 2(P_1 + P_2)) = tr(Oρ),  O = R(I − 2(Π_1 + Π_2)),

so O has eigenvalues ±R. If f has L¹[f̂] = B ≤ R, some θ gives ‖f − f_θ‖_{L²(μ)} ≤ B/√m [2, Theorem II.4].

**Noise model.** Depolarising noise after each of the two stages gives [1, Proposition 3.9]

ρ̃ = αρ + (1 − α) I/D.

In the hardware model of [1, Section 3.6], the two stages have q − 2 one-qubit gates and N_2Q = mq/15 two-qubit gates. With gate errors ε_1Q and ε_2Q,

α = (1 − ε_1Q)^{q−2} (1 − ε_2Q)^{mq/15},

and decoherence over the circuit time adds factors 1 − p_T/2 ≤ 1.

**Affine correction.** The noisy output is f̃ = αf_θ + (1 − α)c₀, where c₀ = tr(O)/D. [1, Theorem 3.15] shows that the affine map (f̃ − (1 − α)c₀)/α returns f_θ exactly. That holds in expectation. With finitely many shots, the 1/α in this map also scales up the statistical error.

## Results

Each shot measures the noisy state with the readout and records Y = R(1 − 2·1[o ∈ {1, 2}]). Let Ȳ be the mean of N shots, and

f̂ = (Ȳ − (1 − α)c₀)/α.

**Theorem 1 (shots at one input).** Fix θ and x.

1. **Upper bound.** E f̂ = f_θ(x) and E|f̂ − f_θ(x)|² ≤ R²/(α²N). Also, P(|f̂ − f_θ(x)| ≥ ε) ≤ 2 exp(−Nα²ε²/(2R²)).
2. **Lower bound, same readout.** Suppose the family contains two settings with the following ideal readout distributions:
   - P⁻, and P⁺ = P⁻ + (ε/R)(e_a − e_b), with a ∈ {0, 3} and b ∈ {1, 2};
   - P⁻_a, P⁻_b ≥ 1/8;
   - tr Π_a/D, tr Π_b/D ≥ 1/8, which holds when m₀ = 0.

   Their outputs differ by 2ε. Suppose a method uses N shots of the readout and, for both settings, comes within less than ε of the output with probability at least 2/3. Then it needs
   N ≥ R²/(72 α² ε²),
   whatever its post-processing.
3. **Lower bound, any measurement.** Let ρ^± be two ideal states with |tr(Oρ⁺) − tr(Oρ⁻)| ≥ 2ε, and let F = F(ρ⁺, ρ⁻) be the root fidelity. Consider any measurement on N copies of the noisy state, including joint ones, as in virtual distillation. If it comes within less than ε for both states with probability at least 2/3, then
   N ≥ ln(9/8)/(2α(1 − F)) · (1 − α(1 − F)).
   For pure states cos φ|a⟩ + sin φ|b⟩, with |a⟩ and |b⟩ in the +R and −R eigenspaces of O and φ = π/4 ∓ η, this gives N ≥ R²/(23 α ε²) for ε ≤ R/2.

So the correction costs Θ(R²/(α²ε²)) shots with the readout of [1]. When the family contains the pure pair of part 3, no measurement strategy goes below order R²/(αε²). Since α decays exponentially in the gate count, both costs are exponential in mq.

**Theorem 2 (budget of the noisy approximation).** Take f with L¹[f̂] = B ≤ R. Run the circuit of [2] with m blocks and N shots per input, and apply the correction.

1. **Error.** (E ∫ |f − f̂|² dμ)^{1/2} ≤ B/√m + R/(α(m)√N).
2. **Accuracy ε.** Choose m = ⌈4B²/ε²⌉ and N = ⌈4R²/(α(m)²ε²)⌉. Then the error is at most ε. Per input this needs
   N ≤ (4R²/ε²) · e^{2c·mq} + 1 = (4R²/ε²) · exp(O(c B² log(B/ε)/ε²)) for m₀ = O(m),
   where c = −ln(1 − ε_1Q) − ln(1 − ε_2Q)/15 with gate errors only. Decoherence over the circuit time adds t_2Q(1/T_1 + 1/T_2)/30 to c.
3. **Shots needed at these m blocks.** Since α ≤ (1 − ε_2Q)^{mq/15}, the conditions of Theorem 1 give the following lower bounds:
   - with the readout: N ≥ (R²/(72ε²)) (1 − ε_2Q)^{−2mq/15};
   - with any measurement: N ≥ (R²/(23ε²)) (1 − ε_2Q)^{−mq/15}.

   At m = ⌈4B²/ε²⌉ both are exp(Ω(ε_2Q B² log(B/ε)/ε²)).
4. **Fixed budget.** With N shots per input, take the largest m with c·m·q(m) ≤ (ln N)/4. Then the error is
   O(B √(c log(ln N/c)/ln N) + R N^{−1/4})
   for m₀ = O(m) and N large enough that m ≥ 1. So the accuracy guaranteed by this route improves only logarithmically in the number of shots. The number of usable blocks is m = O(ln N/(c log(ln N/c))).

## Numbers

Take the calibration values of [1, Appendix A] and B = R = 1. In the ibm_fez rows the lower end of α includes decoherence; the upper end uses two-qubit gate errors only.

| device | ε | m | q | N_2Q | α | shots that suffice | shots needed at this m |
|---|---|---|---|---|---|---|---|
| ibm_fez | 0.1 | 400 | 11 | 293 | 0.40 to 0.47 | 2.5·10³ | 6 |
| ibm_fez | 0.05 | 1600 | 13 | 1387 | 0.013 to 0.029 | 9.4·10⁶ | 6.6·10³ |
| ibm_fez | 0.02 | 10⁴ | 16 | 10667 | 3·10⁻¹⁵ to 2·10⁻¹² | 9·10³² | 1.5·10²⁵ |
| H2, gate errors | 0.05 | 1600 | 13 | 1387 | 0.25 | 2.6·10⁴ | 89 |
| H2, gate errors | 0.02 | 10⁴ | 16 | 10667 | 2.3·10⁻⁵ | 1.9·10¹³ | 6.5·10¹⁰ |

Take the 8192 shots per circuit used in [1]. When the family satisfies the conditions of Theorem 1, part 2, the readout cannot reach ε = 0.05 pointwise on ibm_fez beyond m = 1649 blocks. There the approximation term B/√m is about 0.025.

## Proofs

*Theorem 1, part 1.* The shots are independent, with Y ∈ {−R, R} and E Y = tr(Oρ̃) = αf_θ + (1 − α)c₀. So E f̂ = f_θ, and Var f̂ = Var(Y)/(α²N) ≤ R²/(α²N). Hoeffding's inequality for Ȳ at deviation αε gives the tail bound. □

*Theorem 1, part 2.* The noisy readout law is P̃ = αP + (1 − α)u, with u_o = tr Π_o/D.

- **The two laws differ little.** P̃⁺ − P̃⁻ = (αε/R)(e_a − e_b). On a and b, P̃⁻ ≥ min(P⁻, u) ≥ 1/8. Hence χ²(P̃⁺ ‖ P̃⁻) ≤ 16 α²ε²/R².
- **The outputs differ by 2ε.** f⁺ − f⁻ = −2R(P⁺_1 + P⁺_2 − P⁻_1 − P⁻_2) = 2ε.
- **So the method yields a test.** Reporting the setting whose output is nearer to the estimate is correct with probability at least 2/3 under each setting. So the total variation distance between the N-shot laws is at least 1/3.
- **The shot count follows.** That distance is at most √(N·KL/2) ≤ √(N·χ²/2) by Pinsker's inequality and KL ≤ χ². So N ≥ 2/(9χ²) ≥ R²/(72α²ε²). □

*Theorem 1, part 3.* Root fidelity is jointly concave [5, Theorem 9.7]. Apply it to the mixtures with weights α and 1 − α:

F̃ := F(αρ⁺ + (1 − α)I/D, αρ⁻ + (1 − α)I/D) ≥ αF + (1 − α).

As in part 2, the method yields a test between ρ̃⁺^{⊗N} and ρ̃⁻^{⊗N} that succeeds with probability at least 2/3. Root fidelity is multiplicative on tensor powers. So the trace distance bound of [6] gives

1/3 ≤ √(1 − F̃^{2N}).

Hence 2N ln(1/F̃) ≥ ln(9/8). With ln(1/F̃) ≤ (1 − F̃)/F̃ and 1 − F̃ ≤ α(1 − F), the bound follows.

For the pure pair, tr(Oρ^±) = ±R sin 2η and F = cos 2η. So sin 2η = ε/R, and 1 − F ≤ ε²/R². For ε ≤ R/2, 1 − α(1 − F) ≥ 3/4, and ln(9/8)·(3/4)/2 > 1/23. □

*Theorem 2.*

- **Part 1.** By Minkowski's inequality in L²(μ ⊗ shots), the error is at most ‖f − f_θ‖_{L²(μ)} + sup_x (E|f̂(x) − f_θ(x)|²)^{1/2}. The two terms are bounded by [2, Theorem II.4] and Theorem 1, part 1.
- **Part 2.** Each term is then at most ε/2. With −ln(1 − p_T/2) ≤ t_circ/(2T) and t_circ = N_2Q t_2Q, we get −ln α ≤ c·mq, using q − 2 ≤ mq. Finally, mq = O((B²/ε²) log(B/ε)).
- **Part 3.** This is Theorem 1, parts 2 and 3, with α ≤ (1 − ε_2Q)^{mq/15}. Here −ln(1 − ε_2Q) ≥ ε_2Q and q ≥ log₂(16B²/ε²).
- **Part 4.** Since α ≥ e^{−c mq} ≥ N^{−1/4}, the shot term is at most R N^{−1/4}. By maximality, c(m + 1)q(m + 1) > (ln N)/4, so m ≥ (ln N)/(8c·q(m + 1)) for m ≥ 1. Also q(m + 1) = O(log(ln N/c)), and so B/√m = O(B √(c log(ln N/c)/ln N)). □

## Remarks

1. **Relation to error mitigation bounds.** [3] and [4] prove that the sample cost of error mitigation grows exponentially with depth under local depolarising noise, for broad classes of mitigation methods. Theorem 1 is the global depolarising case in the model of [1], with explicit constants for the readout of [1] and for joint measurements. The new content is Theorem 2, which combines these costs with the approximation rate of [2].
2. **Scope.** Both lower bounds are worst case over two settings at one input. Theorem 2, parts 2 and 4, are upper bounds obtained by this route. Parts 1 to 3 keep the gate-count model of [1, Section 3.6]. Under that model α decays like e^{−Θ(ε_2Q m log m)}, so the shot cost is driven by the number of blocks m, not the qubit count.
3. **Between the two lower bounds.** The readout bound scales as 1/α², the bound for joint measurements as 1/α. A matching upper bound of order 1/α for joint measurements is not treated here.

## Check

`sim/shot_check.py` checks the following:

- the corrected estimator is unbiased, with mean square error at most R²/(α²N), on 30 random cases;
- the exact total variation of the two shot records at N = R²/(72α²ε²) is below 1/3;
- the fidelity inequality holds on 200 random mixed pairs;
- the pure pair of part 3 has F̃^{2N} ≥ 8/9 at N = R²/(23αε²);
- the budget table above.

```
corrected estimator: unbiased, E|f^ - f|^2 <= R^2/(a^2 N) on 30 cases (largest ratio 1.015)
a = 0.5, eps = 0.1: at N = 5, TV of the two shot records = 0.1217 < 1/3
fidelity lemma on 200 random pairs: min slack = 3.12e-04 >= 0
a = 0.9, eps = 0.01: at N = 483, F~^(2N) = 0.9597 >= 8/9
ibm_fez, eps = 0.05: m = 1600, q = 13, N2Q = 1387, alpha in [0.0131, 0.0291], shots per point: suffice 9.38e+06, needed at this m >= 6.57e+03
ibm_fez, N = 8192, eps = 0.05: the fixed readout cannot reach eps pointwise beyond m = 1649 blocks (B/sqrt(m) = 0.025)
shot cost checks pass
```

## References

1. L. Gonon, A. Jacquier, M. Mordarski. Quantitative universal approximation for noisy quantum neural networks. arXiv:2604.02064.
2. L. Gonon, A. Jacquier. Universal approximation theorem and error bounds for quantum neural networks and quantum reservoirs. IEEE Transactions on Neural Networks and Learning Systems (2025), arXiv:2307.12904.
3. R. Takagi, S. Endo, S. Minagawa, M. Gu. Fundamental limits of quantum error mitigation. npj Quantum Information 8, 114 (2022), arXiv:2109.04457.
4. Y. Quek, D. Stilck França, S. Khatri, J. J. Meyer, J. Eisert. Exponentially tighter bounds on limitations of quantum error mitigation. Nature Physics 20, 1648 (2024), arXiv:2210.11505.
5. M. A. Nielsen, I. L. Chuang. Quantum Computation and Quantum Information. Cambridge University Press (2010).
6. C. A. Fuchs, J. van de Graaf. Cryptographic distinguishability measures for quantum-mechanical states. IEEE Transactions on Information Theory 45, 1216 (1999).
