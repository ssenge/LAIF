# Shot cost of noise cancellation in quantum neural network approximation

Written 6 Nov 2026.

## Setting

[1] gives error bounds for a QNN under hardware noise. The QNN is the one of [2].

**Circuit and output.**

- **Size.** For m accuracy blocks, m a power of two, the circuit has q = log₂(4m) qubits; write D = 2^q = 4m.
- **Parameters.** These are θ = (a_i, b_i, γ_i)_{i ≤ m}. Block i applies U_1 = H R_z(−b_i) R_z(−a_i·x) H to the first target qubit and U_2 = R_y(γ_i) to the second [2, Section II.A].
- **State and readout.** The ideal state is ρ = ρ(θ, x). Measuring all q qubits in the computational basis gives a basis state k. The grouped outcome is o = k mod 4.
- **Output.** With P_o the probability of o, the output is
  f_θ(x) = R(1 − 2(P_1 + P_2)) = tr(Oρ),  O = R(I − 2(Π_1 + Π_2)),
  where Π_o projects onto the basis states with k mod 4 = o. So O has eigenvalues ±R.
- **Approximation.** If f has L¹[f̂] = B ≤ R, some θ gives ‖f − f_θ‖_{L²(μ)} ≤ B/√m [2, Theorem II.4].

**Noise model.** Depolarising noise after each of the two stages gives [1, Proposition 3.9]

ρ̃ = αρ + (1 − α) I/D.

The hardware model of [1, Section 3.6] has q − 2 one-qubit gates in the first stage and N_2Q = mq/15 two-qubit gates in the second. With gate errors ε_1Q and ε_2Q,

α = (1 − ε_1Q)^{q−2} (1 − ε_2Q)^{mq/15} (1 − p_{T_1}/2)(1 − p_{T_2}/2),

where p_T = 1 − e^{−t/T} accounts for decoherence over the time t = N_2Q t_2Q.

**Affine correction.** The noisy output is f̃ = αf_θ + (1 − α)c₀, where c₀ = tr(O)/D. [1, Theorem 3.15] shows that the affine map (f̃ − (1 − α)c₀)/α returns f_θ exactly. That holds in expectation. With finitely many shots, the 1/α in this map also scales up the statistical error.

**Black-box methods.** Here a method sees only the shot record, together with α and c₀, and must work for every θ. The output of this QNN has the closed form f_θ(x) = (1/m) Σ_i R cos γ_i cos(b_i + a_i·x) [1, Section 4.1.1]. So the bounds below are about evaluating the QNN on the noisy device, not about the approximation task itself.

## Results

Each shot records Y = R(1 − 2·1[o ∈ {1, 2}]). Let Ȳ be the mean of N shots, and

f̂ = (Ȳ − (1 − α)c₀)/α.

**Lemma 1 (a pair of settings).** Take a_i = b_i = 0 and γ_i = γ^± = π/2 ∓ 2η for all i, with sin 2η = ε/R. Then:

- the ideal states are pure: ψ^± = cos(γ^±/2)|A⟩ + sin(γ^±/2)|B⟩. Here |A⟩ and |B⟩ are the uniform superpositions over the m control states with target bits 00 and 01. They lie in the +R and −R eigenspaces of O;
- f^± = ±ε, for every x;
- for the full computational-basis readout, P⁺_k − P⁻_k = ±ε/(Rm) on the 2m basis states with target bits 00 or 01, and 0 elsewhere. On those states P⁻_k ≥ (1 − ε/R)/(2m).

**Theorem 1 (shots at one input).** Fix θ and x.

1. **Upper bound.** E f̂ = f_θ(x) and E|f̂ − f_θ(x)|² ≤ R²/(α²N). Also, P(|f̂ − f_θ(x)| ≥ ε) ≤ 2 exp(−Nα²ε²/(2R²)).
2. **Lower bound, computational-basis readout.** Let ε ≤ 3R/4. Suppose a black-box method uses N shots, each a measurement of all q qubits in the computational basis. Suppose also that for both settings of Lemma 1 it comes within less than ε of the output with probability at least 2/3. Then
   N ≥ R²/(72 α² ε²).
   This also covers the grouped readout, which is a coarse-graining of the full one.
3. **Lower bound, any measurement.** Let ε ≤ R/2. Consider any measurement on N copies of the noisy state, including joint ones such as virtual distillation. If it comes within less than ε for both settings of Lemma 1 with probability at least 2/3, then
   N ≥ (α + 2(1 − α)/D) · R²/(23 α² ε²).

So the correction costs Θ(R²/(α²ε²)) shots with the computational-basis readout, in the worst case over the pair of Lemma 1. The constants differ by a factor of about 260. With any measurement, the cost is at least of order R²/(αε²) when α ≳ 1/D, and of order R²/(Dα²ε²) below that. Since α decays exponentially in the gate count, all these costs are exponential in mq.

**Theorem 2 (budget of the noisy approximation).** Take f with L¹[f̂] = B ≤ R. Run the circuit of [2] with m blocks and N shots per input, and apply the correction.

1. **Error.** (E ∫ |f − f̂|² dμ)^{1/2} ≤ B/√m + R/(α(m)√N), for every α(m).
2. **Accuracy ε.** Let m be the least power of two with m ≥ 4B²/ε², and N = ⌈4R²/(α(m)²ε²)⌉. Then the error is at most ε. Per input,
   N ≤ (4R²/ε²) (1 − ε_1Q)^{−2(q−2)} e^{2c·mq} + 1 = (4R²/ε²) · exp(O(c B² log(B/ε)/ε²)),
   with c = −ln(1 − ε_2Q)/15 + t_2Q(1/T_1 + 1/T_2)/30.
3. **Shots needed at these m blocks.** Since α ≤ (1 − ε_2Q)^{mq/15}, Lemma 1 and Theorem 1 give lower bounds for black-box methods. They concern methods whose estimate of f_θ(x) has mean square error at most ε² for both settings, with √3ε ≤ R/2:
   - with the readout: N ≥ (R²/(216ε²)) (1 − ε_2Q)^{−2mq/15};
   - with any measurement: N ≥ (R²/(69ε²)) (α + 2(1 − α)/D) α^{−2}, which is at least (R²/(69ε²)) (1 − ε_2Q)^{−mq/15}.

   At m ≥ 4B²/ε² both are exp(Ω(ε_2Q B² log(B/ε)/ε²)).
4. **Fixed budget.** With N shots per input, take the largest power of two m with c·m·q ≤ (ln N)/4 − (q − 2)(−ln(1 − ε_1Q)). Then the error is
   O(B √(c log(ln N/c)/ln N) + R N^{−1/4})
   for N large enough that m ≥ 1. So the accuracy guaranteed by this route decreases only like (ln N)^{−1/2}, up to a factor √(log(ln N/c)).

## Numbers

These use the gate-count model of [1, Section 3.6] and the calibration values of [1, Appendix A], with B = R = 1 and m the least power of two with m ≥ 4/ε².

- **The two ends of α.** The upper end of α counts two-qubit gate errors only. The lower end also includes the one-qubit gates and the decoherence factors of [1].
- **Columns.**
  - "suffice" uses the lower end, with N = ⌈4/(α²ε²)⌉ (Theorem 2, part 2).
  - "readout" is the pointwise bound R²/(72α²ε²) of Theorem 1, part 2, at the upper end.
  - "any measurement" is the bound of Theorem 1, part 3, at the upper end.
- **H2 rows.** They omit memory error and decoherence, which [1] also lists, so their "suffice" column is optimistic.

| device | ε | m | q | N_2Q | α | suffice | readout | any measurement |
|---|---|---|---|---|---|---|---|---|
| ibm_fez | 0.1 | 512 | 11 | 375 | 0.31 to 0.38 | 4.1·10³ | 9 | 11 |
| ibm_fez | 0.05 | 2048 | 13 | 1775 | 0.0050 to 0.011 | 6.4·10⁷ | 4.8·10⁴ | 1.7·10³ |
| ibm_fez | 0.02 | 16384 | 16 | 17476 | 1.1·10⁻²⁰ to 4.3·10⁻²⁰ | 8.6·10⁴³ | 1.9·10⁴⁰ | 1.8·10³⁶ |
| H2, gate errors | 0.05 | 2048 | 13 | 1775 | 0.17 | 5.6·10⁴ | 194 | 103 |
| H2, gate errors | 0.02 | 16384 | 16 | 17476 | 2.6·10⁻⁸ | 1.5·10¹⁹ | 5.3·10¹⁶ | 5.1·10¹² |

Take the 8192 shots per circuit used in [1]. Then, on ibm_fez, no black-box method with the readout reaches ε = 0.1 pointwise beyond m = 1024 blocks, for powers of two m. There the approximation term B/√m is about 0.031.

## Proofs

*Lemma 1.*

- **The state.** With a_i = b_i = 0, U_1 = H H = I, so the first target qubit stays in |0⟩. The second is R_y(γ)|0⟩ = cos(γ/2)|0⟩ + sin(γ/2)|1⟩. The control register is uniform over the m = D/4 control states. This gives ψ^±, and f^± = R cos γ^± = ±R sin 2η = ±ε.
- **The readout.** Per basis state, the probabilities are cos²(γ/2)/m and sin²(γ/2)/m. At γ^±, cos²(γ^±/2) = (1 ± ε/R)/2. □

*Theorem 1, part 1.* The shots are independent, with Y ∈ {−R, R} and E Y = tr(Oρ̃) = αf_θ + (1 − α)c₀. So E f̂ = f_θ, and Var f̂ = Var(Y)/(α²N) ≤ R²/(α²N). The tail bound for bounded independent variables, applied to Ȳ at deviation αε, gives the tail bound. □

*Theorem 1, part 2.* The noisy law of the basis state is P̃_k = αP_k + (1 − α)/D. On the 2m states where the two settings differ:

- **The laws differ little.** |P̃⁺_k − P̃⁻_k| = αε/(Rm). Also P̃⁻_k ≥ min{(1 − ε/R)/(2m), 1/(4m)} ≥ 1/(8m) for ε ≤ 3R/4. Hence χ²(P̃⁺ ‖ P̃⁻) ≤ 2m · (αε/(Rm))² · 8m = 16α²ε²/R².
- **So the method yields a test.** The outputs differ by 2ε. Reporting the setting whose output is nearer to the estimate is therefore correct with probability at least 2/3 under each setting. So the total variation distance between the N-shot laws is at least 1/3.
- **The shot count follows.** That distance is at most √(N·KL/2) ≤ √(N·χ²/2), by the bound TV ≤ √(KL/2) and KL ≤ χ². So N ≥ 2/(9χ²) ≥ R²/(72α²ε²). □

*Theorem 1, part 3.*

- **Fidelity of the noisy pair.** Write β = (1 − α)/D. The noisy states agree on the complement of span{|A⟩, |B⟩}, where both equal βI. On the span they are (α + 2β)σ^±. The σ^± are qubit states (I + r_± · (X, Y, Z))/2 with vectors r_± of length r = α/(α + 2β), at angle 4η. The qubit fidelity formula F(σ⁺, σ⁻)² = tr(σ⁺σ⁻) + 2√(det σ⁺ det σ⁻) gives F(σ⁺, σ⁻) = √(1 − r² sin² 2η). So the root fidelity of the noisy states is
  F̃ = (α + 2β)√(1 − r²ε²/R²) + (D − 2)β,
  and 1 − F̃ ≤ (α + 2β) r² ε²/R² = α²ε²/((α + 2β)R²).
- **A test is needed.** As in part 2, the method yields a test between ρ̃⁺^{⊗N} and ρ̃⁻^{⊗N} that succeeds with probability at least 2/3. By the optimal test between two states, the trace distance between them is then at least 1/3.
- **The copy count follows.** Root fidelity is multiplicative on tensor powers, so the bound of [5] gives 1/3 ≤ √(1 − F̃^{2N}). Hence 2N ln(1/F̃) ≥ ln(9/8). Here ln(1/F̃) ≤ (1 − F̃)/F̃, and F̃ ≥ 1 − αε²/R² ≥ 3/4 for ε ≤ R/2. So N ≥ (3 ln(9/8)/8) (α + 2β) R²/(α²ε²), and 3 ln(9/8)/8 > 1/23.

This is the fidelity bound of [6, Theorem 1] applied to the pair of Lemma 1. □

*Theorem 2.*

- **Part 1.** By the triangle inequality in L²(μ ⊗ shots), the error is at most ‖f − f_θ‖_{L²(μ)} + sup_x (E|f̂(x) − f_θ(x)|²)^{1/2}. The two terms are bounded by [2, Theorem II.4] and Theorem 1, part 1.
- **Part 2.**
  - Each term is then at most ε/2.
  - Since (1 + e^{−s})/2 ≥ e^{−s/2}, each decoherence factor is at least e^{−t/(2T)}, with t = N_2Q t_2Q = mq t_2Q/15. So −ln α ≤ (q − 2)(−ln(1 − ε_1Q)) + c·mq.
  - Finally, mq = O((B²/ε²) log(B/ε)), since m < 8B²/ε².
- **Part 3.**
  - Suppose the mean square error is at most ε² for both settings. Then the second moment inequality gives accuracy below √3ε with probability at least 2/3.
  - So Theorem 1 applies to the pair of Lemma 1 built for √3ε. The pair does not depend on x.
  - Use α ≤ (1 − ε_2Q)^{mq/15}. For the second bound, note also (α + 2β)/α² ≥ 1/α. Here −ln(1 − ε_2Q) ≥ ε_2Q, and q ≥ log₂(16B²/ε²).
- **Part 4.**
  - By the choice of m, α ≥ N^{−1/4}, so the shot term is at most R N^{−1/4}.
  - By maximality, 2m violates the condition. So m ≥ (ln N)/(8c·q(2m)) − (−ln(1 − ε_1Q))/(2c), with q(2m) = q(m) + 1.
  - Also q = O(log(ln N/c)). So B/√m = O(B √(c log(ln N/c)/ln N)). □

## Remarks

1. **Relation to error mitigation bounds.**
   - Part 3 of Theorem 1 is the fidelity bound of [6] for the pair of Lemma 1, which has an explicit fidelity.
   - [7] shows that unbiased mitigation of global depolarising noise costs order (1 − α)/α² in variance, and that plain rescaling attains it asymptotically.
   - [3] and [4] prove that the sample cost grows exponentially with depth under local depolarising noise, for broad classes of methods.
   - Part 2 is a standard two-point bound for the readout of [1].

   The new content is the explicit pair for the QNN of [2] and Theorem 2. Theorem 2 combines these costs with the approximation rate of [2] into a shot budget.
2. **Scope.**
   - Both lower bounds are worst case over the pair of Lemma 1 at one input, and they hold for black-box methods only.
   - Parts 2 and 4 of Theorem 2 are upper bounds obtained by this route.
   - Parts 2 to 4 use the gate-count model of [1, Section 3.6], N_2Q = mq/15. Under that model α decays like e^{−Θ(ε_2Q m log m)}, so the shot cost is driven by the number of blocks m. A count that grows like D instead would give e^{−Θ(ε_2Q m)}.
   - The lower bounds remain valid whenever the true α is smaller than the modelled one.
   - The note assumes that α and c₀ are known. An error Δα adds a bias of order |Δα|/α to f̂.
   - Readout bit-flip error [1, Section 3.7] is not treated.
   - The case D > 4m is also not treated. There the control register of [1, Proposition 3.4] is spread over more than m states.
3. **Between the two lower bounds.** For α ≳ 1/D, the bound for joint measurements scales as 1/α and the readout bound as 1/α². A matching upper bound of order 1/α for joint measurements is not treated here. Over mixed ideal states, or for estimators unbiased everywhere, order 1/α² is necessary [7].

## Check

`sim/shot_check.py` checks the following:

- **Upper bound.** The corrected estimator is unbiased, with mean square error at most R²/(α²N), on 30 random cases.
- **Readout lower bound.** The exact total variation of the two shot records at N = R²/(72α²ε²) is below 1/3. This includes the worst case where the ideal and uniform weights are 1/8.
- **The pair.** Lemma 1 holds on D = 16.
- **Fidelity.** The concavity inequality holds on 200 random mixed pairs. The closed form of F̃ matches a direct computation, and F̃^{2N} ≥ 8/9 at the bound of part 3, including α < 1/D.
- **Numbers.** It computes the table above.

```
a = 0.2, eps = 0.1, P = 0.125, u = 0.125: at N = 34, TV of the two shot records = 0.1853 < 1/3
realizable pair on D = 4m: f = +-eps, per-basis readout differs by eps/(R m) on 2m states, each of ideal probability >= 1/(8m)
a = 0.0001, eps = 0.3, D = 64: F~ matches its closed form; at N = 1514341, F~^(2N) = 0.9575 >= 8/9
ibm_fez, eps = 0.05: m = 2048, q = 13, N2Q = 1775, alpha in [0.00502, 0.0108], shots per point: suffice 6.36e+07, readout lower bound 4.76e+04, any measurement 1.65e+03
ibm_fez, N = 8192, eps = 0.1: the readout cannot reach eps pointwise beyond m = 1024 blocks (powers of two; B/sqrt(m) = 0.031)
shot cost checks pass
```

## References

1. L. Gonon, A. Jacquier, M. Mordarski. Quantitative universal approximation for noisy quantum neural networks. arXiv:2604.02064.
2. L. Gonon, A. Jacquier. Universal approximation theorem and error bounds for quantum neural networks and quantum reservoirs. IEEE Transactions on Neural Networks and Learning Systems (2025), arXiv:2307.12904.
3. R. Takagi, S. Endo, S. Minagawa, M. Gu. Fundamental limits of quantum error mitigation. npj Quantum Information 8, 114 (2022), arXiv:2109.04457.
4. Y. Quek, D. Stilck França, S. Khatri, J. J. Meyer, J. Eisert. Exponentially tighter bounds on limitations of quantum error mitigation. Nature Physics 20, 1648 (2024), arXiv:2210.11505.
5. C. A. Fuchs, J. van de Graaf. Cryptographic distinguishability measures for quantum-mechanical states. IEEE Transactions on Information Theory 45, 1216 (1999).
6. R. Takagi, H. Tajima, M. Gu. Universal sampling lower bounds for quantum error mitigation. arXiv:2208.09178.
7. K. Tsubouchi, T. Sagawa, N. Yoshioka. Universal cost bound of quantum error mitigation based on quantum estimation theory. arXiv:2208.09385.
