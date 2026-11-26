# Constants in the sample complexity of wave matrix Lindbladization

2026-11-26

Wave matrix Lindbladization (WML) simulates the Lindbladian with one jump operator L on a d-dimensional system from copies of a program state that encodes L [1]. Each copy drives one step of time Δ = t/n. The number of copies is set by the leading constant of the one-step error, in the normalized diamond distance and with ‖L‖₂ = 1. This folder pins down that constant up to an additive constant, for WML and for every protocol, and gives a one-copy step whose constant d/4 + O(1) matches the lower bound for every protocol up to an additive constant.

The results are also written up as a paper, [paper/main.pdf](paper/main.pdf) (source `paper/main.tex`). There Theorem 8 is Theorems 1 and 3, Theorem 7 is Theorems 2 and 4, Theorems 2 and 3 are Theorems 5 and 6, and Theorem 1 is the remark on [1, Eq. (40)].

| Quantity | Previous bound | Here |
|---|---|---|
| One-step error of WML, leading constant, worst case over L | at most (2d+3)/8 · ‖L‖∞² [1, Lemma 4] | between (2d−3)/4 and d/2 + 1 (Theorems 1 and 2) |
| Copies needed by WML for time t and error ε, ‖L‖∞ ≤ 1 | at most (2d+3)/8 · t²/ε [1, Theorem 3] | at most (d/2 + e^{1/d}) t²/ε for n > 2dt (Theorem 2) |
| Copies needed by WML in the worst case over L, as ε → 0 | at least d/32 · t²/ε [1, Theorem 10] | at least (d−1)/4 · t²/ε for every t, and (2d−3)/4 · t²/ε as t → 0 (Theorem 3) |
| Copies needed by any regular memoryless protocol with a bounded number of fresh copies per step and comparable step sizes, as n → ∞ | at least 10⁻⁴ · t²/ε, for every protocol [2] | at least (d−1)/4 · t²/ε, with the same constant as WML on the witness L = \|0⟩⟨0\| (Theorem 4) |
| One-copy error of any channel from S ⊗ P to S, worst case over L, as t → 0 | | at least (d−1)/4 · t² − O(t³) (Theorem 5) |
| Copies needed by every protocol (any number of copies, joint processing allowed), for t ≤ c/d | at least 10⁻⁴ · t²/ε [2] | at least (d−1)/4 · (1 − O(dt)) · t²/ε (Theorem 6) |
| Copies needed by every protocol in the high-accuracy regime ε ≤ t²/(C′ d log(2d/t)), for t ≤ c | at least 10⁻⁴ · t²/ε [2] | at least (d−1)/4 · (1 − O(t)) · t²/ε (Theorem 7) |
| Copies needed by every protocol at moderate accuracy, d ≥ 3 | at least 10⁻⁴ · t²/ε [2] | at least (d−2)(1 − e^{−t})²/(32ε) for ε ≤ (1 − e^{−t})/8; for t ≤ 1 and ε ≤ 0.079 t this is at least 0.0124 (d−2) t²/ε (Theorem 8) |
| Copies sufficient for every L, with one program copy per step | at most (2d+3)/8 · t²/ε for WML [1, Theorem 3]; at most (d/2 + e^{1/d}) t²/ε (Theorem 2) | at most (d/4 + 1) t²/ε + 2t for ε ≤ t, by a new one-copy step (Theorem 9); its leading constant is (d−1)/4 for d = 2, 3, 4, 5 on all operators tested |

The first three rows are about the WML protocol, as in [1, Theorem 10]. The fourth row covers the class of Theorem 4, the fifth every channel that uses one copy, and the last every protocol, for short times t ≤ c/d. For t of order one the lower bound for all protocols remains 10⁻⁴ · t²/ε [2].

## Setting

One WML step applies exp(ΔM) to ρ ⊗ π_L and traces out the program, where M is the fixed Lindbladian of [1, Eqs. (14), (15)] and π_L = |L⟩⟨L| with |L⟩ = (L ⊗ I)|Γ⟩. By the transfer matrix of [1, App. B], the step is

Φ_Δ = id + Δ ℒ + c_J(Δ) J + c_A(Δ) A + c_D(Δ) D₁∘J,

with J = L · L†, A = {L†L, ·}/2, ℒ = J − A, and D₁ = (I/d) Tr. The coefficients have the closed forms

- c_A = (2/d) u² φ(u),
- c_D = (d u²/(d²−2)) [4(d²−1) φ(v)/d² − 2φ(u)],
- c_J = −Δ² (d²−1) φ(v)/d − 2c_D/d²,

where u = Δd/2, v = Δ(d − 1/d) and φ(z) = (e^{−z} − 1 + z)/z². Their leading terms are c_J ≈ −dΔ²/2 and c_A ≈ c_D ≈ dΔ²/4.

## Results

**Theorem 1 (a jump operator with a large error).** Let L = |0⟩⟨1|, so ‖L‖₂ = ‖L‖∞ = 1, and take the input state |1⟩⟨1|. Then the one-step error of WML is Δ² (2d−3)/4 + O(Δ³).

- For d ≥ 5 and small Δ this exceeds Δ² (2d+3)/8. The excess is 7% at d = 5 and grows towards a factor 2 as d grows.
- The n-step error exceeds (2d+3) t²/(8n) for small t and n > 2dt. At t = 0.02 the ratio is 1.06 (d = 5), 1.18 (d = 6), 1.35 (d = 8) and 1.53 (d = 12).
- Full-rank perturbations of L give the same picture.

This hints at a possible gap in [1, Eq. (40)]. To leading order, L̃ − L = (Δd/4) A − (Δd/2) J, whose diamond norm for this L is 3Δd/4 rather than Δd/4. Eq. (41), which follows from Eq. (40), fails for every d ≥ 2: ‖Φ_Δ − id − Δℒ‖⋄/Δ² tends to (2d−1)/2 rather than d/2.

The tail estimate in [1, Eq. (36)] reads (3/4)Δ²‖L‖∞². With x = 2Δ‖L‖∞², the bound e^x − x − 1 ≤ (3/4)x² gives 3Δ²‖L‖∞⁴. The scaling O(d t²/ε) of [1] is not affected; only the constants change.

**Theorem 2 (corrected bound).** For every L with ‖L‖₂ = 1, every d ≥ 2 and every Δ ≤ 1/(2d),

½ ‖e^{Δℒ} − Φ_Δ‖⋄ ≤ Δ² ‖L‖∞² (d/2 + e^{1/d} ‖L‖∞²).

*Proof.*
- **Coefficients.** φ is decreasing with values in (0, 1/2], and v ≥ u. This gives 0 < c_A ≤ dΔ²/4 and 0 < c_D ≤ dΔ²/4, using φ(v) ≥ φ(1/2) > 1/3 for the sign. Both parts of c_J are negative, so |c_J| ≤ dΔ²/2.
- **Maps.** J and D₁∘J are completely positive with adjoint value L†L at the identity, and A is bounded by ‖L†L‖. So each has diamond norm at most ‖L‖∞², and ‖ℒ‖⋄ ≤ 2‖L‖∞².
- **Tail.** The exponential series gives ‖e^{Δℒ} − id − Δℒ‖⋄ ≤ e^x − 1 − x ≤ x² e^x/2, with x = 2Δ‖L‖∞² ≤ 1/d.

Summing these over n steps, the error after n > 2dt steps is at most (d/2 + e^{1/d}‖L‖∞²) ‖L‖∞² t²/n. So n ≥ max(2dt, (d/2 + e^{1/d}) t²/ε) copies suffice for ‖L‖∞ ≤ 1. Together with Theorem 1, the worst-case leading constant lies between d/2 − 3/4 and d/2 + 1.

**Theorem 3 (lower bound for WML).** For L = |0⟩⟨0|, the witness of [1, Theorem 10], with input |0⟩⟨0|:

- the input is fixed by e^{tℒ};
- each step leaks Δ² (d−1)/4 in trace distance, at leading order;
- these errors add up without decay.

Hence n · error/t² tends to (d−1)/4 as n → ∞, for every t. For L = |0⟩⟨1| the same limit tends to (2d−3)/4 as t → 0. The number of copies WML needs in the worst case over L is therefore at least (max{(d−1)/4, c(t)} − o(1)) t²/ε as ε → 0, where c(t) is the limit for L = |0⟩⟨1|. This is at least 8(d−1)/d ≥ 4 times the constant d/32 of [1, Theorem 10], for every t.

**Theorem 4 (lower bound for regular protocols with fresh copies in each step).** Consider protocols that are sequential and memoryless and use fresh copies of the program state in each step: step j uses k_j ≤ k_max copies and applies a channel Λ⁽ʲ⁾_{Δ_j} from S ⊗ P^{⊗k_j} to S, with Δ₁ + … + Δ_m = t and n = k₁ + … + k_m copies in all. Each family Λ_Δ is assumed to

- (H) agree with the target to first order: Λ_Δ(ρ ⊗ π_L^{⊗k}) = ρ + Δℒ_L(ρ) + O(Δ²) for all ρ and L;
- (R) be regular: Λ_Δ = Tr_P + ΔG + Δ²E + R_Δ with ‖E‖⋄ ≤ K and ‖R_Δ‖⋄ ≤ KΔ³ for Δ ≤ Δ₀, with one constant K for all steps;
- (S) use comparable step sizes: Δ_j ≤ c·k_j·t/n for a fixed constant c ≥ 1, as WML does with k_j = 1 and c = 1.

Let ε be the error on L = |0⟩⟨0| with input |0⟩⟨0|, in normalized trace distance; it is at most the worst-case diamond error. Then ε ≥ (d−1)/4 · S · (1 − O(√(t·max_j Δ_j) + max_j Δ_j)) for max_j Δ_j ≤ Δ₀, with S = Δ₁²/k₁ + … + Δ_m²/k_m ≥ t²/n, the constants depending on K, k_max and d. Hence n·ε ≥ ((d−1)/4 − o(1)) t² as n → ∞, for every fixed t: along protocols whose number of copies grows, error ε needs at least ((d−1)/4 − o(1)) t²/ε copies. Several copies per step do not lower the constant per copy. WML, with one copy per step, belongs to the class and its error on this witness is (d−1)/4 · t²/n to leading order (Theorem 3), so the constant cannot be raised for this witness.

*Proof sketch.*
1. **The map G is forced where it matters.** By (R), Λ₀ = Tr_P; on symmetric programs linearity alone forces this. The operators |v⟩⟨v|^{⊗k} with unit v span all operators on the symmetric subspace Sym^k(P), so (H) fixes G on L(S) ⊗ L(Sym^k(P)). There it equals the average over the copies of the one-copy map ρ ⊗ |L⟩⟨L′| ↦ Lρ L′† − ½(L′†L ρ + ρ L′†L), with the trace on the other copies. The Choi matrix of Tr_P is C₀ = |Γ⟩⟨Γ| ⊗ I.
2. **Positivity bounds E.** The Choi matrix of Λ_Δ is positive for Δ ∈ [0, Δ₀). For a vector e with C₀e = 0 and e†C₁e = 0, positivity at first order puts C₁e in the range of C₀. Testing with e + Δf, f = −C₀⁺C₁e, gives e†C₂e ≥ e†C₁C₀⁺C₁e, where C₂ is the Choi matrix of E. The right-hand side is at least its part on Sym^k(P), which step 1 fixes.
3. **The forced leak.** For L = |0⟩⟨0| and the vector e_i = |0⟩|L⟩^{⊗k} ⊗ |i⟩, i ≠ 0, the symmetric part equals 1/(4k). So a step with k copies moves at least (d−1)Δ²/(4k) out of |0⟩ at second order. Running k steps of WML with time Δ/k each attains this.
4. **Accumulation.** The exact evolution keeps |0⟩⟨0| fixed. Population that has left |0⟩ returns only at order Δ², because ⟨0|X|0⟩ = 0 and ⟨0|ℒ_L(X)|0⟩ = 0 for the part X of the state outside |0⟩⟨0|. The coherences between |0⟩ and its complement are at most the square root of the population outside |0⟩, so the return in step j is O(KΔ_j²(p + √p)) for an outside population p. Summing over the steps gives the bound on ε. By the Cauchy-Schwarz inequality, S ≥ (Δ₁ + … + Δ_m)²/(k₁ + … + k_m) = t²/n, and under (S), max_j Δ_j ≤ c·k_max·t/n tends to 0 as n grows. ∎

Protocols with memory across steps, steps far from Tr_P, or step sizes that do not shrink with n are outside the class. The bound is asymptotic in n: rescaling WML to Λ_Δ = Φ_{Δ(1−Δ/Δ₀)} with Δ₀ = t/n satisfies (H), (R) and (S), and every step of size Δ₀ is then Tr_P, which has zero error on this witness for that n.

**Theorem 5 (every channel that uses one copy).** For every d ≥ 2 there is a constant K_d such that every channel Λ from S ⊗ P to S and every t ∈ (0, 1] satisfy

sup_L ½ ‖Λ(· ⊗ π_L) − e^{tℒ_L}‖⋄ ≥ (d−1)/4 · t² − K_d t³,

with the supremum over all L with ‖L‖₂ = 1. No step structure, expansion or regularity in t is assumed. The supremum may be restricted to finitely many operators: L = |0⟩⟨0| together with any finite set whose program states span all operators on P.

*Proof.* Let ε be the supremum, A = Λ − Tr_P and G the forced map of Theorem 4, step 1, and set B = A − tG.
1. **B is small on every input.** For every L, B(ρ ⊗ π_L) = (e^{tℒ_L} − id − tℒ_L)(ρ) + (Λ(ρ ⊗ π_L) − e^{tℒ_L}(ρ)). Since ‖ℒ_L‖⋄ ≤ 2, this has diamond norm at most 2e²t² + 2ε. Fix finitely many L_k whose π_{L_k} span the operators on P. Every matrix unit of S ⊗ P is then a fixed combination of products Y ⊗ π_{L_k}, so every entry of the Choi matrix C_B of B is at most κ_d (t² + ε).
2. **Positivity.** The Choi matrix of Λ is C₀ + tC₁ + C_B ≥ 0, with C₀ and C₁ as in Theorem 4. For L = |0⟩⟨0| and e_i = |0⟩|L⟩ ⊗ |i⟩, i ≠ 0, test it with e_i + tf, f = −C₀⁺C₁e_i. The terms of order t² give −t²/4, as in Theorem 4. The terms that involve C_B give e_i†C_B e_i plus at most κ′_d t(t² + ε). The term t³ f†C₁f is O(t³). Hence e_i†C_B e_i ≥ t²/4 − κ″_d t(t² + ε).
3. **The witness.** For L = |0⟩⟨0|, ℒ_L(|0⟩⟨0|) = 0, so e^{tℒ_L} fixes |0⟩⟨0| and e_i†C_B e_i = ⟨i|Λ(|0⟩⟨0| ⊗ π_L)|i⟩. Summed over i ≠ 0 this is the population that leaves |0⟩, which is at most the trace distance to |0⟩⟨0|, hence at most ε.
4. **Conclusion.** Together, ε ≥ (d−1)t²/4 − (d−1)κ″_d t(t² + ε). If ε > (d−1)t²/4 there is nothing to prove; otherwise ε ≤ dt², and the claim follows with K_d = 2d(d−1)κ″_d. ∎

Theorem 5 is a lower bound. Over the operators of step 1, the optimal one-copy channel, computed by an exact semidefinite program over all channels, has error divided by t² equal to 0.2374, 0.2437 and 0.2470 for t = 0.04, 0.02 and 0.01 at d = 2, and 0.4667, 0.4834 and 0.4924 at d = 3. These are lower bounds on the worst case over all L, and they approach (d−1)/4 with a deficit of order t, as the proof predicts.

**Theorem 6 (every protocol, any number of copies, short times).** There is an absolute constant K such that for every d ≥ 2, every n ≥ 1, every t ∈ (0, 1/2] and every channel Λ from S ⊗ P^{⊗n} to S, with any joint processing of the n copies,

sup_L ½ ‖Λ(· ⊗ π_L^{⊗n}) − e^{tℒ_L}‖⋄ ≥ (d−1)/(4n) · t² · (1 − K d t).

The supremum may be restricted to L = |0⟩⟨ψ| with ψ = cos θ |0⟩ + e^{−iφ} sin θ |i⟩, over all θ, φ and i = 1, …, d − 1. Hence for t ≤ c/d with an absolute constant c, every protocol, sequential or collective, needs at least ((d−1)/4)(1 − O(dt)) t²/ε copies. In this regime the factor d of the WML bound is necessary, and WML has the same constant (d−1)/4 on the witness L = |0⟩⟨0| (Theorem 3).

*Proof sketch.* Let ε be the supremum. Write ℓ = |L⟩ for L = |0⟩⟨0|, q_i = |0⟩|i⟩ ∈ P, v = cos θ ℓ + e^{iφ} sin θ q_i, and τ̂ = n^{−1/2} Σ_j |ℓ … q_i … ℓ⟩ (q_i in copy j).
1. **The Choi matrix.** Let G be the average over the copies of the one-copy map of Theorem 4 (step 1), with the trace on the other copies, and B = Λ − Tr_P − tG. The Choi matrix of Λ is C₀ + tC₁ + C_B ≥ 0.
2. **Two test vectors.** Take e = |0⟩|ℓ⟩^{⊗n}|i⟩ and f = −C₀⁺C₁e = (2d√n)^{−1} Σ_m |m⟩|τ̂⟩|m⟩. Then e†C₀e = e†C₁e = 0, so e†Ce is the population ⟨i|Λ(|0⟩⟨0| ⊗ π_ℓ^{⊗n})|i⟩ that leaves |0⟩ towards |i⟩. Also f†C₀f = 1/(4n), e†C₁f = −1/(4n) and f†C₁f ≤ 0. Positivity of the 2 × 2 compression gives e†Ce ≥ |e†Cf|²/f†Cf.
3. **Bernstein's inequality.** The map (θ, φ) ↦ Λ(· ⊗ π_v^{⊗n}) is a trigonometric polynomial of degree 2n in θ, and the Taylor polynomial of e^{tℒ_v} of order n + 1 has degree 2n + 2, with remainder at most 4e²t²(2t)^n/(n+2)!. Their difference is a trigonometric polynomial of degree at most 2n + 2 and lies within 2ε + 4e²t²(2t)^n/(n+2)! of zero for all θ, φ. By Bernstein's inequality its first and second θ-derivatives are at most 4n and 16n² times that bound. At θ = 0 these derivatives, the first at two phases and the second averaged over φ, are B applied to |τ̂⟩⟨ℓ^{⊗n}| (times √n) and to |τ̂⟩⟨τ̂| (times 2n, minus 2n π_ℓ^{⊗n}), up to the smooth part of the exponential, which is O(t²). This gives |e†C_B f| ≤ 4ε + O(t²/n) and f†C_B f ≤ O(ε + t²/n), uniformly in n; the factors of d cancel, so K is absolute.
4. **Conclusion.** With e†Cf = −t/(4n) + e†C_B f, the leak towards |i⟩ is at least t²/(4n) · (1 − O(nε/t + t)). Summing over the d − 1 states |i⟩ bounds ε from below. If nε > (d−1)t²/4 there is nothing to prove; otherwise nε/t ≤ dt/4, and the claim follows. ∎

The correction O(dt) comes from the term nε/t, and Theorem 6 says nothing for t ≳ 1/d. The bound is not claimed tight for WML: on the family of Theorem 6, which contains L = |0⟩⟨1|, the worst-case constant of WML is (2d−3)/4. Protocols with a random number of copies are not covered. On the collective WML channel, which uses its n copies in n steps of time t/n, the bound of step 4 captures 99.0% to 99.9% of the true leak for n ≤ 3, d ≤ 3 and t between 0.0125 and 0.05.

**Theorem 7 (every protocol, high accuracy).** There is an absolute constant C such that for every d ≥ 2, every n ≥ 1, every t ∈ (0, 1/2] and every channel Λ from S ⊗ P^{⊗n} to S,

n · sup_L ½ ‖Λ(· ⊗ π_L^{⊗n}) − e^{tℒ_L}‖⋄ ≥ (d−1)/4 · t² · (1 − C t (1 + d · min{1, √(log(2n/t)/n)})),

with the supremum over the family of Theorem 6.

**Corollary.** There are absolute constants c and C′ such that for t ≤ c and ε ≤ t²/(C′ d log(2d/t)), every protocol with error at most ε on this family uses at least ((d−1)/4)(1 − C′t) t²/ε copies. In the high-accuracy regime the factor d of the WML bound is therefore necessary for every protocol at every time t ≤ c, with c independent of d, and the leading constant is (d−1)/4.

*Proof sketch.* Only step 3 of Theorem 6 changes: the degree 2n + 2 in Bernstein's inequality is replaced by an effective degree k₀.
1. **Harmonic split.** Let W = span{ℓ, q_i}. The states π_v^{⊗n} lie in L(Sym^n W), on which SU(2) acting on W gives the operators of spin k = 0, …, n. Write π_v^{⊗n} = Σ_k O_k(v) with O_k(v) of spin k. Each O_k(v) is a rotation of O_k(ℓ), and ‖O_k‖₂² = (2k+1) n!²/((n−k)!(n+k+1)!).
2. **Trace-norm tail.** (n+1)‖O_k‖₂²/(2k+1) = ∏_{j<k} (n−j)/(n+j+2) ≤ e^{−k(k+1)/(2n+1)} ≤ e^{−k²/(2n)}, and O_k has rank at most n + 1. Hence ‖O_k(v)‖₁ ≤ √(2k+1) e^{−k²/(4n)} for every v.
3. **Degrees.** Λ(· ⊗ O_k(v)) has diamond norm at most ‖O_k‖₁, and its entries are spherical harmonics of degree k on the Bloch sphere of W, whose polar angle is 2θ. So it is a trigonometric polynomial of degree 2k in θ. Since ℒ_v is linear in |v⟩⟨v|, the Taylor polynomial of order k₀ of e^{tℒ_v} has degree at most 2k₀ in θ.
4. **Truncated Bernstein.** Let k₀ = min{n + 1, ⌈√(24 n log(2n/t))⌉}, and apply step 3 of Theorem 6 to Σ_{k ≤ k₀} Λ(· ⊗ O_k(v)) minus the Taylor polynomial of order k₀, a trigonometric polynomial of degree at most 2k₀. The discarded parts and their first two θ-derivatives are bounded by Σ_{k > k₀} (2k)^r ‖O_k‖₁ ≤ t²/n for r = 0, 1, 2. Bernstein's factors become 2k₀ and 4k₀² in place of 4n and 16n², so |e†C_B f| ≤ 2k₀ε/n + O(t²/n) and f†C_B f ≤ O(k₀²ε/n + ε + t²)/(4n).
5. **Conclusion.** As in step 4 of Theorem 6, the leak towards |i⟩ is at least t²/(4n) · (1 − O(k₀ε/t + t)), where the denominator f†Cf contributes O(k₀²ε/n + ε + t²) ≤ O(k₀ε/t + t²) relative to 1/(4n). If nε > (d−1)t²/4 there is nothing to prove; otherwise k₀ε/t ≤ (d−1) t k₀/(4n), and k₀/n ≤ C min{1, √(log(2n/t)/n)}. For the corollary, discarding copies makes the optimal error non-increasing in n, so a protocol with fewer than N₀ = ⌈A d² log(2d/t)⌉ copies has error at least the bound at N₀, where d √(log(2N₀/t)/N₀) ≤ 1. ∎

For k₀ = n + 1, Theorem 7 is Theorem 6; it improves on it for n ≳ d² log(2n/t). Moderate accuracies between t²/(C′ d log(2d/t)) and order one are covered only by Theorem 6, for t ≤ c/d.

**Theorem 8 (every protocol, moderate accuracy).** Let d ≥ 3, n ≥ 1, t > 0 and θ ∈ (0, π/2), and write c = cos θ, s = sin θ, a = 1 − e^{−t/2} and γ = a(1 − ac²). For a unit vector u orthogonal to |0⟩ let ψ_u = c|0⟩ + s ū, where ū is the entrywise complex conjugate in the computational basis, and let ε_θ be the worst case over u of the error of a channel Λ from S ⊗ P^{⊗n} to S on L = |0⟩⟨ψ_u|. Then

n · ε_θ ≥ (d−2) · (cγ − ε_θ/s)₊².

The bound already holds for the trace-norm error on the single input |0⟩⟨0|.

**Corollary.** Let ε be the worst case over the whole family. Then ε ≥ ε_θ for every θ, and the right side decreases in ε_θ. With θ = π/4 one has γ = (1 − e^{−t})/2, so every protocol with ε ≤ (1 − e^{−t})/8 uses at least (d−2)(1 − e^{−t})²/(32ε) copies. Since 1 − e^{−t} ≥ 0.632 t for t ≤ 1, the accuracy ε ≤ 0.079 t gives n ≥ 0.0124 (d−2) t²/ε for t ≤ 1, and ε ≤ 0.079 gives n ≥ 0.0124 (d−2)/ε for t ≥ 1. With β_t = e^{−t/2}(1 − e^{−t/2}) ≤ γ and sin θ = (ε/2β_t)^{1/3}, also n ε ≥ (d−2) β_t² (1 − 3(ε/2β_t)^{2/3})₊², whose constant tends to (d−2)/4 as t and ε/t tend to 0.

*Proof sketch.*
1. **Reduction.** Fix the input |0⟩⟨0|. Then T = Λ(|0⟩⟨0| ⊗ ·) is a channel on (C^d)^{⊗n} with ½ ‖T(φ_u^{⊗n}) − σ_u‖₁ ≤ ε_θ, where σ_u = e^{tℒ}(|0⟩⟨0|) and the program is |L⟩ = Σ_j L|j⟩|j⟩ = |0⟩ ⊗ φ_u with φ_u = c|0⟩ + s u. The program carries u, while σ_u carries ū.
2. **The target coherence.** The state σ_u is supported on span{|0⟩, ū}, and its coherence q = ⟨ū|σ_u|0⟩ is real. Every jump resets the state to |0⟩, and the no-jump evolution maps |0⟩ to (1 − ac²)|0⟩ − acs |ū⟩. So q = q₀ + c² ∫₀ᵗ e^{−τ} q(t − τ) dτ with q₀ = −csγ. The kernel is the density of the first jump, hence q ≤ q₀ < 0 and |q| ≥ csγ.
3. **Two tests.** With W_u = −(|0⟩⟨ū| + |ū⟩⟨0|) and Π_u = 1 − |0⟩⟨0| − |ū⟩⟨ū|, and u Haar-distributed, set X = E_u Tr W_u T(φ_u^{⊗n}) and Y = E_u Tr Π_u T(φ_u^{⊗n}). Since ‖W_u‖∞ = 1, Tr W_u σ_u = −2q and Tr Π_u σ_u = 0, one has X ≥ 2csγ − 2ε_θ and Y ≤ ε_θ.
4. **A dual certificate.** Let J_T = Σ_{ij} T(|i⟩⟨j|) ⊗ |i⟩⟨j|, so that Tr M T(ρ) = Tr J_T (M ⊗ ρᵀ) and Tr_out J_T = 1. The transpose maps φ_u to χ_v = c|0⟩ + s v with v = ū, so for every λ > 0, X − λY = Tr J_T Ω with Ω = E_v[(−|0⟩⟨v| − |v⟩⟨0| − λΠ_v) ⊗ (|χ_v⟩⟨χ_v|)^{⊗n}]. This is where the conjugation enters: both factors of Ω now carry v. Let H_k be the span of the normalized symmetric states |k; v⟩ with k factors v and n − k factors |0⟩, so that H_k ≅ Sym^k(C^{d−1}) with projector Π_k and dimension D_k. Then χ_v^{⊗n} = Σ_k √b_k |k; v⟩, with b_k the Binomial(n, s²) weights, and E_v (vv†)^{⊗k} = Π_{Sym^k}/D_k. After the phase average v ↦ e^{iα}v, only the cross terms |0⟩⟨v| ⊗ |k; v⟩⟨k−1; v| and the terms diagonal in k remain, and Ω vanishes on |0⟩ ⊗ H_0 and outside ⊕_k C^d ⊗ H_k. The cross term maps the copy of Sym^k(C^{d−1}) inside C^{d−1} ⊗ H_{k−1} isometrically onto |0⟩ ⊗ H_k, with weight g_k = √(b_k b_{k−1})/D_k. On C^{d−1} ⊗ H_{k−1} the term λΠ_v equals λ h_{k−1} on that copy, with h_{k−1} = b_{k−1}(1/D_{k−1} − 1/D_k) = b_{k−1}(d−2)/(D_{k−1}(k+d−2)), and λ b_{k−1}/D_{k−1} on its complement; d ≥ 3 makes h_{k−1} positive. With X_op = Σ_{k≥1} x_k Π_k and x_k = g_k²/(λh_{k−1}), the operator 1 ⊗ X_op − Ω consists of the blocks [[x_k, g_k], [g_k, x_{k−1} + λh_{k−1}]] for k = 1, …, n (each tensored with the identity on Sym^k) and is diagonal and non-negative elsewhere. Each block is positive semidefinite, since x_k · λh_{k−1} = g_k² and x_{k−1} ≥ 0. Hence X − λY ≤ Tr X_op = Σ_k D_k x_k = Σ_k k b_k/(λ(d−2)) = n s²/(λ(d−2)).
5. **Conclusion.** Optimizing over λ gives Y ≥ (d−2) X²/(4 n s²), and step 3 gives the claim. The corollary takes θ = π/4, and sin θ = (ε/2β_t)^{1/3} together with γ ≥ β_t and √(1 − x²) ≥ 1 − x²; the second form needs ε < 2β_t and is trivial otherwise. ∎

The mechanism is universal conjugation of the program state; compare the optimal fidelity (n + 1)/(n + d) of state estimation from n copies [3].

**Numerical supremum.** The supremum of the leading constant over all L, computed with an exact semidefinite program for the diamond norm and local search over L, is about 0.300 at d = 2 and 0.750 at d = 3. At d = 3 this equals (2d−3)/4.

**Theorem 9 (a one-copy step with constant d/4 + O(1)).** For a program |L⟩ = Σ_{ab} L_{ab} |a⟩|b⟩ on P = C^d ⊗ C^d and 0 < Δ ≤ 4/d, define the channel Λ_Δ from S ⊗ P to S by the d² + 1 Kraus operators

- A_{ac} |s⟩|a′⟩|b⟩ = δ_{aa′} (δ_{cb} |s⟩ − (Δ/2) δ_{bs} |c⟩) for a, c = 1, …, d,
- A_J |s⟩|a⟩|b⟩ = √(Δ(1 − dΔ/4)) δ_{bs} |a⟩.

Then Λ_Δ(ρ ⊗ π_L) = ρ + Δ ℒ(ρ) + Δ² E_L(ρ) exactly, with E_L(ρ) = ¼ Tr(ρK) I − (d/4) LρL† and K = L†L. Applying Λ_{t/n} n times, each time with a fresh copy, gives error at most t² e_L/n + (2/3) t³ e^{2t/n}/n² for every L with ‖L‖₂ = 1, where e_L = ½‖E_L − ℒ²/2‖⋄ ≤ (d − 1/d)‖K‖/4 + ‖K‖² ≤ d/4 + 1. Hence n = ⌈(d/4 + 1) t²/ε + 2t⌉ copies give error at most ε, for every ε ≤ t.

Proof sketch.
1. **Kraus form.** With the rows r_a = Σ_b L_{ab} ⟨b|, the operators A_{ac} act on ρ ⊗ π_L as L_{ac} I − (Δ/2)|c⟩ r_a. Summing over a and c gives Tr(K) ρ − (Δ/2){K, ρ} + (Δ²/4) Tr(ρK) I, since Σ_a r_a† r_a = K. The jump operator adds (Δ − dΔ²/4) LρL†, and Tr K = 1. Trace preservation follows from the trace of the expansion.
2. **Error map.** Write E_L − ℒ²/2 = Φ₁ − ℒ²/2 with Φ₁(ρ) = ¼(Tr(ρK) I − d LρL†). The Kraus operators |i⟩ r_a of Tr(ρK) I, rotated by a unitary on the index (i, a) that takes the unit vector δ_{ia}/√d to the first basis vector, contain L/√d, so Tr(ρK) I − LρL†/d is completely positive. Hence Φ₁ is the difference of the completely positive maps ¼(Tr(ρK) I − LρL†/d) and ¼(d − 1/d) LρL†, both with adjoint value ¼(d − 1/d) K at the identity, and ½‖Φ₁‖⋄ ≤ (d − 1/d)‖K‖/4. Also ‖ℒ‖⋄ ≤ 2‖K‖.
3. **Steps.** ½‖Λ_Δ(· ⊗ π_L) − e^{Δℒ}‖⋄ ≤ Δ² e_L + ½ Σ_{j≥3} (2Δ)^j/j!, and the errors of the n steps add. With n ≥ 2t the remainder is at most (2e/3) t³/n², which is at most 2tε/n when n ≥ (d/4 + 1)t²/ε; and ε ≤ t gives n ≥ dt/4. ∎

The constant d/4 + 1 is half of the constant d/2 + e^{1/d} of Theorem 2 for WML, and with Theorem 7 the optimal leading constant for every protocol lies between (d−1)/4 and d/4 + 1 in the regime where both apply: t ≤ c and ε ≤ min{t, t²/(C′ d log(2d/t))}. On the step itself the leading constant is attained at L = |0⟩⟨0| with input |0⟩⟨0|, where E_L(|0⟩⟨0|) = ¼(I − d|0⟩⟨0|) has trace distance (d−1)/4 from 0 and ℒ² vanishes. Numerically, sup_L e_L = (d−1)/4 exactly: a cutting-plane search over L with an exact semidefinite program for the diamond norm gives 0.25000, 0.50000 and 0.75000 for d = 2, 3, 4, and structured and random operators give at most 1.00000 for d = 5. At leading order and for d = 2, 3, the minimax over all covariant one-copy steps with the forced first-order term is also (d−1)/4.

## Scope

- Theorems 1 and 3 are exact statements about explicit operators, checked numerically with plain-state certificates and with diamond norms from a semidefinite program.
- Theorems 2, 4, 5, 6, 7, 8 and 9 are written proofs (Claim). The Kraus form of Theorem 9 is checked exactly for d = 2 to 5, and its n-step error against the matrix exponential for d = 2, 3; the value sup_L e_L = (d−1)/4 is numerical only. The constant K_d of Theorem 5 and the absolute constants of Theorems 6 and 7 are not optimized. For Theorem 8, the program convention, the coherence bound |q| ≥ csγ for t from 0.01 to 12, and the positivity and trace of the dual certificate for (d, n) up to (3, 4), (4, 3), (5, 2) and (6, 2) are checked numerically. For Theorem 7, the spin decomposition, the trace-norm tail and the degree of each spin part are checked numerically. Every coefficient identity of Theorem 2 is checked against the matrix exponential to 1e-12, and the Schur-complement value of Theorem 4 is checked exactly for d = 2, 3, 4 with one copy per step and for (d, k) = (2, 2), (3, 2), (4, 2), (2, 3), (3, 3).
- Lean (`lean/`, standard axioms only, listed in `lean/axioms.txt`). The library `WmlCoefficients` checks the scalar steps of Theorem 2: 0 < φ ≤ 1/2 and φ antitone on (0, ∞), φ(1/2) > 1/3, the bounds 0 < c_A, c_D ≤ dΔ²/4 and 0 < −c_J ≤ dΔ²/2, the tail e^x − 1 − x ≤ x² e^x/2, and their sum at most Δ² κ (d/2 + e^{1/d} κ) for d ≥ 2, Δ ≤ 1/(2d) and κ = ‖L‖∞² ∈ (0, 1]; the diamond-norm bounds on J, A and D₁∘J and the series bound on the tail are not formalized. The library `ConjugationBound` checks the scalar steps of Theorem 8: the dimension identities D_{k+1}(k+1) = D_k(k+d−1) and 1/D_k − 1/D_{k+1} = (d−2)/(D_k(k+d−1)) for D_k = dim Sym^k(C^{d−1}), the binomial mean Σ k b_k = n s², positivity of the 2 × 2 blocks, the trace n s²/(λ(d−2)) of the certificate, step 5, and the constants of the corollary at θ = π/4 (1 − e^{−t} ≥ 0.632 t on [0, 1], hence n ≥ 0.0124 (d−2) t²/ε for ε ≤ 0.079 t). The block decomposition of Ω from the Haar moments and step 2 are not formalized. `step5_satisfiable` gives an instance of the hypotheses of step 5 with a positive right-hand side, and `step5_conclusion_can_fail` shows that its conclusion is not automatic.
- The step of WML is built twice: from the transfer matrix of [1, App. B], and directly from [1, Eq. (15)] on the full system and program space. The two agree to 1e-16 for d = 2, 3.
- The supremum over L for d ≥ 4 is not computed. Over all protocols, Theorem 6 covers t ≤ c/d, and Theorem 7 covers t ≤ c at accuracies ε ≤ t²/(C′ d log(2d/t)). Theorem 8 covers d ≥ 3 at accuracies ε ≤ (1 − e^{−t})/8 for every t, with the factor d − 2.

## Files

- `sim/wml.py`: the WML step from the transfer matrix and from the definition, the leading error map, and the diamond-norm semidefinite program.
- `sim/check_gap.py`, `sim/nstep.py`: Theorem 1, one step and n steps, with asserts (`check_gap.py --brute` adds the step from the definition at d = 5, about 8 GB).
- `sim/check_bound.py`: Theorem 2 against exact diamond norms on random and structured L.
- `sim/projector.py`: Theorem 3.
- `sim/class_bound.py`: the forced leak of Theorem 4 with one copy per step, from the full Choi matrices, with asserts for d = 2, 3, 4.
- `sim/kcopies.py`: the forced leak with k copies per step, (d−1)/(4k), and its attainment by k WML steps, with asserts for (d, k) up to (4, 2) and (3, 3).
- `sim/scan.py`, `sim/supL.py`: rank-one scan and the numerical supremum over L.
- `sim/opt.py`, `sim/opt2.py`: the optimal channel with n copies over all channels, as an exact semidefinite program on covariant Choi matrices (partially transposed permutation operators, block-diagonalized for n = 2); `sim/check_conv.py` checks its conventions against the full WML channel; `sim/frame_check.py` gives the numbers after Theorem 5.
- `sim/thm6_check.py`: the derivative identities, the trigonometric degree and the test vectors of Theorem 6, and the 2 × 2 bound on the collective WML channel, with asserts.
- `sim/thm7_check.py`: the spin decomposition of Theorem 7 (Hilbert-Schmidt norms exactly for n ≤ 100, trace-norm tails beyond k₀ for n ≤ 2000) and the degree 2k of each spin part under a random channel, with asserts.
- `sim/thm8_check.py`: the program convention, the target coherence and the dual certificate of Theorem 8, with asserts.
- `sim/step_kraus.py`, `sim/step_check.py`: the Kraus operators of Theorem 9, its exact expansion, the bound on e_L, and the n-step error, with asserts.
- `lean/WmlCoefficients/Basic.lean`, `lean/ConjugationBound/Basic.lean`: the Lean proofs of the scalar steps of Theorems 2 and 8; `lean/Axioms.lean` prints the axioms of each theorem.

## References

1. S. Park, Y. Seo, B. Go, D. Patel, M. M. Wilde, H. Kwon. Improved sample complexity bound for sample-based Lindbladian simulation. arXiv:2605.30301 (2026).
2. B. Go, H. Kwon, S. Park, D. Patel, M. M. Wilde. Sample-based Hamiltonian and Lindbladian simulation: non-asymptotic analysis of sample complexity. arXiv:2412.02134.
3. D. Bruß, C. Macchiavello. Optimal state estimation for d-dimensional quantum systems. Phys. Lett. A 253, 249 (1999).

## Use of AI

The constructions, checks and text were produced with Claude Opus 5.5.
