# Nonadaptive learning of the ternary family: the exact exponential base is (3 − u)/2 per signal qubit

Written 10 Nov 2026.

## Problem

In the ternary family of [1], a label a ∈ {X, Y, Z}^L selects the state

ρ_{a,c} = τ_a ⊗ 2^{−L}(I + cP_a)

on L marker and L signal qubits. Each marker qubit is in τ_X = (I − uZ)/2, τ_Y = I/2 or τ_Z = (I + uZ)/2, with 0 < u < 1/2. The string P_a is the tensor product of the letters of a. The task is to estimate c near 0 from N copies, measured one copy at a time. All constants below are local minimax constants at c = 0, over a shrinking window |c| ≤ w_N = N^{−1/2+ε} and the worst label, as in [1]; schedules randomised in advance are allowed.

[1, Theorem V.1] shows that the adaptive local asymptotic minimax MSE constant is 1. For the nonadaptive constant N R_NA (arbitrary global single-copy measurements, fixed in advance), [1] shows

1/B_L ≤ lim inf N R_NA ≤ lim sup N R_NA ≤ 2^L + 1,  with B_L = (2^L − 1)(1 + u)^L / 3^L.

The two bounds are exponential with bases 3/(2(1 + u)) and 2 per signal qubit. [1] states that "closing it would determine the exact base of the exponential".

## Result

Write q = 2/(3 − u).

**Theorem 1.** For every L ≥ 1 and 0 < u < 1/2,

max{1/B_L, ((3 − u)/2)^L} ≤ lim inf N R_NA ≤ lim sup N R_NA ≤ 2((3 − u)/2)^L.

So the nonadaptive constant is ((3 − u)/2)^L up to a factor at most 2. Its exact base per signal qubit is (3 − u)/2, which lies strictly between the two bases of [1]. The ratio of the nonadaptive to the adaptive constant is Θ(((3 − u)/2)^L).

**Proposition 2.** For L = 1 the nonadaptive constant is exactly (3 + u)/(1 + u).

The proof of the finite-sample bound [1, Theorem V.10] also gives N ≥ 1/(144 q^L ε²), so the number of copies is at least max{1/(144 B_L ε²), 1/(144 q^L ε²)}, which is exponentially larger for large L.

## Proof

**Measurements.** All marker states are diagonal in the Z basis. So replacing each element E_y of a measurement by its diagonal blocks Σ_z |z⟩⟨z| ⊗ ⟨z|E_y|z⟩ leaves every outcome distribution of the family unchanged. Recording z as well can only increase the information. Here the information of a measurement with outcome probabilities p_y(c) is I = Σ_y (∂_c p_y)²/p_y at c = 0, the variance of the score. Hence we may assume the measurement reads the marker string z ∈ {±1}^L and then measures the signal with a measurement F^z = {F^z_y} that depends on z. This gives

I_M(a; 0) ≤ Σ_z p(z|a) I_{F^z}(a),  p(z|a) = Π_l p(z_l|a_l),

where p(+1|X) = (1 − u)/2, p(+1|Y) = 1/2 and p(+1|Z) = (1 + u)/2.

With d = 2^L, the signal measurement gives I_F(a) = Σ_y tr(F_y P_a)² / (d tr F_y). Split every F_y into rank-one pieces f|φ⟩⟨φ|. Since (Σ x_k)²/Σ y_k ≤ Σ x_k²/y_k for positive y_k, the splitting does not decrease this, and a piece contributes (f/d)⟨φ|P_a|φ⟩². The weights f/d of all pieces sum to 1. Hence, for any weights λ ≥ 0,

Σ_a λ_a I_F(a) ≤ max over pure states φ of Σ_a λ_a ⟨φ|P_a|φ⟩².  (1)

**Lemma 3 (weighted correlations).** Let φ be a pure state of L qubits, and let μ_1, …, μ_L be nonnegative weights on {X, Y, Z}. Write m(μ) for the sum of the two largest values of μ. Then

Σ_{a∈{X,Y,Z}^L} Π_l μ_l(a_l) ⟨φ|P_a|φ⟩² ≤ Π_l m(μ_l).

*Proof.* The left side is linear in each μ_l separately. Each μ_l lies in m(μ_l)Δ, where Δ = {μ ≥ 0 : μ(s) + μ(t) ≤ 1 for all s ≠ t}. The vertices of Δ are 0, the three unit vectors and (1/2, 1/2, 1/2). So it suffices to show that the left side is at most 1 when every μ_l is such a vertex. If some μ_l is 0, the left side is 0.

Otherwise let A be the sites carrying a unit vector, with Q the resulting fixed string on A, and B the sites carrying (1/2, 1/2, 1/2). Put σ = tr_A((Q ⊗ I)|φ⟩⟨φ|). This is a self-adjoint operator on B, by cyclicity of the partial trace over A. Then:
- ⟨φ|Q ⊗ R|φ⟩ = tr(σR) for every string R on B;
- summing over all 4^{|B|} strings R gives Σ_R tr(σR)² = 2^{|B|} tr σ²;
- tr σ² ≤ ‖σ‖_1² ≤ ‖(Q ⊗ I)|φ⟩⟨φ|‖_1² = 1, since the partial trace does not increase the trace norm.

The left side is 2^{−|B|} Σ_{R∈{X,Y,Z}^B} tr(σR)², a sub-sum of nonnegative terms, so it is at most 2^{−|B|} · 2^{|B|} tr σ² ≤ 1. ∎

**Lemma 4 (weighted budget).** Let π(a) = Π_l π_1(a_l) with π_1(X) = π_1(Z) = 1/(3 − u) and π_1(Y) = (1 − u)/(3 − u). Then every global single-copy measurement M satisfies

Σ_a π(a) I_M(a; 0) ≤ q^L.

*Proof.* By the first paragraph and (1), the left side is at most Σ_z max_φ Σ_a π(a) p(z|a) ⟨φ|P_a|φ⟩². The weights factor over sites as μ_l = π_1(·) p(z_l|·). For z_l = +1 these are:
- (1 − u)/(2(3 − u)) for X;
- (1 − u)/(2(3 − u)) for Y;
- (1 + u)/(2(3 − u)) for Z.

So m(μ_l) = 1/(3 − u), and the same holds for z_l = −1. By Lemma 3 the sum over z is at most Π_l (2/(3 − u)) = q^L. ∎

**Lower bound.** In the proof of [1, Lemma C.5], average over the labels with weights π instead of uniformly. With Lemma 4 in place of [1, Theorem V.7], this gives a label a★, fixed before any data, whose total information at c = 0 is at most N q^L. This also holds for schedules randomised in advance. The rest of the proof of [1, Theorem V.9] (Lemma C.4 and Lemma A.1 there) is unchanged and gives lim inf N R_NA ≥ q^{−L}. The bound 1/B_L of [1] holds as well.

**Upper bound.** Every copy is measured with the same measurement M*:
1. Read the marker string z.
2. For each site independently, choose a pair S_l of letters. With probability 1 − r, S_l omits the letter that z_l disfavours (X if z_l = +1, Z if z_l = −1). With probability r = (1 − u)/(3 − u), S_l = {X, Z}.
3. Apply single-qubit stabilizer gates C_l mapping S_l to {X, Y} up to sign: the identity for {X, Y}, the sign transform (Z ↦ X, Y ↦ −Y) for {Y, Z}, and the rotation by π/2 about X (Z ↦ ±Y) for {X, Z}.
4. Measure in the cat basis (|x⟩ ± e^{iπ/4}|x̄⟩)/√2, where x̄ is the complement of x.

Every string in {X, Y}^L maps |x⟩ to a multiple of |x̄⟩, by a phase in {±1, ±i}. So its expectation in each basis state has absolute value 1/√2. Hence every label a with a_l ∈ S_l for all l has ⟨P_a⟩² = 1/2 in every outcome state.

For each letter, the probability that it lies in S_l is
- (1 + u)/2 + ((1 − u)/2) r = q for Z, and likewise for X;
- 1 − r = q for Y.

So the event "a_l ∈ S_l for all l" has probability exactly q^L for every label.

*Estimator.* First estimate the label â from all marker outcomes, as in the proof of [1, Proposition V.11]; the error probability is at most 2L e^{−Nu²/8}. On each copy put T(a) = 2 · 1[a_l ∈ S_l ∀l] · g_y(a) / q^L, where g_y(a) = ⟨ψ_y|P_a|ψ_y⟩ for the outcome state ψ_y, and output the mean of the T(â), clipped to [−1, 1].
- Given inclusion, the outcome y has probability (1 + c g_y(a))/d and g_y(a)² = 1/2. So E[g_y(a)] = c/2 and E T = c.
- Similarly E T² = 4 q^L (1/2)/q^{2L} = 2/q^L.

Here the marker outcomes also choose the signal measurement, so they are not independent of the T values. Compare instead with the clipped mean c̃ of the T(a) for the true label a, which are independent with mean c and variance 2q^{−L} − c². The two estimates agree unless â ≠ a, so the mean squared error is at most (2q^{−L} − c²)/N + 4 · 2L e^{−Nu²/8}. Hence sup_{|c| ≤ w_N} N · MSE ≤ 2q^{−L} + o(1), which gives the upper bound. Check 2 confirms, for L ≤ 3, that M* gives every label the same information, at least q^L/2. ∎

**Proposition 2 (L = 1).**
- *Strategy.* For z = +1, measure Z with probability 2/(3 + u) and Y otherwise. For z = −1, measure X with probability 2/(3 + u) and Y otherwise. Every label then has information (1 + u)/(3 + u).
- *Matching budget.* For L = 1, the maximum in (1) is the largest weight. With weights (s, 1 − 2s, s) and s = 1/(3 + u), the bound Σ_z max_a π(a) p(z|a) equals (1 + u)/(3 + u). The weighted chain of the lower bound, with these weights, gives the constant at least (3 + u)/(1 + u).
- *Estimator.* On each copy put T = 1[measured letter = â] · (±1)/p with p = (1 + u)/(3 + u) the probability that the letter of the label is measured. Then E T = c and E T² = 1/p, and the comparison with the true label, as above, attains (3 + u)/(1 + u). ∎

## Remarks

- At u → 0 the base (3 − u)/2 and the lower base 3/(2(1 + u)) of [1] meet at 3/2. For u > 0 the marker helps the nonadaptive learner less than the bound of [1] allows. With probability r the measurement drops the letter Y, even though the marker does not disfavour it, because this keeps all three letters equally covered.
- The factor 2 is the gap between Lemma 3 and the information of M*. Direct maximisation of the weighted budget for L ≤ 4 suggests that most of it lies in Lemma 3, which is not tight away from the vertex (1/2, 1/2, 1/2); a sharper Lemma 3 would narrow the factor.
- For even L, M* gives more than q^L/2 (check 2), because labels with no letter covered map to ±Z^{⊗L}, which the cat states also stabilise. For odd L the information is exactly q^L/2.
- Lemma 3 is a weighted bound on full-weight correlations. With all weights 1 it gives the bound 2^L, which matches the purity bound up to the identity term.

## Check

`sim/check.py` (about 5 seconds) checks:
- Lemma 3 for random states and weights and at all vertices, for L ≤ 4;
- the information of M* for L ≤ 3;
- Lemma 4 for random global measurements on marker and signal, for L ≤ 2;
- the L = 1 values;
- a table of the bounds.

The output is in `sim/out.txt`.

## References

1. A. Goldar, Z. Qin, Z. Zhu, Z.-X. Gong, M. B. Wakin. Adaptive Local Measurements For Quantum Learning Can Exponentially Outperform Nonadaptive Global Measurements. arXiv:2610.38922 (2026).
