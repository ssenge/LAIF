# Simulating adaptive messages without adaptivity: the cost Θ(d log(1/ε)) is tight for d ≥ 3

Written 11 Nov 2026.

## Problem

In an adaptive protocol, Alice measures her part of a shared entangled state and sends the outcome a ∈ [d] to Bob, who chooses his measurement according to a. In a non-adaptive protocol, Bob's measurement does not depend on the message. Reference [1] shows the following.
- A ternary adaptive message can beat any number M of non-adaptive messages. The example is an exclusion task: Alice gets M of the 3R pairs (j, a), and Bob must output a pair not among them, with R = M² + 1.
- Every adaptive protocol with d messages can be simulated non-adaptively, within worst-case total-variation error ε, with

  M_ε ≤ 1 + ⌈ln(1/ε)/(ln d − ln(d − 1))⌉ ≤ 1 + ⌈d ln(1/ε)⌉ messages [1, Eq. (11)].

It then states: "Whether this scaling is tight remains open."

## Result

**Theorem.** For every d ≥ 3 and every ε < 1/480, there is an adaptive protocol with d messages whose non-adaptive simulation cost satisfies

M_ε ≥ (1/2)⌊d/3⌋ (ln(1/(2ε))/ln(240e) − 1),

and for d = 3 also M_ε ≥ ⌊ln(1/ε)/ln(240e)⌋ + 1. Together with [1, Eq. (11)], the worst case over adaptive protocols is therefore Θ(d log(1/ε)) as ε → 0, for every d ≥ 3. So for d ≥ 3 the scaling in both ε and d is tight up to a constant factor. In these protocols Bob has no input. The protocol depends on ε, as it must: by [1, Eq. (9)], a protocol with a fixed finite entanglement dimension has bounded cost for every ε, so Θ(d log(1/ε)) is a worst case over a family of protocols.

Two changes to the construction of [1] give this:
1. **Three uniformly random bases of C^R with R = 80M**, instead of mutually unbiased bases with R = M² + 1, support the exclusion measurement of [1] for every input S, for some choice of the bases (a random choice works with positive probability). A ground set of size linear in M turns the error of M classical messages into e^{−O(M)}. With R = M² + 1 the same argument gives only Ω(log(1/ε)/log log(1/ε)).
2. **A label.** For d = 3k, Alice also gets a label z ∈ [k] and Bob must output it with his pair. This multiplies the classical cost by about k/2.

## Proofs

**Exclusion with random bases.** Let U₁ = 1 and let U₂, U₃ be independent uniformly random unitaries in dimension R. Write W_{kl} = U_k†U_l. For an input S (M pairs (j, a)), the matrix of inner products G of the M chosen vectors has identity diagonal blocks and off-diagonal blocks G_{kl}, which are submatrices of W_{kl}. Reference [1] (Eqs. (4) to (7)) writes G = C₁ + C₂ + C₃ and defines the measurement A_a = T G⁻¹C_a G⁻¹T† + (1 − P)/3, which satisfies A_a u_{j|a} = 0 for (j, a) ∈ S. Here C_a has zero block row and column a, and its other two diagonal blocks are halves of identities. It works as soon as every ‖G_{kl}‖ < 1/2: then each C_a is positive semidefinite, and G is positive definite, because a common null vector of C₁, C₂, C₃ would vanish on every block. So it suffices that

(†) every submatrix W_{kl}[A, B] with |A| + |B| ≤ M has norm < 1/2, for the three pairs k < l.

*Lemma.* For R = 80M, (†) holds with positive probability.

*Proof.* Each W_{kl} is uniformly random. Fix A, B with |A| + |B| = M; larger submatrices have larger norm, so these are enough. Take nets of mesh η = 0.1 on the unit spheres of C^A and C^B, of sizes at most (1 + 2/η)^{2|A|} and (1 + 2/η)^{2|B|}; then ‖X‖ ≤ (1 − 2η)⁻¹ max |⟨y, Xx⟩| over the nets. For fixed unit x and y, Wx is uniform on the unit sphere and P(|⟨y, Wx⟩| ≥ u) = (1 − u²)^{R−1}. With u = (1 − 2η)/2 = 0.4, this gives P(‖W[A, B]‖ ≥ 1/2) ≤ 21^{2M} · 0.84^{R−1}. There are Σ_a C(R, a)C(R, M − a) = C(2R, M) ≤ (2eR/M)^M pairs (A, B) with |A| + |B| = M. With three pairs (k, l), the failure probability is at most 3 · 0.84⁻¹ · (2e · 80 · 441 · 0.84^{80})^M ≤ 3.6 · 0.168^M < 1. ∎

**Lower bound for d = 3.** Since Bob has no input, a non-adaptive protocol is a classical protocol with shared randomness [1]. Fix the shared randomness, and absorb Bob's private randomness into it. Bob's output is then a function of the message, so he can produce at most M' outputs. Let B be the set of those outputs that are pairs of the ground set (any other output is a failure). If B ⊆ S, the input S fails with certainty. For S uniform among the M-subsets of the 3R pairs and |B| ≤ M' ≤ M, P(B ⊆ S) ≥ 1/C(3R, M). The adaptive protocol never outputs a pair of S, so the total-variation error at S is at least the probability of failure, and

max_S error ≥ E_S error ≥ 1/C(3R, M).

So ε < 1/C(240M, M) forces M_ε ≥ M + 1. Since C(240M, M) < (240e)^M, every M ≤ ln(1/ε)/ln(240e) qualifies.

**Lower bound for d = 3k.** Alice's input is (S, z) with z ∈ [k]. She sends (a, z), and Bob outputs (b, z) with b measured in basis a. This is an adaptive protocol with 3k messages that never fails. In a classical protocol with M' ≤ kM/2 messages and fixed randomness, let B^{(z)} be the set of pairs that Bob can output with label z (an output with a wrong label, or outside the ground set, is a failure). Their sizes add up to at most M', so at least k/2 labels have |B^{(z)}| ≤ M. For such z, the input (S, z) fails whenever B^{(z)} ⊆ S, with probability at least 1/C(3R, M) over S. Averaging over z and S gives error at least 1/(2C(3R, M)). So ε < 1/(2C(240M, M)) forces M_ε > kM/2. The largest such M is at least ln(1/(2ε))/ln(240e) − 1, and it is at least 1 when ε < 1/480. For d not divisible by 3, use k = ⌊d/3⌋ and leave the other messages unused. ∎

For d = 2 the decomposition is impossible, since it would force G₁₂ = 0. The case d = 2 is not covered here.

## Numbers

Lower bounds from the exact binomials in the proofs (slightly stronger than the closed formulas) against the upper bound 1 + ⌈ln(1/ε)/ln(d/(d − 1))⌉ of [1]:

| ε | d = 3 | d = 30 |
|---|---|---|
| 10⁻⁶ | 3 ≤ M_ε ≤ 36 | 11 ≤ M_ε ≤ 409 |
| 10⁻¹² | 5 ≤ M_ε ≤ 70 | 21 ≤ M_ε ≤ 817 |
| 10⁻³⁰ | 11 ≤ M_ε ≤ 172 | 51 ≤ M_ε ≤ 2039 |
| 10⁻¹⁰⁰ | 36 ≤ M_ε ≤ 569 | 176 ≤ M_ε ≤ 6793 |

For d = 3 the gap of about 16 comes mostly from R = 80M, which is not optimized. For d = 30 the factors ⌊d/3⌋/d and 1/2 of the labelled task add about 6.

## Check

`python sim/check.py` (a few seconds, numpy and scipy) checks:
- the union-bound arithmetic;
- the exclusion measurement built from random bases: positivity, completeness and exclusion, on random inputs at R = 80M for M = 2, 3, 4;
- the table above.

The output is in `sim/out.txt`.

## References

1. A. Tavakoli. Unbounded advantage of adaptivity in entanglement-assisted communication. arXiv:2611.11333 (2026).
