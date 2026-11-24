# Tolerant Fourier dimensionality testing with the square-root saving

Written 22 Nov 2026.

**Setting.** As in [1]: f : F₂ⁿ → {−1, 1} is given by a quantum query oracle, and f has Fourier dimension at most k when the strings with nonzero Fourier coefficient span a subspace of dimension at most k. For 0 ≤ α < 1/2 and 0 < ε < 1/2, a tolerant tester accepts with probability at least 2/3 when f is within distance αε of some function of Fourier dimension at most k, and rejects with probability at least 2/3 when f is at distance at least ε from all of them. Write x = 1 − 2α.

| | Problem | Previous best bound | This folder | Status |
|---|---|---|---|---|
| Thm 1 | Tolerant testing, quantum queries | O(k/(ε x²) · log(1/(ε x))) [1, Thm 5.1]; O(k/√ε) for standard testing (α = 0) and Ω(k) [1] | O(k(1 + αk)/(x² √ε) · log(e(1 + αk)/x) + k log(k + 1)/√ε) | Claim; tester logic checked by classical simulation (n = 5, k ≤ 2) |

So the square-root saving in ε holds for α ≤ 1/k, where the bound is O(k log(e(k + 1)/x)/(x²√ε)), and O(k log(k + 1)/√ε) for k ≥ 3. Theorem 1 is smaller than the bound of [1, Thm 5.1] when (1 + αk) log(e(1 + αk)/x) + x² log(k + 1) is below about log(1/(εx))/√ε, so when 1 + αk is below about 1/√ε up to logarithmic factors. For every constant α, Theorem 1 has the dependence 1/√ε on ε, at a cost quadratic in k. For constant α and k ≳ 1/√ε the bound of [1] stays the better one, and a bound of order k/√ε for constant α is open, in the sense of the question at the end of Section 5 of [1].

## Facts from [1]

Measuring the state Σ_s f̂(s)|s⟩, prepared with one query, gives a sample of the Fourier distribution μ(s) = f̂(s)². For a subspace W write μ(W̄) for the mass outside W.

- (Y) If f is within distance αε of a function g of Fourier dimension at most k and U is the span of the support of ĝ, then μ(Ū) ≤ 4αε [1, Lemma 5.1].
- (N) If f is at distance at least ε from every function of Fourier dimension at most k, then μ(Ū) ≥ 2ε for every subspace U of dimension at most k [1, Cor. 3.1].

## The tester

Let Λ = max(4, 80αk). Both phases use amplitude estimation and amplitude amplification [2] on the state Σ_s f̂(s)|s⟩ with the strings outside the current subspace W marked. Amplitude amplification keeps the relative amplitudes of the marked strings, so a successful run returns an exact sample of μ conditioned on W̄, and success is checked classically. Since the marked mass p is only known to lie in an interval, the samples use randomly chosen iteration counts as in the exponential search of [2], with expected cost O(1/√p) for a lower bound p on the marked mass; capping the total at a constant times its expectation gives the worst-case query count at a small extra failure probability.

**Phase A.** Start with W = {0} and repeat: with amplitude estimation at O(1/√(Λε)) queries (median of O(log(k + 1)) runs), decide whether μ(W̄) ≥ Λε or μ(W̄) < Λε/2 (either answer is allowed in between). If the answer is large, draw a sample s outside W by amplitude amplification, set W ← span(W, s), and reject if dim W > k. If the answer is small, go to phase B.

**Phase B.** Now w = μ(W̄) < Λε. Estimate w by ŵ with |ŵ − w| ≤ (x/8) max(w, ε), using O(1/(x√ε)) queries. Accept if ŵ ≤ (1 + 2α)ε. Otherwise w > (1 + 2α − x/8)ε ≥ 7ε/8; draw m = ⌈C Λ k x^{−2} ln(eΛ/x)⌉ samples of μ conditioned on W̄, each with O(1/√ε) queries, and accept if and only if some subspace V with dim(W + V) ≤ k has at most τ = (1 + 2α)(ε/ŵ)m of the samples outside W + V.

Amplitude amplification is only applied after an estimate has shown, with high probability, μ(W̄) ≥ Λε/2 in phase A or μ(W̄) > 7ε/8 in phase B, so every amplification step runs on a marked mass bounded below. A run that returns a string inside W is repeated; phase A allows O(log(k + 1)) capped runs per round, and phase B caps the total at O(m) runs, which by a tail bound on the number of successes yields m samples with high probability.

## Theorem 1, the proof

**Query count.** Phase A runs at most k + 1 rounds of O(log(k + 1)/√(Λε)) queries. Phase B uses O(1/(x√ε)) queries for the estimate and O(m/√ε) for the samples, with m = O(Λk x^{−2} log(eΛ/x)) and Λ = O(1 + αk).

**Yes case.** Let U be the subspace of (Y), with dim U ≤ k and μ(Ū) ≤ 4αε. Phase A adds a sample only after a certificate μ(W̄) ≥ Λε/2, and as long as W ⊆ U, that sample lies outside U with probability μ(Ū)/μ(W̄) ≤ 8α/Λ ≤ 1/(10k). Phase A adds at most k samples while W ⊆ U, so W ⊆ U at the end with probability at least 9/10, and in particular phase A does not reject. In phase B, if the tester does not accept at once, take V with W + V = U. The number X of samples outside U is binomial with mean at most 4αεm/w. If w ≥ ε, then ŵ ≤ (1 + x/8)w; if 7ε/8 < w < ε, then ŵ ≤ w + xε/8 ≤ (1 + x/7)w. In both cases, with x ≤ 1,

τ − E[X] ≥ (ε/w) m ((1 + 2α)(1 − x/7) − 4α) ≥ (ε/w) m (x − 2x/7) = (5/7) x (ε/w) m,

and the variance of X is at most 4αεm/w. The second-moment inequality bounds the probability that X > τ by (196α/25) · w/(εm x²) ≤ 8αΛ/(m x²), which is small for the chosen m.

**No case.** Phase A rejects correctly if dim W exceeds k. Otherwise dim W ≤ k, so w ≥ 2ε by (N), the estimate exceeds (1 + 2α)ε, and the samples are drawn. Suppose some V with dim(W + V) ≤ k has at most τ samples outside W + V. Replacing V by the span of the samples inside W + V gives a subspace with the same samples outside, spanned by W and a set J of at most k samples. Fix J. Conditioned on the samples in J, the other samples are independent, and each lies outside W + span(J) with probability at least 2ε/w by (N). With ŵ ≥ (1 − x/8)w (here w ≥ 2ε) and m ≥ 16k/x, the threshold satisfies τ ≤ (1 − x/4) E[Y] for the number Y of the other samples outside. The multiplicative lower-tail bound for sums of independent indicators gives probability at most exp(−(x²/32)(2ε/w)(m − k)) ≤ exp(−x²(m − k)/(16Λ)). A union bound over the at most (em/k)^k sets J keeps the total below 1/20 for a suitable constant C.

**Failure probability.** In the yes case the errors are the phase A event of leaving U (at most 1/10), the second-moment bound, the failures of the estimates (at most 1/(100(k + 1)) per round of phase A and a small constant in phase B) and of the capped sampling. In the no case they are the union bound (at most 1/20) and the same estimate and sampling failures. With the constants chosen accordingly, each sum is at most 1/3. ∎

## Scripts

`sim/check_tester.py` runs the tester classically on Fourier distributions over F₂⁵ with k ∈ {1, 2}. Yes instances have a subspace of dimension k with mass at most 4αε outside, and no instances are checked exhaustively to have mass at least 2ε outside every subspace of dimension at most k. Amplitude estimation is replaced by exact values perturbed at random within the stated errors, and amplitude amplification by exact conditional samples. The script checks the acceptance rates on 60 instances of each kind.

```
python sim/check_tester.py
k=1 alpha=0.1 eps=0.02: yes accepted 58/60, no rejected 60/60, cost <= 325 (k/eps scale 323)
k=2 alpha=0.1 eps=0.02: yes accepted 60/60, no rejected 60/60, cost <= 1428 (k/eps scale 646)
k=2 alpha=0.25 eps=0.01: yes accepted 60/60, no rejected 60/60, cost <= 17254 (k/eps scale 4239)
k=2 alpha=0.05 eps=0.005: yes accepted 60/60, no rejected 60/60, cost <= 987 (k/eps scale 2668)
```

The cost column counts queries with the constants of the tester; at these sizes the constant 80 in Λ dominates, and the gain over the k/ε scale appears only for small ε.

## Lean

The library `FourierDim` in `lean/` (Lean 4, toolchain and Mathlib revision pinned in `lean-toolchain` and `lake-manifest.json`) proves, with only the standard axioms (`lean/axioms.txt`):

* `phaseA_ratio`: 4αε/(Λε/2) ≤ 1/(10k) for Λ ≥ 80αk, the phase A step of the yes case.
* `phaseB_mass`: ŵ > (1 + 2α)ε and |ŵ − w| ≤ (x/8) max(w, ε) give w > 7ε/8.
* `est_ratio`, `yes_margin`, `second_moment_eq`, `second_moment_le`: the yes case of phase B, from ŵ ≤ (1 + x/7)w and the margin (5/7)x to the bound 8αΛ/(m x²).
* `no_estimate`, `no_threshold`, `tail_exponent`: the no case, with ŵ > (1 + 2α)ε, τ ≤ (1 − x/4)E[Y] for m x ≥ 16k, and the exponent x²(m − k)/(16Λ).
* `outside_same`: for W ≤ U, a sample lies outside W + span of the samples in U exactly when it lies outside U, the reduction to the sets J.

**Not formalized:** the size bound |J| ≤ k, the tail and second-moment inequalities, the union bound over J, the query count and the failure sum. Amplitude estimation and amplification, and the facts (Y) and (N) of [1], are taken from the literature.

## Use of AI

Claude Opus 5.5 (Anthropic) was used throughout this research: to explore approaches, to develop and check proofs, to write the check scripts, and to draft the text.

## References

1. K. Chen. Exponential quantum advantage in testing Fourier dimensionality. arXiv:2609.25816, 2026.
2. G. Brassard, P. Høyer, M. Mosca, A. Tapp. Quantum amplitude amplification and estimation. Contemporary Mathematics 305, 2002. arXiv:quant-ph/0005055.
