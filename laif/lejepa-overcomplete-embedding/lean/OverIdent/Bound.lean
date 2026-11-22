import Mathlib

/-!
# LeJEPA with an over-complete embedding: the alignment bound

Two views with mutual information `I` (in nats) are embedded by the same encoder into `ℝ^M`; `Ixy` is the mutual
information of the two embeddings and `L = E ‖h(x') - h(x)‖²` the alignment loss.
* `align_lower` (Theorem 1): from data processing and the rate distortion function of `N(0, I_M)`,
  `L ≥ M exp(-2 I / M)`;
* `align_lower_gauss`: in the normal world, `I = (N/2) log 1/(1 - ρ²)` gives `L ≥ M (1 - ρ²)^{N/M}`;
* `align_lower_hermite`: per-coordinate correlations at most `ρ` give `L ≥ 2 M (1 - ρ)`;
* `kl_lower`, `kl_lower_gauss` (Theorem 4): the relative entropy bound for near-normal embeddings.
The information-theoretic inputs are classical and enter as the hypotheses `DataProcessing`, `GaussianRD` and
`ShannonLower`.
-/

open Real

namespace OverIdent

/-- Data processing inequality (T. M. Cover and J. A. Thomas, Elements of Information Theory, 2nd ed.,
Theorem 2.8.1): the embeddings `h(x), h(x')` are functions of the views, so their mutual information `Ixy` is at most
the mutual information `I` of the views. -/
def DataProcessing (Ixy I : ℝ) : Prop := Ixy ≤ I

/-- Rate distortion function of `N(0, I_M)` under squared error (Cover and Thomas, Theorem 10.3.3, with equal
variances): a pair `(X, Y)` with `X ∼ N(0, I_M)` and total distortion `E ‖X - Y‖² = L ≤ M` (distortion `L / M` per
coordinate) has mutual information at least `(M/2) log (M / L)`. -/
def GaussianRD (M : ℕ) (Ixy L : ℝ) : Prop := L ≤ M → (M / 2) * log (M / L) ≤ Ixy

/-- Lower bound on mutual information from the maximum entropy bound, for a law with density, second moment `M`
and relative entropy `K` with respect to `N(0, I_M)` (Cover and Thomas, Theorem 8.6.5):
`Ixy ≥ (M/2) log (M / L) - K`. -/
def ShannonLower (M : ℕ) (Ixy L K : ℝ) : Prop := (M / 2) * log (M / L) - K ≤ Ixy

/-- **Theorem 1.** `L ≥ M exp(-2 I / M)` for an exactly normal embedding. -/
theorem align_lower {M : ℕ} (hM : 0 < M) {Ixy I L : ℝ} (hL : 0 < L) (hI : 0 ≤ I)
    (hdp : DataProcessing Ixy I) (hrd : GaussianRD M Ixy L) : M * exp (-2 * I / M) ≤ L := by
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM
  by_cases hLM : L ≤ M
  · have h1 : (M / 2) * log (M / L) ≤ I := (hrd hLM).trans hdp
    have h2 : log (M / L) ≤ 2 * I / M := by
      rw [le_div_iff₀ hM']; nlinarith
    have h3 : M / L ≤ exp (2 * I / M) := by
      rwa [← log_le_iff_le_exp (div_pos hM' hL)]
    have h4 : M ≤ exp (2 * I / M) * L := by rwa [div_le_iff₀ hL] at h3
    have h5 : exp (-2 * I / M) * exp (2 * I / M) = 1 := by
      rw [← exp_add]; ring_nf; exact exp_zero
    calc M * exp (-2 * I / M) ≤ exp (2 * I / M) * L * exp (-2 * I / M) :=
          mul_le_mul_of_nonneg_right h4 (exp_pos _).le
      _ = L * (exp (-2 * I / M) * exp (2 * I / M)) := by ring
      _ = L := by rw [h5, mul_one]
  · have : exp (-2 * I / M) ≤ 1 := by
      rw [exp_le_one_iff]; exact div_nonpos_of_nonpos_of_nonneg (by linarith) hM'.le
    nlinarith [not_le.1 hLM]

/-- In the normal world `M exp(-2 I / M) = M (1 - ρ²)^{N/M}` for `I = (N/2) log 1/(1 - ρ²)`. -/
lemma exp_gauss {M N : ℕ} (hM : 0 < M) {ρ : ℝ} (h0 : 0 ≤ ρ) (h1 : ρ < 1) :
    exp (-2 * ((N / 2) * log (1 / (1 - ρ ^ 2))) / M) = (1 - ρ ^ 2) ^ ((N : ℝ) / M) := by
  have hp : 0 < 1 - ρ ^ 2 := by nlinarith
  rw [rpow_def_of_pos hp, one_div, log_inv]
  congr 1; field_simp

/-- Theorem 1 in the normal world: `L ≥ M (1 - ρ²)^{N/M}`. -/
theorem align_lower_gauss {M N : ℕ} (hM : 0 < M) {ρ Ixy L : ℝ} (h0 : 0 ≤ ρ) (h1 : ρ < 1) (hL : 0 < L)
    (hdp : DataProcessing Ixy ((N / 2) * log (1 / (1 - ρ ^ 2)))) (hrd : GaussianRD M Ixy L) :
    M * (1 - ρ ^ 2) ^ ((N : ℝ) / M) ≤ L := by
  have hp : 0 < 1 - ρ ^ 2 := by nlinarith
  have hI : 0 ≤ (N / 2 : ℝ) * log (1 / (1 - ρ ^ 2)) := by
    refine mul_nonneg (by positivity) (log_nonneg ?_)
    rw [le_div_iff₀ hp]; nlinarith
  rw [← exp_gauss hM h0 h1]; exact align_lower hM hL hI hdp hrd

/-- The second term of Theorem 1: if every coordinate has variance 1 and correlation at most `ρ` across the views
(by the expansion in orthogonal polynomials of the normal density, `E[f(z) f(z')] ≤ ρ Var f`), then `L = 2M - 2 Σ cᵢ ≥ 2M(1 - ρ)`. -/
theorem align_lower_hermite {M : ℕ} {ρ L : ℝ} (c : Fin M → ℝ) (hc : ∀ i, c i ≤ ρ)
    (hL : L = 2 * M - 2 * ∑ i, c i) : 2 * M * (1 - ρ) ≤ L := by
  have : ∑ i, c i ≤ M * ρ := by
    calc ∑ i, c i ≤ ∑ _i : Fin M, ρ := Finset.sum_le_sum fun i _ => hc i
      _ = M * ρ := by simp
  rw [hL]; linarith

/-- **Theorem 4.** `K ≥ (M/2) log (M / L) - I`. -/
theorem kl_lower {M : ℕ} {Ixy I L K : ℝ} (hdp : DataProcessing Ixy I) (hsl : ShannonLower M Ixy L K) :
    (M / 2) * log (M / L) - I ≤ K := by
  unfold DataProcessing at hdp; unfold ShannonLower at hsl; linarith

/-- Theorem 4 in the normal world: matched-level alignment `L ≤ c N (1 - ρ)` forces
`K ≥ ((M - N)/2) log 1/(1 - ρ) - (M/2) log (c N / M)`. -/
theorem kl_lower_gauss {M N : ℕ} (hM : 0 < M) (hN : 0 < N) {ρ c Ixy L K : ℝ} (h0 : 0 ≤ ρ) (h1 : ρ < 1)
    (hc : 0 < c) (hL : 0 < L) (hLc : L ≤ c * N * (1 - ρ))
    (hdp : DataProcessing Ixy ((N / 2) * log (1 / (1 - ρ ^ 2)))) (hsl : ShannonLower M Ixy L K) :
    ((M : ℝ) - N) / 2 * log (1 / (1 - ρ)) - (M / 2) * log (c * N / M) ≤ K := by
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hr : 0 < 1 - ρ := by linarith
  have hp : 0 < 1 - ρ ^ 2 := by nlinarith
  have hk := kl_lower hdp hsl
  -- log (M / L) ≥ log (M / (c N)) + log 1/(1 - ρ)
  have hA : log (M / (c * N)) + log (1 / (1 - ρ)) ≤ log (M / L) := by
    rw [← log_mul (by positivity) (by positivity)]
    refine log_le_log (by positivity) ?_
    rw [div_mul_div_comm, mul_one, div_le_div_iff₀ (by positivity) hL]
    nlinarith
  -- log 1/(1 - ρ²) ≤ log 1/(1 - ρ)
  have hB : log (1 / (1 - ρ ^ 2)) ≤ log (1 / (1 - ρ)) := by
    refine log_le_log (by positivity) ?_
    rw [div_le_div_iff₀ hp hr]; nlinarith
  have hC : log (c * N / M) = -log (M / (c * N)) := by
    rw [← log_inv, inv_div]
  rw [hC]
  have := mul_le_mul_of_nonneg_left hA (by positivity : (0 : ℝ) ≤ M / 2)
  have := mul_le_mul_of_nonneg_left hB (by positivity : (0 : ℝ) ≤ N / 2)
  nlinarith

end OverIdent
