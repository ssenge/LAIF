import LPType.Potential
import LPType.Tree
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.NormNum

/-!
# The expectation part of Theorem 1

The classical skeleton of the algorithm in Section 3 of the notes, as a finite adaptive process.
A round draws a sample `R` for the estimate and then the sample `S`, both from product measures,
with new independent randomness. The quantum searches are taken to be exact here: `R` and `S` have
exactly these laws and "no violator" is decided correctly. The errors of the searches are not modelled.

The process `clarkson` does not redraw, so `S` given `W̃` is independent, as Lemma 1 needs. The
redraw of an earlier version of the notes is treated at the end with `Kernel.conditioned`.

After a stop the process keeps drawing, which does not change the law of the event that it did not
stop within the first `T` rounds.
-/

open Finset

namespace LPType

variable {H R : Type*} [DecidableEq H] [Fintype H] [PartialOrder R]

/-- The state between rounds: for each `h` the number of violated samples, and the last estimate. -/
structure RoundState (H : Type*) where
  /-- The number of earlier samples violated by `h`. -/
  count : H → ℕ
  /-- The previous estimate of the weight. -/
  est : ℝ

namespace RoundState

/-- The weight `w_t(h) = 2^{count}`. -/
noncomputable def w (σ : RoundState H) (h : H) : ℝ := 2 ^ σ.count h

/-- The total weight `W_t`. -/
noncomputable def W (σ : RoundState H) : ℝ := ∑ h, σ.w h

omit [DecidableEq H] [Fintype H] in
theorem w_pos (σ : RoundState H) (h : H) : 0 < σ.w h := pow_pos (by norm_num) _

/-- The state before the first round, for any initial estimate. -/
def init (Z : ℝ) : RoundState H := ⟨fun _ => 0, Z⟩

omit [DecidableEq H] in
@[simp] theorem W_init (Z : ℝ) : (init Z : RoundState H).W = Fintype.card H := by
  simp [W, w, init]

end RoundState

/-- The inclusion probability `min(1, s w_h / Z)`. If `Z = 0`, which happens when the estimate's
sample is empty, the expression of the notes is undefined; the probability is `1` here, reading
everything, which is what `s w_h / Z = ∞` means. -/
noncomputable def inclProb (s : ℝ) (w : H → ℝ) (Z : ℝ) (h : H) : ℝ :=
  if 0 < Z then min 1 (s * w h / Z) else 1

omit [DecidableEq H] [Fintype H] in
theorem inclProb_pos {s Z : ℝ} {w : H → ℝ} (hs : 0 < s) (hw : ∀ h, 0 < w h) (h : H) :
    0 < inclProb s w Z h := by
  unfold inclProb
  split_ifs with hZ
  · exact lt_min one_pos (div_pos (mul_pos hs (hw h)) hZ)
  · exact one_pos

omit [DecidableEq H] [Fintype H] in
theorem inclProb_le_one (s : ℝ) (w : H → ℝ) (Z : ℝ) (h : H) : inclProb s w Z h ≤ 1 := by
  unfold inclProb
  split_ifs
  · exact min_le_left _ _
  · exact le_rfl

omit [DecidableEq H] [Fintype H] in
theorem inclProb_isProb {s Z : ℝ} {w : H → ℝ} (hs : 0 < s) (hw : ∀ h, 0 < w h) :
    IsProb (inclProb s w Z) :=
  fun h => ⟨(inclProb_pos hs hw h).le, inclProb_le_one s w Z h⟩

omit [DecidableEq H] [Fintype H] in
/-- The inequality that Lemma 1 needs, including the case `Z = 0`. -/
theorem inclProb_key {s Z : ℝ} {w : H → ℝ} (hs : 0 < s) (hw : ∀ h, 0 < w h) (hZ : 0 ≤ Z) (h : H) :
    s * w h * (1 - inclProb s w Z h) ≤ Z * inclProb s w Z h := by
  rcases hZ.lt_or_eq with hZ' | rfl
  · refine Problem.key_of_min_le (inclProb_isProb hs hw) (fun i => (hw i).le) hs hZ' (fun i => ?_) h
    simp [inclProb, hZ']
  · simp [inclProb]

omit [DecidableEq H] [Fintype H] in
/-- The inclusion probability is at most `s w_h / Z`, for `Z > 0`. -/
theorem inclProb_le_div {s Z : ℝ} {w : H → ℝ} (hZ : 0 < Z) (h : H) :
    inclProb s w Z h ≤ s * w h / Z := by
  simp only [inclProb, hZ, ite_eq_left]
  exact min_le_right _ _

/-- The estimate `W̃`: half the Horvitz-Thompson sum over the sample `R`. -/
noncomputable def estimate (s' : ℝ) (σ : RoundState H) (R : Finset H) : ℝ :=
  (∑ h ∈ R, σ.w h / inclProb s' σ.w σ.est h) / 2

omit [DecidableEq H] [Fintype H] in
theorem estimate_nonneg {s' : ℝ} (hs' : 0 < s') (σ : RoundState H) (R : Finset H) :
    0 ≤ estimate s' σ R :=
  div_nonneg (sum_nonneg fun h _ =>
    div_nonneg (σ.w_pos h).le (inclProb_pos hs' σ.w_pos h).le) (by norm_num)

/-- `E[W̃ | past] = W_t / 2`, whatever the previous estimate was. -/
theorem expect_estimate {s' : ℝ} (hs' : 0 < s') (σ : RoundState H) :
    prodExp (inclProb s' σ.w σ.est) (estimate s' σ) = σ.W / 2 := by
  have h := prodExp_htSum (p := inclProb s' σ.w σ.est) (inclProb_pos hs' σ.w_pos) σ.w
  have h2 : prodExp (inclProb s' σ.w σ.est) (estimate s' σ)
      = prodExp (inclProb s' σ.w σ.est) (fun R => ∑ h ∈ R, σ.w h / inclProb s' σ.w σ.est h) / 2 := by
    simp only [prodExp, estimate, sum_div, mul_div_assoc]
  rw [h2, h]
  rfl

variable (P : Problem H R)

namespace Problem

open scoped Classical in
/-- **One round of the algorithm**, as a finite adaptive process. A step is the pair `(R, S)`. Given
the state, `R` is drawn with `s'` and the previous estimate; then, given `R`, `S` is drawn with `s`
and `W̃(R)`. Violators of `S` double. -/
noncomputable def clarkson {s s' : ℝ} (hs : 0 < s) (hs' : 0 < s') :
    Kernel (RoundState H) (Finset H × Finset H) where
  weight σ x := prodWeight (inclProb s' σ.w σ.est) x.1 *
    prodWeight (inclProb s σ.w (estimate s' σ x.1)) x.2
  next σ x := ⟨fun h => σ.count h + if P.Violates h x.2 then 1 else 0, estimate s' σ x.1⟩
  weight_nonneg σ x := mul_nonneg
    (prodWeight_nonneg (inclProb_isProb hs' σ.w_pos) _)
    (prodWeight_nonneg (inclProb_isProb hs σ.w_pos) _)
  weight_sum σ := by
    rw [Fintype.sum_prod_type]
    simp only [← mul_sum, prodWeight_sum, mul_one]

variable {s s' : ℝ} (hs : 0 < s) (hs' : 0 < s')

/-- `W_{t+1} = W_t + w_t(V_t)`. -/
theorem clarkson_W_next (σ : RoundState H) (x : Finset H × Finset H) :
    ((P.clarkson hs hs').next σ x).W = σ.W + ∑ h ∈ P.violators x.2, σ.w h := by
  classical
  have h1 : ∀ h, ((P.clarkson hs hs').next σ x).w h
      = σ.w h + if h ∈ P.violators x.2 then σ.w h else 0 := by
    intro h
    by_cases hv : P.Violates h x.2
    · simp [clarkson, RoundState.w, hv, pow_succ, mul_two]
    · simp [clarkson, RoundState.w, hv]
  simp only [RoundState.W, h1, sum_add_distrib, sum_ite_mem, univ_inter]

/-- `E[w_t(V_t) | past] ≤ δ W_t / (2 s)`: Lemma 1 given `W̃`, then `E[W̃ | past] = W_t / 2`. -/
theorem clarkson_expected_violators (σ : RoundState H) :
    ∑ x, (P.clarkson hs hs').weight σ x * ∑ h ∈ P.violators x.2, σ.w h
      ≤ P.combDim / (2 * s) * σ.W := by
  have hR : ∀ R : Finset H,
      prodExp (inclProb s σ.w (estimate s' σ R)) (fun S => ∑ h ∈ P.violators S, σ.w h)
        ≤ P.combDim * estimate s' σ R / s := by
    intro R
    have hZ := estimate_nonneg hs' σ R
    have := P.prodExp_violators_core (s := s) (inclProb_isProb hs σ.w_pos) hZ
      (inclProb_key hs σ.w_pos hZ)
    rw [le_div_iff₀ hs]
    linarith
  have hδ : (0 : ℝ) ≤ P.combDim := Nat.cast_nonneg _
  calc ∑ x, (P.clarkson hs hs').weight σ x * ∑ h ∈ P.violators x.2, σ.w h
      = ∑ R : Finset H, prodWeight (inclProb s' σ.w σ.est) R *
          prodExp (inclProb s σ.w (estimate s' σ R)) (fun S => ∑ h ∈ P.violators S, σ.w h) := by
        rw [Fintype.sum_prod_type]
        refine sum_congr rfl fun R _ => ?_
        rw [prodExp, mul_sum]
        exact sum_congr rfl fun S _ => by simp only [clarkson]; ring
    _ ≤ ∑ R : Finset H, prodWeight (inclProb s' σ.w σ.est) R * (P.combDim * estimate s' σ R / s) :=
        sum_le_sum fun R _ => mul_le_mul_of_nonneg_left (hR R)
          (prodWeight_nonneg (inclProb_isProb hs' σ.w_pos) R)
    _ = P.combDim / s * prodExp (inclProb s' σ.w σ.est) (estimate s' σ) := by
        rw [prodExp, mul_sum]
        exact sum_congr rfl fun R _ => by ring
    _ = P.combDim / (2 * s) * σ.W := by
        rw [expect_estimate hs']
        field_simp

/-- **`E[W_{t+1} | past] ≤ W_t (1 + δ / (2 s))`.** -/
theorem clarkson_step (σ : RoundState H) :
    ∑ x, (P.clarkson hs hs').weight σ x * ((P.clarkson hs hs').next σ x).W
      ≤ (1 + P.combDim / (2 * s)) * σ.W := by
  have h1 : ∑ x, (P.clarkson hs hs').weight σ x * ((P.clarkson hs hs').next σ x).W
      = σ.W + ∑ x, (P.clarkson hs hs').weight σ x * ∑ h ∈ P.violators x.2, σ.w h := by
    simp only [clarkson_W_next, mul_add, sum_add_distrib, ← sum_mul, Kernel.weight_sum, one_mul]
  rw [h1]
  linarith [P.clarkson_expected_violators hs hs' σ]

/-- **`E[W_T] ≤ W_0 (1 + δ / (2 s))^T`.** -/
theorem expected_W_le (T : ℕ) (σ : RoundState H) :
    (P.clarkson hs hs').expect T σ (fun l => ((P.clarkson hs hs').run σ l).W)
      ≤ (1 + P.combDim / (2 * s)) ^ T * σ.W := by
  have hc : 0 ≤ 1 + (P.combDim : ℝ) / (2 * s) := by positivity
  exact (P.clarkson hs hs').expect_potential_le hc (P.clarkson_step hs hs') T σ

/-- **`E[W_T] ≤ n exp(T δ / (2 s))`.** -/
theorem expected_W_le_exp (T : ℕ) (Z : ℝ) :
    (P.clarkson hs hs').expect T (RoundState.init Z)
        (fun l => ((P.clarkson hs hs').run (RoundState.init Z) l).W)
      ≤ Fintype.card H * Real.exp (T * P.combDim / (2 * s)) := by
  have h := P.expected_W_le hs hs' T (RoundState.init Z)
  rw [RoundState.W_init] at h
  have hx : 0 ≤ (P.combDim : ℝ) / (2 * s) := by positivity
  have h1 : (1 + (P.combDim : ℝ) / (2 * s)) ^ T ≤ Real.exp (T * P.combDim / (2 * s)) := by
    have h2 : Real.exp (T * P.combDim / (2 * s)) = Real.exp ((P.combDim : ℝ) / (2 * s)) ^ T := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    rw [h2]
    exact pow_le_pow_left₀ (by positivity) (by linarith [Real.add_one_le_exp ((P.combDim : ℝ) / (2 * s))]) T
  refine h.trans ?_
  rw [mul_comm]
  exact mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg _)

/-! ## From the expectation to the failure probability -/

/-- The algorithm has not stopped within a path: every sample has a violator. -/
def NotStopped (l : List (Finset H × Finset H)) : Prop :=
  ∀ x ∈ l, ∃ h, P.Violates h x.2

/-- The state after a path records exactly the violation counts of the path. -/
theorem run_count (σ : RoundState H) (l : List (Finset H × Finset H)) (h : H) :
    ((P.clarkson hs hs').run σ l).count h = σ.count h + P.violCount (l.map Prod.snd) h := by
  classical
  induction l generalizing σ with
  | nil => simp [violCount]
  | cons x l ih =>
    rw [Kernel.run_cons, ih]
    simp only [clarkson, violCount, List.map_cons, List.countP_cons, decide_eq_true_eq]
    omega

/-- The weight in the process is the weight of the history. -/
theorem W_run_init (Z : ℝ) (l : List (Finset H × Finset H)) :
    ((P.clarkson hs hs').run (RoundState.init Z) l).W = P.histTotal (l.map Prod.snd) := by
  simp [RoundState.W, RoundState.w, histTotal, histWeight, run_count, RoundState.init]

/-- Pathwise: on a path that has not stopped, `W_T ≥ 2^{T/δ}`. -/
theorem two_rpow_le_of_notStopped [Nonempty H] (hδ : 1 ≤ P.combDim) (Z : ℝ)
    (l : List (Finset H × Finset H)) (hl : P.NotStopped l) :
    (2 : ℝ) ^ ((l.length : ℝ) / P.combDim) ≤ ((P.clarkson hs hs').run (RoundState.init Z) l).W := by
  rw [W_run_init]
  have := P.two_rpow_le_histTotal hδ (hist := l.map Prod.snd) (by
    intro S hS
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hS
    exact exists_violates_iff.1 (hl x hx))
  simpa using this

omit [DecidableEq H] in
theorem W_nonneg (σ : RoundState H) : 0 ≤ σ.W :=
  sum_nonneg fun h _ => (σ.w_pos h).le

/-- **Markov**: `2^{T/δ} P[not stopped after T rounds] ≤ n exp(T δ / (2 s))`. -/
theorem prob_notStopped_mul_le [Nonempty H] (hδ : 1 ≤ P.combDim) (T : ℕ) (Z : ℝ) :
    (2 : ℝ) ^ ((T : ℝ) / P.combDim) * (P.clarkson hs hs').prob T (RoundState.init Z) P.NotStopped
      ≤ Fintype.card H * Real.exp (T * P.combDim / (2 * s)) := by
  refine ((P.clarkson hs hs').markov (φ := fun l => ((P.clarkson hs hs').run (RoundState.init Z) l).W)
    (fun l _ => W_nonneg _) (fun l hl hA => ?_)).trans (P.expected_W_le_exp hs hs' T Z)
  have := P.two_rpow_le_of_notStopped hs hs' hδ Z l hA
  rwa [hl] at this

end Problem

/-! ## The arithmetic -/

/-- The Markov arithmetic: for `T = ⌈12 δ ln n⌉` and `c < ln 2`, the bound `n e^{c T/δ} / 2^{T/δ}` is
at most `n^{-e}` when `e + 1 ≤ 12 (0.693147 - c)`. -/
theorem markov_arith {n δ T : ℕ} (hn : 1 ≤ n) (hδ : 1 ≤ δ)
    (hT : T = ⌈12 * δ * Real.log n⌉₊) {c e : ℝ} (hc : c ≤ 0.693147)
    (he : e + 1 ≤ 12 * (0.693147 - c)) :
    n * Real.exp (c * ((T : ℝ) / δ)) / (2 : ℝ) ^ ((T : ℝ) / δ) ≤ (n : ℝ) ^ (-e) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hδ0 : (0 : ℝ) < δ := by exact_mod_cast hδ
  have hL : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn)
  set L := Real.log n with hLdef
  set x := (T : ℝ) / δ with hx
  have hx12 : 12 * L ≤ x := by
    rw [hx, le_div_iff₀ hδ0, hT]
    have := Nat.le_ceil (12 * (δ : ℝ) * L)
    linarith
  have hlog2 : (0.693147 : ℝ) < Real.log 2 := by
    have := Real.log_two_gt_d9
    linarith
  have hn_eq : (n : ℝ) = Real.exp L := (Real.exp_log hn0).symm
  have h2 : (2 : ℝ) ^ x = Real.exp (Real.log 2 * x) := Real.rpow_def_of_pos (by norm_num) x
  have hpow : (n : ℝ) ^ (-e) = Real.exp (L * -e) := Real.rpow_def_of_pos hn0 _
  have hsplit : (n : ℝ) * Real.exp (c * x) / (2 : ℝ) ^ x
      = Real.exp (L + c * x - Real.log 2 * x) := by
    rw [h2, Real.exp_sub, Real.exp_add, ← hn_eq]
  rw [hsplit, hpow, Real.exp_le_exp]
  -- `x (ln 2 - c) ≥ 12 L (0.693147 - c) ≥ (e + 1) L`
  have hgap : 0 ≤ 0.693147 - c := by linarith
  have h1 : 12 * L * (0.693147 - c) ≤ x * (Real.log 2 - c) :=
    mul_le_mul hx12 (by linarith) hgap (by linarith)
  have h3 : (e + 1) * L ≤ 12 * (0.693147 - c) * L := mul_le_mul_of_nonneg_right he hL
  nlinarith

/-- The arithmetic of the notes: `n e^{T/(2δ)} / 2^{T/δ} ≤ n^{-1.3}`. -/
theorem markov_arith_half {n δ T : ℕ} (hn : 1 ≤ n) (hδ : 1 ≤ δ)
    (hT : T = ⌈12 * δ * Real.log n⌉₊) :
    n * Real.exp ((T : ℝ) / (2 * δ)) / (2 : ℝ) ^ ((T : ℝ) / δ) ≤ (n : ℝ) ^ (-1.3 : ℝ) := by
  have := markov_arith (c := 1 / 2) (e := 1.3) hn hδ hT (by norm_num) (by norm_num)
  have hδ0 : (δ : ℝ) ≠ 0 := by positivity
  have he : (1 / 2 : ℝ) * ((T : ℝ) / δ) = (T : ℝ) / (2 * δ) := by
    field_simp
  rwa [he] at this

namespace Problem

variable {s' : ℝ} (hs' : 0 < s')

theorem two_mul_sq_pos (hδ : 1 ≤ P.combDim) : (0 : ℝ) < 2 * (P.combDim : ℝ) ^ 2 := by
  have : (0 : ℝ) < P.combDim := by exact_mod_cast hδ
  positivity

/-- From the Markov inequality to the bound: if `2^{T/δ} p ≤ n exp(c T/δ)` then `p ≤ n^{-e}`. -/
theorem prob_le_of_markov {δ n T : ℕ} {p c e : ℝ} (hn : 1 ≤ n) (hδ : 1 ≤ δ)
    (hT : T = ⌈12 * δ * Real.log n⌉₊) (hc : c ≤ 0.693147) (he : e + 1 ≤ 12 * (0.693147 - c))
    (h : (2 : ℝ) ^ ((T : ℝ) / δ) * p ≤ n * Real.exp (c * ((T : ℝ) / δ))) :
    p ≤ (n : ℝ) ^ (-e) := by
  refine le_trans ?_ (markov_arith hn hδ hT hc he)
  rw [le_div_iff₀ (Real.rpow_pos_of_pos (by norm_num) _), mul_comm]
  exact h

/-- **Theorem 1, failure probability, as in the notes.** For `δ ≥ 1`, `s = 2 δ²`, `T = ⌈12 δ ln n⌉`,
any `s' > 0` and any initial estimate, `P[not stopped after T rounds] ≤ n^{-1.3}`. -/
theorem failure_prob_le [Nonempty H] (hδ : 1 ≤ P.combDim) (Z : ℝ) :
    (P.clarkson (P.two_mul_sq_pos hδ) hs').prob ⌈12 * (P.combDim : ℝ) * Real.log (Fintype.card H)⌉₊
        (RoundState.init Z) P.NotStopped
      ≤ (Fintype.card H : ℝ) ^ (-1.3 : ℝ) := by
  have hδ0 : (P.combDim : ℝ) ≠ 0 := by
    have : (0 : ℝ) < P.combDim := by exact_mod_cast hδ
    exact this.ne'
  refine prob_le_of_markov (c := 1 / 2) Fintype.card_pos hδ rfl (by norm_num) (by norm_num) ?_
  have h := P.prob_notStopped_mul_le (P.two_mul_sq_pos hδ) hs' hδ
    ⌈12 * (P.combDim : ℝ) * Real.log (Fintype.card H)⌉₊ Z
  refine h.trans (mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _))
  rw [Real.exp_le_exp]
  -- `T δ / (2 s) = T / (4 δ) ≤ T / (2 δ)`
  set T : ℝ := (⌈12 * (P.combDim : ℝ) * Real.log (Fintype.card H)⌉₊ : ℝ)
  have hδ1 : (0 : ℝ) < P.combDim := by exact_mod_cast hδ
  have hT0 : 0 ≤ T := Nat.cast_nonneg _
  have e1 : T * P.combDim / (2 * (2 * (P.combDim : ℝ) ^ 2)) = T / P.combDim * (1 / 4) := by
    field_simp
    ring
  rw [e1]
  have : 0 ≤ T / P.combDim := by positivity
  linarith

/-- **Theorem 1, failure probability, what the proof gives.** The notes' step
`n exp(T δ / (2 s)) ≤ n e^{T/(2δ)}` loses a factor `2` in the exponent. Without it the bound is
`n^{-4.3}`. -/
theorem failure_prob_le_sharp [Nonempty H] (hδ : 1 ≤ P.combDim) (Z : ℝ) :
    (P.clarkson (P.two_mul_sq_pos hδ) hs').prob ⌈12 * (P.combDim : ℝ) * Real.log (Fintype.card H)⌉₊
        (RoundState.init Z) P.NotStopped
      ≤ (Fintype.card H : ℝ) ^ (-4.3 : ℝ) := by
  refine prob_le_of_markov (c := 1 / 4) Fintype.card_pos hδ rfl (by norm_num) (by norm_num) ?_
  have h := P.prob_notStopped_mul_le (P.two_mul_sq_pos hδ) hs' hδ
    ⌈12 * (P.combDim : ℝ) * Real.log (Fintype.card H)⌉₊ Z
  refine h.trans (le_of_eq ?_)
  congr 2
  have hδ1 : (0 : ℝ) < P.combDim := by exact_mod_cast hδ
  field_simp
  ring

/-! ## The redraw of an earlier version

An earlier version of the notes redrew when `|S_t|` was too large, and the notes now avoid it. Conditioning breaks independence, so the step
`E[W_{t+1} | past] ≤ W_t (1 + δ / (2 s))` does not follow for that process. What does hold is the same
step with an extra factor `1 / P[accept | past]`. With `P[accept | past] ≥ 1/2` this is exactly the
factor `2` that `failure_prob_le` wastes, so `n^{-1.3}` survives. Acceptance is a hypothesis below,
on an invariant set of states, since it is not true for every state: a very large previous estimate
makes `R` likely to be empty, so that `W̃ = 0` and `S = H`. Such an estimate is reachable with small
positive probability, since the Horvitz-Thompson sum can reach about `n W⁻ / (2 s')`. So neither
acceptance nor a mean sample size can be bounded from every reachable state. -/

variable {s : ℝ} (hs : 0 < s)

/-- `E[W_{t+1} | past, accept] ≤ W_t (1 + δ / (2 s q))` with `q = P[accept | past]`. Only `q > 0` is
needed. The step redrawn is the whole pair `(R, S)`: redrawing `S` alone can never end, when
`W̃ = 0` and `n` exceeds the cap. -/
theorem conditioned_step (A : RoundState H → Finset H × Finset H → Prop) {σ : RoundState H}
    (hq : 0 < (P.clarkson hs hs').acceptProb A σ) :
    ∑ x, ((P.clarkson hs hs').conditioned A).weight σ x *
        ((P.clarkson hs hs').conditioned A |>.next σ x).W
      ≤ (1 + P.combDim / (2 * s * (P.clarkson hs hs').acceptProb A σ)) * σ.W := by
  set K := P.clarkson hs hs' with hK
  set q := K.acceptProb A σ with hqdef
  have hnext : ∀ x, ((K.conditioned A).next σ x).W = σ.W + ∑ h ∈ P.violators x.2, σ.w h :=
    fun x => P.clarkson_W_next hs hs' σ x
  have h1 : ∑ x, (K.conditioned A).weight σ x * ((K.conditioned A).next σ x).W
      = σ.W + ∑ x, (K.conditioned A).weight σ x * ∑ h ∈ P.violators x.2, σ.w h := by
    simp only [hnext, mul_add, sum_add_distrib, ← sum_mul, Kernel.weight_sum, one_mul]
  have h2 := K.sum_conditioned_le A hq (g := fun x => ∑ h ∈ P.violators x.2, σ.w h)
    (fun x => sum_nonneg fun h _ => (σ.w_pos h).le)
  have h3 : (∑ x, K.weight σ x * ∑ h ∈ P.violators x.2, σ.w h) / q
      ≤ (P.combDim / (2 * s) * σ.W) / q :=
    div_le_div_of_nonneg_right (P.clarkson_expected_violators hs hs' σ) hq.le
  have h4 : (P.combDim / (2 * s) * σ.W) / q = P.combDim / (2 * s * q) * σ.W := by
    field_simp
  rw [h1, add_mul, one_mul]
  linarith

/-- **Theorem 1 with the redraw.** Suppose that from every state of an invariant set containing the
start, the event `A` has probability at least `1/2`. Then, with `s = 2 δ²`, the process conditioned on
`A` satisfies `E[W_T] ≤ n exp(T δ / s) = n e^{T/(2δ)}`, and `P[not stopped] ≤ n^{-1.3}`. -/
theorem failure_prob_le_redraw [Nonempty H] (hδ : 1 ≤ P.combDim) (Z : ℝ)
    (A : RoundState H → Finset H × Finset H → Prop) (I : RoundState H → Prop)
    (h0 : I (RoundState.init Z))
    (hinv : ∀ σ x, I σ → A σ x →
      (P.clarkson (P.two_mul_sq_pos hδ) hs').weight σ x ≠ 0 →
      I ((P.clarkson (P.two_mul_sq_pos hδ) hs').next σ x))
    (hq : ∀ σ, I σ → 1 / 2 ≤ (P.clarkson (P.two_mul_sq_pos hδ) hs').acceptProb A σ) :
    ((P.clarkson (P.two_mul_sq_pos hδ) hs').conditioned A).prob
        ⌈12 * (P.combDim : ℝ) * Real.log (Fintype.card H)⌉₊ (RoundState.init Z) P.NotStopped
      ≤ (Fintype.card H : ℝ) ^ (-1.3 : ℝ) := by
  classical
  have hs2 := P.two_mul_sq_pos hδ
  set K := P.clarkson hs2 hs' with hK
  set T := ⌈12 * (P.combDim : ℝ) * Real.log (Fintype.card H)⌉₊ with hT
  have hδ1 : (0 : ℝ) < P.combDim := by exact_mod_cast hδ
  have hqpos : ∀ σ, I σ → 0 < K.acceptProb A σ := fun σ hσ =>
    lt_of_lt_of_le (by norm_num) (hq σ hσ)
  have hstep : ∀ σ, I σ → ∑ x, (K.conditioned A).weight σ x * ((K.conditioned A).next σ x).W
      ≤ (1 + (P.combDim : ℝ) / (2 * (P.combDim : ℝ) ^ 2)) * σ.W := by
    intro σ hσ
    refine (P.conditioned_step hs' hs2 A (hqpos σ hσ)).trans ?_
    refine mul_le_mul_of_nonneg_right ?_ (W_nonneg σ)
    have h1 : (P.combDim : ℝ) / (2 * (2 * (P.combDim : ℝ) ^ 2) * K.acceptProb A σ)
        ≤ (P.combDim : ℝ) / (2 * (P.combDim : ℝ) ^ 2) := by
      refine div_le_div_of_nonneg_left hδ1.le (by positivity) ?_
      have := hq σ hσ
      have hp : (0 : ℝ) < 2 * (P.combDim : ℝ) ^ 2 := hs2
      nlinarith
    linarith
  have hinv' : ∀ σ x, I σ → (K.conditioned A).weight σ x ≠ 0 → I ((K.conditioned A).next σ x) := by
    intro σ x hσ hx
    have hq0 := hqpos σ hσ
    have hx' : (if A σ x then K.weight σ x else 0) / K.acceptProb A σ ≠ 0 := by
      simpa only [Kernel.conditioned, ite_eq_left hq0] using hx
    by_cases hA : A σ x
    · rw [ite_eq_left hA] at hx'
      exact hinv σ x hσ hA (fun h => hx' (by rw [h, zero_div]))
    · rw [ite_eq_right hA, zero_div] at hx'
      exact absurd rfl hx'
  have hc : 0 ≤ 1 + (P.combDim : ℝ) / (2 * (P.combDim : ℝ) ^ 2) := by positivity
  have hE := (K.conditioned A).expect_potential_le_on hc hinv' hstep T (RoundState.init Z) h0
  rw [RoundState.W_init] at hE
  have hrun : ∀ l, (K.conditioned A).run (RoundState.init Z) l = K.run (RoundState.init Z) l :=
    fun _ => rfl
  have hM : (2 : ℝ) ^ ((T : ℝ) / P.combDim) * (K.conditioned A).prob T (RoundState.init Z) P.NotStopped
      ≤ (K.conditioned A).expect T (RoundState.init Z)
          (fun l => ((K.conditioned A).run (RoundState.init Z) l).W) := by
    refine (K.conditioned A).markov (fun l _ => W_nonneg _) (fun l hl hA => ?_)
    rw [hrun]
    have := P.two_rpow_le_of_notStopped hs2 hs' hδ Z l hA
    rwa [hl] at this
  refine prob_le_of_markov (c := 1 / 2) Fintype.card_pos hδ hT (by norm_num) (by norm_num) ?_
  refine (hM.trans hE).trans ?_
  rw [mul_comm]
  refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
  -- `(1 + x)^T ≤ exp(T x)` with `x = 1 / (2 δ)`
  have hx : (P.combDim : ℝ) / (2 * (P.combDim : ℝ) ^ 2) = 1 / 2 * (1 / P.combDim) := by
    field_simp
  have h2 : Real.exp (1 / 2 * ((T : ℝ) / P.combDim))
      = Real.exp ((P.combDim : ℝ) / (2 * (P.combDim : ℝ) ^ 2)) ^ T := by
    rw [← Real.exp_nat_mul, hx]
    congr 1
    ring
  rw [h2]
  exact pow_le_pow_left₀ hc
    (by linarith [Real.add_one_le_exp ((P.combDim : ℝ) / (2 * (P.combDim : ℝ) ^ 2))]) T

end Problem

end LPType
