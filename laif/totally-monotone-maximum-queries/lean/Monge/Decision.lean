import Monge.Model
import Monge.Recurrence
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# Theorem 3: the decision problem

Inputs are `r × c` matrices with entries in `Fin k`, which stands for any finite ordered set. The
proof runs on any increasing choice of rows `ρ : Fin q → Fin r`, and on any test `τ` that is upward
closed on values. This covers `≥ θ`, `> θ` and subsets of rows, which is what the corollary in the
notes uses.

`gam_rect_le` is the induction on sub-rectangles, using Lemma A and Lemma B on factorizations.
`gam_someEntry_le` is the whole matrix. `decision_query_le`, `theorem3_query_le`, and
`theorem3_sqrt_log` turn this into query bounds using the named hypotheses in `Monge.Model`.
-/

namespace Monge

variable {r c k q : ℕ}

/-- Matrices with entries in `Fin k`, as strings over `Fin r × Fin c`. -/
abbrev Mat (r c k : ℕ) := Fin r × Fin c → Fin k

/-- The totally monotone inputs. -/
def IsTM (x : Mat r c k) : Prop := TotallyMonotone fun (i : Fin r) (j : Fin c) => x (i, j)

/-- `p(i)`, the leftmost maximum of row `i`. -/
noncomputable def lm [NeZero c] (x : Mat r c k) (i : Fin r) : Fin c :=
  rowMax (fun (i : Fin r) (j : Fin c) => x (i, j)) i

theorem lm_spec [NeZero c] (x : Mat r c k) (i : Fin r) :
    IsLeftmostMax (fun j => x (i, j)) (lm x i) :=
  rowMax_spec (fun (i : Fin r) (j : Fin c) => x (i, j)) i

theorem lm_mono [NeZero c] {x : Mat r c k} (hx : IsTM x) {i i' : Fin r} (h : i ≤ i') :
    lm x i ≤ lm x i' :=
  TotallyMonotone.rowMax_monotone hx h

/-- `D[s, n, l, w]`: totally monotone inputs whose chosen rows `s, …, s + n - 1` have their leftmost
maxima in the columns `l, …, l + w`. -/
def Drect [NeZero c] (ρ : Fin q → Fin r) (s n l w : ℕ) : Set (Mat r c k) :=
  {x | IsTM x ∧ ∀ i : Fin q, s ≤ i → (i : ℕ) < s + n →
    l ≤ (lm x (ρ i) : ℕ) ∧ (lm x (ρ i) : ℕ) ≤ l + w}

/-- `F[s, n, l, w]`: some entry in these rows and columns passes the test. -/
noncomputable def Frect (τ : Fin k → Bool) (ρ : Fin q → Fin r) (s n l w : ℕ) (x : Mat r c k) :
    Bool := by
  classical exact decide (∃ (i : Fin q) (j : Fin c), s ≤ i ∧ (i : ℕ) < s + n ∧ l ≤ j ∧
    (j : ℕ) ≤ l + w ∧ τ (x (ρ i, j)) = true)

theorem Frect_eq_true {τ : Fin k → Bool} {ρ : Fin q → Fin r} {s n l w : ℕ} {x : Mat r c k} :
    Frect τ ρ s n l w x = true ↔ ∃ (i : Fin q) (j : Fin c), s ≤ i ∧ (i : ℕ) < s + n ∧ l ≤ j ∧
      (j : ℕ) ≤ l + w ∧ τ (x (ρ i, j)) = true := by
  simp [Frect]

/-- `A(x)`: the leftmost maximum of row `m` on the window of `w + 1` columns starting at `l`. -/
noncomputable def winMax (m : Fin r) (l w : ℕ) (hw : l + w < c) (x : Mat r c k) : Fin (w + 1) :=
  leftmost fun a : Fin (w + 1) => x (m, ⟨l + a, by have := a.2; omega⟩)

/-- On the domain, the window maximum is the global leftmost maximum. -/
theorem winMax_val [NeZero c] {m : Fin r} {l w : ℕ} {hw : l + w < c} {x : Mat r c k}
    (h1 : l ≤ (lm x m : ℕ)) (h2 : (lm x m : ℕ) ≤ l + w) :
    l + (winMax m l w hw x : ℕ) = lm x m := by
  have hspec := lm_spec x m
  have hP : (⟨l + ((lm x m : ℕ) - l), by have := (lm x m).2; omega⟩ : Fin c) = lm x m :=
    Fin.ext (by simp only; omega)
  have hle : IsLeftmostMax (fun a : Fin (w + 1) => x (m, ⟨l + a, by have := a.2; omega⟩))
      ⟨(lm x m : ℕ) - l, by omega⟩ := by
    constructor
    · intro a
      simp only
      rw [hP]
      exact hspec.1 _
    · intro a ha
      simp only
      rw [hP]
      apply hspec.2
      rw [Fin.lt_def]
      rw [Fin.lt_def] at ha
      simp only at ha ⊢
      omega
  have heq : winMax m l w hw x = ⟨(lm x m : ℕ) - l, by omega⟩ := leftmost_eq hle
  rw [heq]
  simp only
  omega

/-- The three parts of `G_p`: the pivot bit, the rows above and the rows below. -/
noncomputable def stepParts (τ : Fin k → Bool) (ρ : Fin q → Fin r) (s n l w : ℕ) (hw : l + w < c)
    (m : Fin q) (a : Fin (w + 1)) : Fin 3 → Mat r c k → Bool :=
  ![fun x => τ (x (ρ m, ⟨l + a, by have := a.2; omega⟩)),
    Frect τ ρ s ((n - 1) / 2) l a,
    Frect τ ρ (s + (n - 1) / 2 + 1) (n - 1 - (n - 1) / 2) (l + a) (w - a)]

/-- The decomposition `F = [x_{m,p} ∈ τ] ∨ F_above ∨ F_below`, on the domain, with `A(x) = p`. -/
theorem Frect_eq_or [NeZero c] {τ : Fin k → Bool} (hτ : ∀ a b, a ≤ b → τ a = true → τ b = true)
    {ρ : Fin q → Fin r} (hρ : StrictMono ρ) {s n l w : ℕ} (hn : n ≠ 0) (hs : s + n ≤ q)
    (hw : l + w < c) {x : Mat r c k} (hx : x ∈ Drect ρ s n l w) :
    Frect τ ρ s n l w x =
      orOf (stepParts τ ρ s n l w hw ⟨s + (n - 1) / 2, by omega⟩
        (winMax (ρ ⟨s + (n - 1) / 2, by omega⟩) l w hw x)) x := by
  obtain ⟨hTM, hwin⟩ := hx
  set m : Fin q := ⟨s + (n - 1) / 2, by omega⟩ with hm
  have hmwin := hwin m (by simp [hm]) (by simp only [hm]; omega)
  have hval := winMax_val (hw := hw) hmwin.1 hmwin.2
  set a := winMax (ρ m) l w hw x with ha
  rw [Bool.eq_iff_iff, Frect_eq_true, orOf_eq_true]
  constructor
  · rintro ⟨i, j, h1, h2, -, -, hτij⟩
    have hP := hwin i h1 h2
    have htest : τ (x (ρ i, lm x (ρ i))) = true := hτ _ _ ((lm_spec x (ρ i)).1 j) hτij
    rcases lt_trichotomy (i : ℕ) (s + (n - 1) / 2) with hlt | heq | hgt
    · refine ⟨1, ?_⟩
      show Frect τ ρ s ((n - 1) / 2) l a x = true
      rw [Frect_eq_true]
      have hile : ρ i ≤ ρ m := hρ.monotone (by rw [Fin.le_def]; simp only [hm]; omega)
      have hmono : (lm x (ρ i) : ℕ) ≤ lm x (ρ m) := lm_mono hTM hile
      exact ⟨i, lm x (ρ i), h1, by omega, hP.1, by omega, htest⟩
    · refine ⟨0, ?_⟩
      show τ (x (ρ m, ⟨l + a, _⟩)) = true
      have him : i = m := Fin.ext heq
      have hcol : (⟨l + a, by have := a.2; omega⟩ : Fin c) = lm x (ρ m) := Fin.ext hval
      rw [hcol, ← him]
      exact htest
    · refine ⟨2, ?_⟩
      show Frect τ ρ (s + (n - 1) / 2 + 1) (n - 1 - (n - 1) / 2) (l + a) (w - a) x = true
      rw [Frect_eq_true]
      have hile : ρ m ≤ ρ i := hρ.monotone (by rw [Fin.le_def]; simp only [hm]; omega)
      have hmono : (lm x (ρ m) : ℕ) ≤ lm x (ρ i) := lm_mono hTM hile
      have haw := a.2
      exact ⟨i, lm x (ρ i), by omega, by omega, by omega, by omega, htest⟩
  · rintro ⟨t, ht⟩
    have haw := a.2
    fin_cases t
    · have ht' : τ (x (ρ m, ⟨l + a, by omega⟩)) = true := ht
      exact ⟨m, ⟨l + a, by omega⟩, by simp [hm], by simp only [hm]; omega, by simp, by simp only; omega,
        ht'⟩
    · have ht' : Frect τ ρ s ((n - 1) / 2) l a x = true := ht
      rw [Frect_eq_true] at ht'
      obtain ⟨i, j, h1, h2, h3, h4, h5⟩ := ht'
      exact ⟨i, j, h1, by omega, h3, by omega, h5⟩
    · have ht' : Frect τ ρ (s + (n - 1) / 2 + 1) (n - 1 - (n - 1) / 2) (l + a) (w - a) x = true := ht
      rw [Frect_eq_true] at ht'
      obtain ⟨i, j, h1, h2, h3, h4, h5⟩ := ht'
      exact ⟨i, j, by omega, by omega, by omega, by omega, h5⟩

/-- `D_p ⊆ D[s, m - 1, l, p]`. -/
theorem subset_above [NeZero c] {ρ : Fin q → Fin r} (hρ : StrictMono ρ) {s n l w : ℕ} (hn : n ≠ 0)
    (hs : s + n ≤ q) (hw : l + w < c) (a : Fin (w + 1)) :
    (Drect ρ s n l w ∩ {x : Mat r c k | winMax (ρ ⟨s + (n - 1) / 2, by omega⟩) l w hw x = a}) ⊆
      Drect ρ s ((n - 1) / 2) l a := by
  rintro x ⟨⟨hTM, hwin⟩, hA⟩
  refine ⟨hTM, fun i h1 h2 => ?_⟩
  have hmwin := hwin ⟨s + (n - 1) / 2, by omega⟩ (by simp) (by simp only; omega)
  have hval := winMax_val (hw := hw) hmwin.1 hmwin.2
  rw [show winMax (ρ ⟨s + (n - 1) / 2, by omega⟩) l w hw x = a from hA] at hval
  have hile : ρ i ≤ ρ ⟨s + (n - 1) / 2, by omega⟩ := hρ.monotone (by rw [Fin.le_def]; simp only; omega)
  have hmono : (lm x (ρ i) : ℕ) ≤ lm x (ρ ⟨s + (n - 1) / 2, by omega⟩) := lm_mono hTM hile
  exact ⟨(hwin i h1 (by omega)).1, by omega⟩

/-- `D_p ⊆ D[m + 1, t, p, u]`. -/
theorem subset_below [NeZero c] {ρ : Fin q → Fin r} (hρ : StrictMono ρ) {s n l w : ℕ} (hn : n ≠ 0)
    (hs : s + n ≤ q) (hw : l + w < c) (a : Fin (w + 1)) :
    (Drect ρ s n l w ∩ {x : Mat r c k | winMax (ρ ⟨s + (n - 1) / 2, by omega⟩) l w hw x = a}) ⊆
      Drect ρ (s + (n - 1) / 2 + 1) (n - 1 - (n - 1) / 2) (l + a) (w - a) := by
  rintro x ⟨⟨hTM, hwin⟩, hA⟩
  refine ⟨hTM, fun i h1 h2 => ?_⟩
  have hmwin := hwin ⟨s + (n - 1) / 2, by omega⟩ (by simp) (by simp only; omega)
  have hval := winMax_val (hw := hw) hmwin.1 hmwin.2
  rw [show winMax (ρ ⟨s + (n - 1) / 2, by omega⟩) l w hw x = a from hA] at hval
  have hile : ρ ⟨s + (n - 1) / 2, by omega⟩ ≤ ρ i := hρ.monotone (by rw [Fin.le_def]; simp only; omega)
  have hmono : (lm x (ρ ⟨s + (n - 1) / 2, by omega⟩) : ℕ) ≤ lm x (ρ i) := lm_mono hTM hile
  have haw := a.2
  have hup := (hwin i (by omega) (by omega)).2
  exact ⟨by omega, by omega⟩

/-- **The induction of Theorem 3.** `hA` is the bound `γ(A) ≤ κ √c` for window maxima. -/
theorem gam_rect_le [NeZero c] {κ : ℝ} (hκ : 0 ≤ κ)
    (hA : ∀ (D : Set (Mat r c k)) (m : Fin r) (l w : ℕ) (hw : l + w < c),
      gam D (winMax m l w hw) ≤ κ * √((w + 1 : ℕ) : ℝ))
    {τ : Fin k → Bool} (hτ : ∀ a b, a ≤ b → τ a = true → τ b = true)
    {ρ : Fin q → Fin r} (hρ : StrictMono ρ)
    (n s l w : ℕ) (hs : s + n ≤ q) (hw : l + w < c) :
    gam (Drect (c := c) (k := k) ρ s n l w) (Frect τ ρ s n l w) ≤
      (2 * κ + 1) * ell n * √(((w + 1 : ℕ) : ℝ) + n) := by
  induction n using Nat.strong_induction_on generalizing s l w with
  | _ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hpos
    · have hconst : gam (Drect (k := k) (c := c) ρ s 0 l w) (Frect τ ρ s 0 l w) = 0 := by
        apply gam_const
        intro x _ y _
        have hfalse : ∀ z : Mat r c k, Frect τ ρ s 0 l w z = false := by
          intro z
          rw [← Bool.not_eq_true, Frect_eq_true]
          rintro ⟨i, j, h1, h2, -⟩
          omega
        rw [hfalse x, hfalse y]
      rw [hconst]
      simp
    · have hn : n ≠ 0 := by omega
      set m : Fin q := ⟨s + (n - 1) / 2, by omega⟩ with hm
      set D : Set (Mat r c k) := Drect ρ s n l w with hD
      set A : Mat r c k → Fin (w + 1) := winMax (ρ m) l w hw with hAdef
      set b : ℝ := (2 * κ + 1) * ell n * √(((w + 1 : ℕ) : ℝ) + n) -
        2 * κ * √((w + 1 : ℕ) : ℝ) with hb
      have hG : ∀ a : Fin (w + 1), gam (D ∩ {x | A x = a})
          (orOf (stepParts τ ρ s n l w hw m a)) ≤ b := by
        intro a
        have haw := a.2
        set Da : Set (Mat r c k) := D ∩ {x | A x = a} with hDa
        have h0 := gam_or_le Da (stepParts τ ρ s n l w hw m a)
        rw [Fin.sum_univ_three] at h0
        have hg0 : gam Da (stepParts τ ρ s n l w hw m a 0) ≤ 1 :=
          gam_bit_le_one Da (ρ m, ⟨l + a, by omega⟩) τ
        have hg0' : gam Da (stepParts τ ρ s n l w hw m a 0) ^ 2 ≤ 1 :=
          pow_le_one₀ (gam_nonneg _ _) hg0
        have hX₁ : gam Da (stepParts τ ρ s n l w hw m a 1) ≤
            (2 * κ + 1) * ell ((n - 1) / 2) * √(((a + 1 : ℕ) : ℝ) + ((n - 1) / 2 : ℕ)) :=
          (gam_mono _ (subset_above hρ hn hs hw a)).trans
            (ih ((n - 1) / 2) (by omega) s l a (by omega) (by omega))
        have hX₂ : gam Da (stepParts τ ρ s n l w hw m a 2) ≤
            (2 * κ + 1) * ell (n - 1 - (n - 1) / 2) *
              √(((w - a + 1 : ℕ) : ℝ) + ((n - 1 - (n - 1) / 2 : ℕ) : ℝ)) :=
          (gam_mono _ (subset_below hρ hn hs hw a)).trans
            (ih (n - 1 - (n - 1) / 2) (by omega) (s + (n - 1) / 2 + 1) (l + a) (w - a) (by omega)
              (by omega))
        have hstep := recurrence_step (c := w + 1) (r := n) (c₁ := a + 1)
          (c₂ := w - a + 1) hκ hpos (gam_nonneg _ _) (gam_nonneg _ _) hX₁ hX₂
          (by omega) (by omega) (by omega)
        have hroot : √(gam Da (stepParts τ ρ s n l w hw m a 0) ^ 2 +
            gam Da (stepParts τ ρ s n l w hw m a 1) ^ 2 +
            gam Da (stepParts τ ρ s n l w hw m a 2) ^ 2) ≤
            √(1 + gam Da (stepParts τ ρ s n l w hw m a 1) ^ 2 +
              gam Da (stepParts τ ρ s n l w hw m a 2) ^ 2) :=
          Real.sqrt_le_sqrt (by linarith)
        rw [hb]
        linarith
      have hmain : gam D (Frect τ ρ s n l w) ≤ 2 * gam D A + b :=
        gam_seq_le (G := fun a => orOf (stepParts τ ρ s n l w hw m a))
          ((gam_nonneg _ _).trans (hG 0)) hG (fun x hx => Frect_eq_or hτ hρ hn hs hw hx)
      have hAle : gam D A ≤ κ * √((w + 1 : ℕ) : ℝ) := hA D (ρ m) l w hw
      rw [hb] at hmain
      linarith

/-! ## The whole matrix -/

/-- `[some entry in the chosen rows passes the test]`. -/
noncomputable def someEntry (τ : Fin k → Bool) (ρ : Fin q → Fin r) (x : Mat r c k) : Bool := by
  classical exact decide (∃ (i : Fin q) (j : Fin c), τ (x (ρ i, j)) = true)

theorem someEntry_eq_true {τ : Fin k → Bool} {ρ : Fin q → Fin r} {x : Mat r c k} :
    someEntry τ ρ x = true ↔ ∃ (i : Fin q) (j : Fin c), τ (x (ρ i, j)) = true := by
  simp [someEntry]

/-- The totally monotone inputs, as a set. -/
def tmInputs (r c k : ℕ) : Set (Mat r c k) := {x | IsTM x}

/-- `γ` of the whole decision problem, on any increasing choice of rows. -/
theorem gam_someEntry_le [NeZero c] {κ : ℝ} (hκ : 0 ≤ κ)
    (hA : ∀ (D : Set (Mat r c k)) (m : Fin r) (l w : ℕ) (hw : l + w < c),
      gam D (winMax m l w hw) ≤ κ * √((w + 1 : ℕ) : ℝ))
    {τ : Fin k → Bool} (hτ : ∀ a b, a ≤ b → τ a = true → τ b = true)
    {ρ : Fin q → Fin r} (hρ : StrictMono ρ) :
    gam (tmInputs r c k) (someEntry τ ρ) ≤ (2 * κ + 1) * ell q * √((c : ℝ) + q) := by
  have hc := NeZero.pos c
  have hsub : tmInputs r c k ⊆ Drect ρ 0 q 0 (c - 1) := by
    intro x hx
    refine ⟨hx, fun i _ _ => ⟨Nat.zero_le _, ?_⟩⟩
    have := (lm x (ρ i)).2
    omega
  have hcongr : gam (tmInputs r c k) (someEntry τ ρ) =
      gam (tmInputs r c k) (Frect τ ρ 0 q 0 (c - 1)) := by
    apply gam_congr
    intro x _
    rw [Bool.eq_iff_iff, someEntry_eq_true, Frect_eq_true]
    constructor
    · rintro ⟨i, j, h⟩
      have h1 := i.2
      have h2 := j.2
      exact ⟨i, j, Nat.zero_le _, by omega, Nat.zero_le _, by omega, h⟩
    · rintro ⟨i, j, -, -, -, -, h⟩
      exact ⟨i, j, h⟩
  rw [hcongr]
  have h := gam_rect_le hκ hA hτ hρ q 0 0 (c - 1) (by omega) (by omega)
  have hcast : ((c - 1 + 1 : ℕ) : ℝ) = c := by
    congr 1
    omega
  rw [hcast] at h
  exact (gam_mono _ hsub).trans h

/-! ## From the hypotheses to query bounds -/

/-- The window maximum as an instance of the maximum finding hypothesis. -/
theorem gam_winMax_le {C κ₀ : ℝ} (hC : 0 ≤ C) (hLQ : LeeQueryAdv C) (hLG : LeeAdvGamma)
    (hDH : DurrHoyer κ₀) (D : Set (Mat r c k)) (m : Fin r) (l w : ℕ) (hw : l + w < c) :
    gam D (winMax m l w hw) ≤ (2 * C * κ₀) * √((w + 1 : ℕ) : ℝ) :=
  gam_leftmost_le hC hLQ hLG hDH D (c := w + 1)
    (fun a => (m, ⟨l + a, by have := a.2; omega⟩))

/-- **Query bound on any increasing choice of rows, for any upward-closed test.** -/
theorem decision_query_le {C κ₀ : ℝ} (hC : 0 ≤ C) (hκ₀ : 0 ≤ κ₀) (hLQ : LeeQueryAdv C)
    (hLG : LeeAdvGamma) (hDH : DurrHoyer κ₀) [NeZero c] {τ : Fin k → Bool}
    (hτ : ∀ a b, a ≤ b → τ a = true → τ b = true) {ρ : Fin q → Fin r} (hρ : StrictMono ρ) :
    (queryQ (tmInputs r c k) (someEntry τ ρ) : ℝ) ≤
      C * ((2 * (2 * C * κ₀) + 1) * ell q * √((c : ℝ) + q)) :=
  (queryQ_le_gam hC hLQ hLG _ _).trans (mul_le_mul_of_nonneg_left
    (gam_someEntry_le (by positivity) (gam_winMax_le hC hLQ hLG hDH) hτ hρ) hC)

/-- The function `F(M) = [max M ≥ θ]`. -/
noncomputable def maxAtLeast (θ : Fin k) (x : Mat r c k) : Bool :=
  someEntry (fun a => decide (θ ≤ a)) id x

theorem maxAtLeast_eq_true {θ : Fin k} {x : Mat r c k} :
    maxAtLeast θ x = true ↔ ∃ i j, θ ≤ x (i, j) := by
  simp [maxAtLeast, someEntry_eq_true]

/-- **Theorem 3, `γ` form.** `γ(F) ≤ (2 κ + 1) ⌈log₂(r + 1)⌉ √(c + r)`, where `κ` is such that a window
maximum on `c'` columns has `γ ≤ κ √c'`. -/
theorem theorem3_gamma [NeZero c] {κ : ℝ} (hκ : 0 ≤ κ)
    (hA : ∀ (D : Set (Mat r c k)) (m : Fin r) (l w : ℕ) (hw : l + w < c),
      gam D (winMax m l w hw) ≤ κ * √((w + 1 : ℕ) : ℝ)) (θ : Fin k) :
    gam (tmInputs r c k) (maxAtLeast θ) ≤ (2 * κ + 1) * ell r * √((c : ℝ) + r) :=
  gam_someEntry_le hκ hA (fun a b hab h => by
    simp only [decide_eq_true_eq] at h ⊢
    exact h.trans hab) strictMono_id

/-- **Theorem 3, query form.** -/
theorem theorem3_query_le {C κ₀ : ℝ} (hC : 0 ≤ C) (hκ₀ : 0 ≤ κ₀) (hLQ : LeeQueryAdv C)
    (hLG : LeeAdvGamma) (hDH : DurrHoyer κ₀) [NeZero c] (θ : Fin k) :
    (queryQ (tmInputs r c k) (maxAtLeast θ) : ℝ) ≤
      C * ((2 * (2 * C * κ₀) + 1) * ell r * √((c : ℝ) + r)) :=
  (queryQ_le_gam hC hLQ hLG _ _).trans (mul_le_mul_of_nonneg_left
    (theorem3_gamma (by positivity) (gam_winMax_le hC hLQ hLG hDH) θ) hC)

/-- `⌈log₂(r + 1)⌉ ≤ 2 log₂ n` for `r ≤ n` and `n ≥ 2`. -/
theorem ell_le_two_logb {r n : ℕ} (hr : r ≤ n) (hn : 2 ≤ n) :
    (ell r : ℝ) ≤ 2 * Real.logb 2 n := by
  have hmono : ell r ≤ ell n := Nat.clog_mono_right 2 (by omega)
  have hpos : 0 < ell n := Nat.clog_pos (by norm_num) (by omega)
  obtain ⟨e, he⟩ : ∃ e, ell n = e + 1 := ⟨ell n - 1, by omega⟩
  have hlt : 2 ^ (ell n - 1) < n + 1 := Nat.pow_pred_clog_lt_self (by norm_num) (by omega)
  rw [he] at hlt
  simp only [Nat.add_sub_cancel] at hlt
  have hle : (2 : ℝ) ^ e ≤ n := by exact_mod_cast Nat.lt_succ_iff.mp hlt
  have h2 : Real.logb 2 ((2 : ℝ) ^ e) ≤ Real.logb 2 n :=
    Real.logb_le_logb_of_le (by norm_num) (by positivity) hle
  rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num), mul_one] at h2
  have h3 : (1 : ℝ) ≤ Real.logb 2 n := by
    have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
    have := Real.logb_le_logb_of_le (b := 2) (x := 2) (y := n) (by norm_num) (by norm_num) hn'
    rwa [Real.logb_self_eq_one (by norm_num)] at this
  have h4 : (ell r : ℝ) ≤ (e : ℝ) + 1 := by
    have : ell r ≤ e + 1 := by omega
    exact_mod_cast this
  linarith

/-- **Theorem 3, final form.** `Q(F) = O(√n log n)` for `n = max(r, c) ≥ 2`, with a constant that does
not depend on `r`, `c`, the alphabet or `θ`. The hypotheses are `LeeQueryAdv`, `LeeAdvGamma` and
`DurrHoyer`. -/
theorem theorem3_sqrt_log {C κ₀ : ℝ} (hC : 0 ≤ C) (hκ₀ : 0 ≤ κ₀) (hLQ : LeeQueryAdv C)
    (hLG : LeeAdvGamma) (hDH : DurrHoyer κ₀) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (r c k n : ℕ) [NeZero c] (θ : Fin k), r ≤ n → c ≤ n → 2 ≤ n →
      (queryQ (tmInputs r c k) (maxAtLeast θ) : ℝ) ≤ K * √(n : ℝ) * Real.logb 2 n := by
  set a := 2 * (2 * C * κ₀) + 1 with ha
  have ha0 : 0 ≤ a := by positivity
  refine ⟨C * a * (2 * √2), by positivity, ?_⟩
  intro r c k n _ θ hr hc hn
  refine (theorem3_query_le hC hκ₀ hLQ hLG hDH θ).trans ?_
  have hell := ell_le_two_logb hr hn
  have hsqrt : √((c : ℝ) + r) ≤ √2 * √(n : ℝ) := by
    rw [← Real.sqrt_mul (by norm_num)]
    apply Real.sqrt_le_sqrt
    have h1 : (r : ℝ) ≤ n := by exact_mod_cast hr
    have h2 : (c : ℝ) ≤ n := by exact_mod_cast hc
    linarith
  have hprod : (ell r : ℝ) * √((c : ℝ) + r) ≤ (2 * Real.logb 2 n) * (√2 * √(n : ℝ)) :=
    mul_le_mul hell hsqrt (Real.sqrt_nonneg _) ((Nat.cast_nonneg _).trans hell)
  calc C * (a * ell r * √((c : ℝ) + r)) = C * a * ((ell r : ℝ) * √((c : ℝ) + r)) := by ring
    _ ≤ C * a * ((2 * Real.logb 2 n) * (√2 * √(n : ℝ))) :=
        mul_le_mul_of_nonneg_left hprod (by positivity)
    _ = C * a * (2 * √2) * √(n : ℝ) * Real.logb 2 n := by ring

end Monge
