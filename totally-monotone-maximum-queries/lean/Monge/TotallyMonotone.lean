import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Total monotonicity

Notes, opening section. Inverse Monge implies totally monotone, leftmost row maxima are
nondecreasing, and the window lemma. Rows and columns are arbitrary linear orders, so this applies
to `Fin r`, `Fin c` and to sub-rectangles.
-/

open Finset

namespace Monge

variable {ι κ α : Type*}

/-- Inverse Monge: `M[i, j] + M[i', j'] ≥ M[i, j'] + M[i', j]` for `i < i'` and `j < j'`. -/
def InverseMonge [LT ι] [LT κ] (M : ι → κ → ℝ) : Prop :=
  ∀ ⦃i i' : ι⦄ ⦃j j' : κ⦄, i < i' → j < j' → M i j' + M i' j ≤ M i j + M i' j'

/-- Totally monotone: for `i < i'` and `j < j'`, `M[i, j] < M[i, j']` implies
`M[i', j] < M[i', j']`. -/
def TotallyMonotone [LT ι] [LT κ] [LT α] (M : ι → κ → α) : Prop :=
  ∀ ⦃i i' : ι⦄ ⦃j j' : κ⦄, i < i' → j < j' → M i j < M i j' → M i' j < M i' j'

/-- Every inverse Monge matrix is totally monotone. -/
theorem InverseMonge.totallyMonotone [LT ι] [LT κ] {M : ι → κ → ℝ} (h : InverseMonge M) :
    TotallyMonotone M := by
  intro i i' j j' hi hj hlt
  have := h hi hj
  linarith

/-- `p` is the leftmost maximum of the row `f`. -/
def IsLeftmostMax [LT κ] [LE α] [LT α] (f : κ → α) (p : κ) : Prop :=
  (∀ j, f j ≤ f p) ∧ ∀ j, j < p → f j < f p

/-- The leftmost maximum of a row is unique. -/
theorem IsLeftmostMax.unique [LinearOrder κ] [LinearOrder α] {f : κ → α} {p q : κ}
    (hp : IsLeftmostMax f p) (hq : IsLeftmostMax f q) : p = q := by
  rcases lt_trichotomy p q with h | h | h
  · exact absurd (hp.1 q) (not_le.mpr (hq.2 p h))
  · exact h
  · exact absurd (hq.1 p) (not_le.mpr (hp.2 q h))

section Leftmost

variable [Fintype κ] [Nonempty κ] [LinearOrder κ] [LinearOrder α]

omit [LinearOrder κ] in
theorem exists_isMax (f : κ → α) : (univ.filter fun p => ∀ j, f j ≤ f p).Nonempty := by
  obtain ⟨p, hp⟩ := Finite.exists_max f
  exact ⟨p, by simpa using hp⟩

/-- The leftmost maximum of a row over a finite nonempty column order. -/
noncomputable def leftmost (f : κ → α) : κ :=
  (univ.filter fun p => ∀ j, f j ≤ f p).min' (exists_isMax f)

theorem leftmost_spec (f : κ → α) : IsLeftmostMax f (leftmost f) := by
  have hmax : ∀ j, f j ≤ f (leftmost f) := (mem_filter.mp (Finset.min'_mem _ (exists_isMax f))).2
  refine ⟨hmax, fun j hj => lt_of_le_of_ne (hmax j) fun heq => ?_⟩
  have : leftmost f ≤ j := Finset.min'_le _ j (by
    simp only [mem_filter, mem_univ, true_and]
    intro j'
    rw [heq]
    exact hmax j')
  exact absurd hj (not_lt.mpr this)

theorem leftmost_eq {f : κ → α} {p : κ} (hp : IsLeftmostMax f p) : leftmost f = p :=
  (leftmost_spec f).unique hp

end Leftmost

section Monotone

variable [LinearOrder ι] [LinearOrder κ] [LinearOrder α]

/-- The core exchange argument: leftmost maxima of two rows are ordered like the rows. -/
theorem TotallyMonotone.leftmost_le {M : ι → κ → α} (hM : TotallyMonotone M) {i i' : ι} {p p' : κ}
    (hi : i ≤ i') (hp : IsLeftmostMax (M i) p) (hp' : IsLeftmostMax (M i') p') : p ≤ p' := by
  rcases hi.eq_or_lt with rfl | hlt
  · exact (hp.unique hp').le
  · by_contra hcon
    have hlt' : p' < p := not_le.mp hcon
    exact absurd (hp'.1 p) (not_le.mpr (hM hlt hlt' (hp.2 p' hlt')))

variable [Fintype κ] [Nonempty κ]

/-- The leftmost maximum of row `i`. -/
noncomputable def rowMax (M : ι → κ → α) (i : ι) : κ := leftmost (M i)

omit [LinearOrder ι] in
theorem rowMax_spec (M : ι → κ → α) (i : ι) : IsLeftmostMax (M i) (rowMax M i) :=
  leftmost_spec _

/-- Leftmost row maxima are nondecreasing. -/
theorem TotallyMonotone.rowMax_monotone {M : ι → κ → α} (hM : TotallyMonotone M) :
    Monotone (rowMax M) :=
  fun _ _ hi => hM.leftmost_le hi (rowMax_spec M _) (rowMax_spec M _)

/-- The window lemma: rows above `m` have leftmost maximum at most `p(m)`, rows below have leftmost
maximum at least `p(m)`. -/
theorem TotallyMonotone.window {M : ι → κ → α} (hM : TotallyMonotone M) (m : ι) :
    (∀ i, i < m → rowMax M i ≤ rowMax M m) ∧ (∀ i, m < i → rowMax M m ≤ rowMax M i) :=
  ⟨fun _ hi => hM.rowMax_monotone hi.le, fun _ hi => hM.rowMax_monotone hi.le⟩

end Monotone

section Transfer

variable {ι' κ' β : Type*}

/-- Sub-rectangles (any strictly increasing choice of rows and columns) stay totally monotone. -/
theorem TotallyMonotone.submatrix [LT ι] [LT κ] [LT α] [LT ι'] [LT κ'] {M : ι → κ → α}
    (hM : TotallyMonotone M) {f : ι' → ι} {g : κ' → κ}
    (hf : ∀ ⦃a b⦄, a < b → f a < f b) (hg : ∀ ⦃a b⦄, a < b → g a < g b) :
    TotallyMonotone fun i j => M (f i) (g j) :=
  fun _ _ _ _ hi hj hlt => hM (hf hi) (hg hj) hlt

/-- Total monotonicity only uses the order of the values within a row, so it survives applying a
function that is strictly increasing on the values. -/
theorem TotallyMonotone.comp [LT ι] [LT κ] [LinearOrder α] [LinearOrder β] {M : ι → κ → α}
    (hM : TotallyMonotone M) {φ : α → β} (hφ : StrictMonoOn φ (Set.range fun q : ι × κ => M q.1 q.2)) :
    TotallyMonotone fun i j => φ (M i j) := by
  intro i i' j j' hi hj hlt
  have mem : ∀ a b, M a b ∈ Set.range fun q : ι × κ => M q.1 q.2 := fun a b => ⟨(a, b), rfl⟩
  have h1 : M i j < M i j' := (hφ.lt_iff_lt (mem _ _) (mem _ _)).mp hlt
  exact hφ (mem _ _) (mem _ _) (hM hi hj h1)

/-- Squaring preserves total monotonicity on nonnegative matrices. -/
theorem TotallyMonotone.sq [LT ι] [LT κ] {M : ι → κ → ℝ} (hM : TotallyMonotone M)
    (h0 : ∀ i j, 0 ≤ M i j) : TotallyMonotone fun i j => M i j ^ 2 := by
  intro i i' j j' hi hj hlt
  have h1 : M i j < M i j' := lt_of_pow_lt_pow_left₀ 2 (h0 _ _) hlt
  exact pow_lt_pow_left₀ (hM hi hj h1) (h0 _ _) (by norm_num)

/-- Minima are the same problem up to sign and column order: reversing the columns and negating
preserves total monotonicity. -/
theorem TotallyMonotone.neg_reverse [LT ι] [LinearOrder κ] [LT κ'] {M : ι → κ → ℝ}
    (hM : TotallyMonotone M) {g : κ' → κ} (hg : ∀ ⦃a b⦄, a < b → g b < g a) :
    TotallyMonotone fun i j => - M i (g j) := by
  intro i i' j j' hi hj hlt
  have := hM hi (hg hj) (neg_lt_neg_iff.mp hlt)
  exact neg_lt_neg this

end Transfer

end Monge
