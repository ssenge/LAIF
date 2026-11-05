import SubsetBalancing.Cap
import SubsetBalancing.Filter

/-!
# From a good prime to marked residues

Lemmas 2, 3 and 4 composed, for the actual lists. Fix a good partition and a good prime, with its set
`R` of residues. The bins are `𝒳_ρ` and `𝒴_ρ`, enumerated arbitrarily, and the windows are their
first `min (T, |bin|)` elements. Then every residue of `R` is marked: its windows contain a pair with
equal exact sum. So the marked fraction of `Z_P` is at least `|R| / (2 P₀)`, which is at least
`1 / (2 (2 + 64 b) s)`.
-/

open Finset

namespace SubsetBalancing

variable {ι Lab : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq Lab] {L : ι → Lab}
  {ν : Layout Lab} {p : Pin ι} {D y : ι → ℤ}

/-- The bin `𝒳_ρ`. -/
noncomputable def binX (ν : Layout Lab) (L : ι → Lab) (p : Pin ι) (y : ι → ℤ) (P : ℕ) (ρ : ℤ) :
    Finset (ι → ℤ) :=
  (listX ν L p).filter fun X => res P (dot X y) = ρ

/-- The bin `𝒴_ρ`. -/
noncomputable def binY (ν : Layout Lab) (L : ι → Lab) (p : Pin ι) (y : ι → ℤ) (P : ℕ) (ρ : ℤ) :
    Finset (ι → ℤ) :=
  (listY ν L p).filter fun Y => res P (dot Y y) = ρ

/-- The windows of the bins at residue `ρ` contain a pair with equal exact sum. -/
def PairFound {P : ℕ} (T : ℕ) (ex : ∀ ρ, Enum (binX ν L p y P ρ)) (ey : ∀ ρ, Enum (binY ν L p y P ρ))
    (ρ : ℤ) : Prop :=
  ∃ X ∈ firstWindow (ex ρ) T, ∃ Y ∈ firstWindow (ey ρ) T, dot X y = dot Y y

/-- **The residue step.** At a residue with a representation `(X⋆, Y⋆)` in that residue, for which at
most `T/2` elements of the two bins have an exact sum other than the value, the windows contain a
pair with equal exact sum. -/
theorem pairFound_of_good {P T : ℕ} (hT : 1 ≤ T) (hy : dot D y = 0)
    (ex : ∀ ρ, Enum (binX ν L p y P ρ)) (ey : ∀ ρ, Enum (binY ν L p y P ρ)) {ρ : ℤ}
    (h : ∃ q ∈ reps L ν p D, res P (dot q.1 y) = ρ ∧ res P (dot q.2 y) = ρ ∧
      ((#{X ∈ listX ν L p | res P (dot X y) = ρ ∧ dot X y ≠ dot q.1 y}
        + #{Y ∈ listY ν L p | res P (dot Y y) = ρ ∧ dot Y y ≠ dot q.1 y} : ℕ) : ℝ) ≤ (T : ℝ) / 2) :
    PairFound T ex ey ρ := by
  classical
  obtain ⟨q, hq, hqX, hqY, hcount⟩ := h
  have hqr := mem_reps.mp hq
  have hmemX : q.1 ∈ binX ν L p y P ρ := mem_filter.mpr ⟨mem_listX.mpr hqr.isX, hqX⟩
  have hmemY : q.2 ∈ binY ν L p y P ρ := mem_filter.mpr ⟨mem_listY.mpr hqr.isY, hqY⟩
  set v := dot q.1 y with hv
  have hval : dot q.2 y = v := (value_eq hq hy).symm
  have hsum2 : 2 * (#{X ∈ listX ν L p | res P (dot X y) = ρ ∧ dot X y ≠ v}
      + #{Y ∈ listY ν L p | res P (dot Y y) = ρ ∧ dot Y y ≠ v}) ≤ T := by
    have : ((2 * (#{X ∈ listX ν L p | res P (dot X y) = ρ ∧ dot X y ≠ v}
        + #{Y ∈ listY ν L p | res P (dot Y y) = ρ ∧ dot Y y ≠ v}) : ℕ) : ℝ) ≤ T := by
      push_cast at hcount ⊢
      linarith
    exact_mod_cast this
  have hcountX : #{X ∈ binX ν L p y P ρ | ¬ dot X y = v}
      ≤ #{X ∈ listX ν L p | res P (dot X y) = ρ ∧ dot X y ≠ v} := by
    apply card_le_card
    intro X hX
    obtain ⟨h1, h2⟩ := mem_filter.mp hX
    obtain ⟨h3, h4⟩ := mem_filter.mp h1
    exact mem_filter.mpr ⟨h3, h4, h2⟩
  have hcountY : #{Y ∈ binY ν L p y P ρ | ¬ dot Y y = v}
      ≤ #{Y ∈ listY ν L p | res P (dot Y y) = ρ ∧ dot Y y ≠ v} := by
    apply card_le_card
    intro Y hY
    obtain ⟨h1, h2⟩ := mem_filter.mp hY
    obtain ⟨h3, h4⟩ := mem_filter.mp h1
    exact mem_filter.mpr ⟨h3, h4, h2⟩
  obtain ⟨X, hX, hXv⟩ := cap_lemma (ex ρ) hT (fun X => dot X y = v) ⟨q.1, hmemX, rfl⟩ (by omega)
  obtain ⟨Y, hY, hYv⟩ := cap_lemma (ey ρ) hT (fun Y => dot Y y = v) ⟨q.2, hmemY, hval⟩ (by omega)
  exact ⟨X, hX, Y, hY, hXv.trans hYv.symm⟩

omit [Fintype ι] [DecidableEq ι] [DecidableEq Lab] in
/-- **The marked fraction.** With `m ≥ |R|` marked residues in `Z_P` and `P ≤ 2 P₀`, the marked
fraction is at least `|R| / (2 P₀)`. With `K ≤ |R| (2 + 64 b)` and `P₀ = K s`, this is at least
`1 / (2 (2 + 64 b) s)`. -/
theorem marked_fraction {K r m P P₀ s b : ℝ} (hK : 0 < K) (hs : 0 < s) (hb : 0 ≤ b) (hP : 0 < P)
    (hR : K ≤ r * (2 + 64 * b)) (hm : r ≤ m) (hP₂ : P ≤ 2 * P₀) (hP₀ : P₀ = K * s) :
    r / (2 * P₀) ≤ m / P ∧ 1 / (2 * (2 + 64 * b) * s) ≤ r / (2 * P₀) := by
  have hc : 0 < 2 + 64 * b := by linarith
  have hd : 0 < 2 * (2 + 64 * b) * s := by positivity
  have hP₀pos : 0 < P₀ := by rw [hP₀]; positivity
  have hr : 0 ≤ r := by
    by_contra h
    have : r * (2 + 64 * b) < 0 := mul_neg_of_neg_of_pos (not_le.mp h) hc
    linarith
  constructor
  · rw [div_le_div_iff₀ (by positivity) hP]
    calc r * P ≤ r * (2 * P₀) := mul_le_mul_of_nonneg_left hP₂ hr
      _ ≤ m * (2 * P₀) := mul_le_mul_of_nonneg_right hm (by positivity)
  · rw [div_le_div_iff₀ hd (by positivity), one_mul, hP₀]
    have := mul_le_mul_of_nonneg_right hR (by positivity : 0 ≤ 2 * s)
    nlinarith

end SubsetBalancing
