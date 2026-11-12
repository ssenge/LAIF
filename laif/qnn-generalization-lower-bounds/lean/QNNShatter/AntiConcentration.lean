import Mathlib

/-!
# Anti-concentration of integer combinations

Let `k : ι → ℤ` and `c : ℤ`. If every `k j` is nonzero, the number of `b ∈ {0,1}^ι` with
`∑ j, k j * b j = c` is at most `C(n, ⌊n/2⌋)` for `n = |ι|`: after flipping the coordinates with
`k j < 0`, the solution sets form an antichain of `Finset ι`, and an antichain of `Finset ι`
has at most `C(n, ⌊n/2⌋)` members.
If some `k j₀` is nonzero, the number of `b ∈ {0, …, M}^ι` with `∑ j, k j * b j = c` is at most
`(M+1)^(n-1)`, since the other coordinates determine `b j₀`.
-/

open Finset

namespace QNNShatter

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The vectors `b ∈ {0, …, M}^ι` with `∑ j, k j * b j = c`. -/
def solutions (M : ℕ) (k : ι → ℤ) (c : ℤ) : Finset (ι → Fin (M + 1)) :=
  univ.filter fun b => ∑ j, k j * ((b j : ℕ) : ℤ) = c

theorem mem_solutions {M : ℕ} {k : ι → ℤ} {c : ℤ} {b : ι → Fin (M + 1)} :
    b ∈ solutions M k c ↔ ∑ j, k j * ((b j : ℕ) : ℤ) = c := by
  simp [solutions]

omit [DecidableEq ι] in
/-- For positive weights, the subsets with a given weight form an antichain. -/
theorem isAntichain_subsetSum (a : ι → ℤ) (ha : ∀ j, 0 < a j) (c : ℤ) :
    IsAntichain (· ⊆ ·) ((univ.filter fun s : Finset ι => ∑ j ∈ s, a j = c : Finset _) :
      Set (Finset ι)) := by
  intro s hs t ht hne hst
  simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hs ht
  have hss : s ⊂ t := LE.le.ssubset_of_ne hst hne
  obtain ⟨i, hit, his⟩ := (Finset.ssubset_iff_of_subset hst).1 hss
  have hlt : ∑ j ∈ s, a j < ∑ j ∈ t, a j :=
    Finset.sum_lt_sum_of_subset hst hit his (ha i) (fun j _ _ => (ha j).le)
  omega

/-- The coordinates on which `b j = 1` holds exactly when `k j` is not negative. -/
def flipSet (k : ι → ℤ) (b : ι → Fin 2) : Finset ι :=
  univ.filter fun j => (b j = 1 ↔ ¬ k j < 0)

omit [DecidableEq ι] in
theorem sum_eq_flipSet (k : ι → ℤ) (hk : ∀ j, k j ≠ 0) (b : ι → Fin 2) :
    ∑ j, k j * ((b j : ℕ) : ℤ)
      = ∑ j, (if k j < 0 then k j else 0) + ∑ j ∈ flipSet k b, |k j| := by
  rw [flipSet, Finset.sum_filter, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hkj := hk j
  generalize b j = x
  fin_cases x
  · by_cases h : k j < 0
    · simp [h, abs_of_neg h]
    · simp [h]
  · by_cases h : k j < 0
    · simp [h]
    · simp [h, abs_of_nonneg (not_lt.1 h)]

/-- Anti-concentration in `{0,1}^ι`: for nonzero integers `k j`, at most `C(n, ⌊n/2⌋)` vectors
`b ∈ {0,1}^ι` satisfy `∑ j, k j * b j = c`, where `n = |ι|`. -/
theorem card_solutions_two_le (k : ι → ℤ) (hk : ∀ j, k j ≠ 0) (c : ℤ) :
    (solutions 1 k c).card ≤ (Fintype.card ι).choose (Fintype.card ι / 2) := by
  have hA := (isAntichain_subsetSum (fun j => |k j|) (fun j => abs_pos.2 (hk j))
    (c - ∑ j, (if k j < 0 then k j else 0))).sperner
  refine le_trans (Finset.card_le_card_of_injOn (flipSet k) ?_ ?_) hA
  · intro b hb
    have hb' := mem_solutions.1 hb
    rw [sum_eq_flipSet k hk] at hb'
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq]
    omega
  · intro b _ b' _ h
    funext j
    have hj := congrArg (j ∈ ·) h
    simp only [flipSet, mem_filter, mem_univ, true_and, eq_iff_iff] at hj
    have h1 : b j = 1 ↔ b' j = 1 := by tauto
    revert h1
    generalize b j = x
    generalize b' j = y
    fin_cases x <;> fin_cases y <;> simp

/-- Anti-concentration in `{0,1}^v` for `ι = Fin v`. -/
theorem card_solutions_two_le_fin {v : ℕ} (k : Fin v → ℤ) (hk : ∀ j, k j ≠ 0) (c : ℤ) :
    (solutions 1 k c).card ≤ v.choose (v / 2) := by
  simpa using card_solutions_two_le k hk c

/-- Anti-concentration in `{0, …, M}^ι`: if `k j₀ ≠ 0`, at most `(M+1)^(n-1)` vectors
`b ∈ {0, …, M}^ι` satisfy `∑ j, k j * b j = c`, where `n = |ι|`. -/
theorem card_solutions_le (M : ℕ) (k : ι → ℤ) (j₀ : ι) (hk : k j₀ ≠ 0) (c : ℤ) :
    (solutions M k c).card ≤ (M + 1) ^ (Fintype.card ι - 1) := by
  calc (solutions M k c).card
      ≤ (univ : Finset ({j // j ≠ j₀} → Fin (M + 1))).card := by
        refine Finset.card_le_card_of_injOn (fun b j => b j) (fun _ _ => mem_coe.2 (mem_univ _)) ?_
        intro b hb b' hb' h
        have hb1 := mem_solutions.1 hb
        have hb2 := mem_solutions.1 hb'
        have hoff : ∀ j, j ≠ j₀ → b j = b' j := fun j hj => congrFun h ⟨j, hj⟩
        rw [← Finset.add_sum_erase _ _ (mem_univ j₀)] at hb1 hb2
        have hrest : ∑ j ∈ univ.erase j₀, k j * ((b j : ℕ) : ℤ)
            = ∑ j ∈ univ.erase j₀, k j * ((b' j : ℕ) : ℤ) :=
          Finset.sum_congr rfl fun j hj => by rw [hoff j (Finset.ne_of_mem_erase hj)]
        have h0 : k j₀ * ((b j₀ : ℕ) : ℤ) = k j₀ * ((b' j₀ : ℕ) : ℤ) := by omega
        have h00 : b j₀ = b' j₀ := Fin.ext (by exact_mod_cast mul_left_cancel₀ hk h0)
        funext j
        by_cases hj : j = j₀
        · subst hj; exact h00
        · exact hoff j hj
    _ = (M + 1) ^ (Fintype.card ι - 1) := by
        rw [card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_subtype_compl,
          Fintype.card_subtype_eq]

/-- Anti-concentration in `{0, …, M}^v` for `ι = Fin v`. -/
theorem card_solutions_le_fin (M : ℕ) {v : ℕ} (k : Fin v → ℤ) (j₀ : Fin v) (hk : k j₀ ≠ 0)
    (c : ℤ) : (solutions M k c).card ≤ (M + 1) ^ (v - 1) := by
  simpa using card_solutions_le M k j₀ hk c

end QNNShatter
