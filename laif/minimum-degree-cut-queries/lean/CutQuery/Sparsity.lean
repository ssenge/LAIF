import CutQuery.Family
import CutQuery.Lattice

/-!
# Sparsity of visible degree shifts: the statements used by the quantum and classical bounds
-/

open Finset

namespace CutQuery

variable {k R : ℕ}

section Bridge

/-- The query matrix over the integers. -/
def queryMat (x : Fin R → Fin (k + 3) → Bool) : Fin R → Fin (k + 3) → ℤ := fun s v => bitZ (x s v)

theorem queryMat_binary (x : Fin R → Fin (k + 3) → Bool) (s : Fin R) (v : Fin (k + 3)) :
    queryMat x s v = 0 ∨ queryMat x s v = 1 := by
  unfold queryMat bitZ
  split_ifs <;> simp

theorem cutInd_queryMat (x : Fin R → Fin (k + 3) → Bool) (s : Fin R) (a c : Fin (k + 3)) :
    cutInd (queryMat x) s a c = cut (pairVec a c) (x s) := by
  rw [cut_pairVec]
  unfold cutInd queryMat bitZ
  cases x s a <;> cases x s c <;> simp

theorem labelVec_queryMat (x : Fin R → Fin (k + 3) → Bool) (u v : Fin (k + 3)) :
    labelVec (queryMat x) 0 1 2 u v = fun s => cut (labelVector u v) (x s) := by
  funext s
  simp only [labelVec, cutInd_queryMat, cut_labelVector]

theorem vertexVec_queryMat (x : Fin R → Fin (k + 3) → Bool) (v : Fin (k + 3)) :
    vertexVec (queryMat x) v (helperA v) (helperC v) = fun s => cut (shiftVec v) (x s) := by
  funext s
  simp only [vertexVec, cutInd_queryMat, cut_shiftVec]

theorem abs_yhat_queryMat_le (x : Fin R → Fin (k + 3) → Bool) (v : Fin (k + 3)) (s : Option (Fin R)) :
    |yhat (queryMat x) 0 v s| ≤ 1 := by
  cases s with
  | none => simp [yhat]
  | some s =>
    simp only [yhat]
    rw [abs_le]
    rcases queryMat_binary x s v with h | h <;> rcases queryMat_binary x s 0 with h' | h' <;>
      rw [h, h'] <;> norm_num

theorem labelVector_comm (u v : Fin (k + 3)) : labelVector u v = labelVector v u := by
  unfold labelVector
  rw [pairVec_comm u v]
  abel

/-- A pair avoiding vertex `0` gives the zero vector or a basis vector. -/
theorem labelVector_cases {u v : Fin (k + 3)} (hu : u ≠ 0) (hv : v ≠ 0) (huv : u ≠ v) :
    labelVector u v = 0 ∨ ∃ j : LabelIdx k, b j = labelVector u v := by
  have hlt : ∀ {u v : Fin (k + 3)}, u ≠ 0 → u < v →
      labelVector u v = 0 ∨ ∃ j : LabelIdx k, b j = labelVector u v := by
    intro u v hu h
    by_cases h12 : (u, v) = ((1 : Fin (k + 3)), (2 : Fin (k + 3)))
    · left
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj h12
      unfold labelVector
      abel
    · exact Or.inr ⟨⟨⟨(u, v), h⟩, hu, h12⟩, rfl⟩
  rcases lt_or_gt_of_ne huv with h | h
  · exact hlt hu h
  · rw [labelVector_comm]
    exact hlt hv h

/-- The label of a pair avoiding vertex `0` lies in any subgroup containing the basis labels. -/
theorem labelVec_mem (x : Fin R → Fin (k + 3) → Bool) (L : AddSubgroup (Fin R → ℤ))
    (hlab : ∀ j : LabelIdx k, (fun s => cut (b j) (x s)) ∈ L) (u v : Fin (k + 3))
    (hu : u ≠ 0) (hv : v ≠ 0) (huv : u ≠ v) : labelVec (queryMat x) 0 1 2 u v ∈ L := by
  rw [labelVec_queryMat]
  rcases labelVector_cases hu hv huv with h | ⟨j, h⟩
  · rw [h]
    have : (fun s => cut (0 : Weights (k + 3)) (x s)) = 0 := by
      funext s
      exact cut_zero _
    rw [this]
    exact L.zero_mem
  · rw [← h]
    exact hlab j

theorem helperA_of_ne {v : Fin (k + 3)} (hv : v ≠ 0) : helperA v = 0 := by
  simp [helperA, hv]

theorem helperC_ne_zero (v : Fin (k + 3)) : helperC v ≠ 0 := by
  unfold helperC
  split_ifs
  · exact zero_ne_two'.symm
  · exact zero_ne_one'.symm

theorem cutSum_queryMat {A : Type*} [AddCommGroup A] (x : Fin R → Fin (k + 3) → Bool) (t : Fin R → A)
    (a c : Fin (k + 3)) : cutSum (queryMat x) t a c = ∑ s, cut (pairVec a c) (x s) • t s := by
  unfold cutSum
  refine sum_congr rfl fun s _ => ?_
  rw [← cutInd_queryMat]
  rfl

theorem sum_cut_labelVector {A : Type*} [AddCommGroup A] (x : Fin R → Fin (k + 3) → Bool) (t : Fin R → A)
    (u v : Fin (k + 3)) :
    ∑ s, cut (labelVector u v) (x s) • t s
      = cutSum (queryMat x) t u v - cutSum (queryMat x) t 0 u - cutSum (queryMat x) t 0 v
        + cutSum (queryMat x) t 0 1 + cutSum (queryMat x) t 0 2 - cutSum (queryMat x) t 1 2 := by
  simp only [cutSum_queryMat, cut_labelVector, sub_smul, add_smul, sum_sub_distrib, sum_add_distrib]

theorem sum_cut_shiftVec {A : Type*} [AddCommGroup A] (x : Fin R → Fin (k + 3) → Bool) (t : Fin R → A)
    (v : Fin (k + 3)) :
    ∑ s, cut (shiftVec v) (x s) • t s
      = cutSum (queryMat x) t v (helperA v) + cutSum (queryMat x) t v (helperC v)
        - cutSum (queryMat x) t (helperA v) (helperC v) := by
  simp only [cutSum_queryMat, cut_shiftVec, sub_smul, add_smul, sum_sub_distrib, sum_add_distrib]

theorem two_divisible_real (y : AddCircle (1 : ℝ)) : ∃ β : AddCircle (1 : ℝ), (2 : ℤ) • β = y := by
  obtain ⟨r, rfl⟩ := QuotientAddGroup.mk_surjective y
  refine ⟨QuotientAddGroup.mk (r / 2), ?_⟩
  have h : (2 : ℤ) • (r / 2) = r := by simp only [zsmul_eq_mul]; push_cast; ring
  exact (map_zsmul (QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : ℝ))) 2 (r / 2)).symm.trans
    (congrArg _ h)

/-- At most one more than the count without vertex `0`. -/
theorem card_le_of_erase_zero (Y : Finset (Fin (k + 3))) (h : (Y.erase 0).card ≤ 2 * (R + 1)) :
    Y.card ≤ 2 * R + 3 := by
  have := pred_card_le_card_erase (s := Y) (a := 0)
  omega

end Bridge

/-- Lemma 2 for cut queries. `x` are the query sets and `t` their coefficients in `R/Z`. If every label
`⟨b_j, F⟩` has norm at most `η`, then few vertices have a large `G ⟨B_v, F⟩`. -/
theorem sparsity_cut (x : Fin R → Fin (k + 3) → Bool) (t : Fin R → AddCircle (1 : ℝ)) (η : ℝ) (hη : 0 ≤ η)
    (G : ℕ) (hG : ∀ d : ℕ, 1 ≤ d → d ≤ k + 3 → d ∣ G)
    (hlab : ∀ j : LabelIdx k, ‖∑ s, cut (b j) (x s) • t s‖ ≤ η) :
    (univ.filter fun v : Fin (k + 3) =>
      (G : ℝ) * (((k + 3) ^ 2 * (k + 3).factorial + 3 : ℕ) : ℝ) * η
        < ‖(G : ℤ) • ∑ s, cut (shiftVec v) (x s) • t s‖).card ≤ 2 * R + 3 := by
  apply card_le_of_erase_zero
  set Y := univ.filter fun v : Fin (k + 3) =>
      (G : ℝ) * (((k + 3) ^ 2 * (k + 3).factorial + 3 : ℕ) : ℝ) * η
        < ‖(G : ℤ) • ∑ s, cut (shiftVec v) (x s) • t s‖ with hY
  set x' := queryMat x with hx'
  set F := cutSum x' t with hFdef
  have hFc : ∀ a b, F a b = F b a := fun a b => cutSum_comm x' t a b
  obtain ⟨β₀, hβ₀⟩ := two_divisible_real (F 0 1 + F 0 2 - F 1 2)
  have hβ₀' : β₀ + β₀ = F 0 1 + F 0 2 - F 1 2 := by rw [← two_smul ℤ β₀]; exact hβ₀
  let β : Fin (k + 3) → AddCircle (1 : ℝ) := fun a => if a = 0 then β₀ else F 0 a - β₀
  have hβ0 : β 0 = β₀ := by simp [β]
  have hβne : ∀ a, a ≠ 0 → β a = F 0 a - β₀ := fun a ha => by simp [β, ha]
  let ε : Fin (k + 3) → Fin (k + 3) → AddCircle (1 : ℝ) := fun a c => F a c - β a - β c
  have hF : ∀ a c, a ≠ c → cutSum x' t a c = β a + β c + ε a c := by
    intro a c _
    simp only [ε, hFdef]
    abel
  have hε0 : ∀ a, a ≠ 0 → ε a 0 = 0 := by
    intro a ha
    simp only [ε, hβ0, hβne a ha, hFc a 0]
    abel
  have hε0' : ∀ a, a ≠ 0 → ε 0 a = 0 := by
    intro a ha
    simp only [ε, hβ0, hβne a ha]
    abel
  have hεeq : ∀ u v, u ≠ 0 → v ≠ 0 → ε u v = ∑ s, cut (labelVector u v) (x s) • t s := by
    intro u v hu hv
    rw [sum_cut_labelVector]
    simp only [ε, hβne u hu, hβne v hv]
    change F u v - (F 0 u - β₀) - (F 0 v - β₀) = F u v - F 0 u - F 0 v + F 0 1 + F 0 2 - F 1 2
    have : F 0 1 + F 0 2 - F 1 2 + F u v - F 0 u - F 0 v
        = F u v - F 0 u - F 0 v + F 0 1 + F 0 2 - F 1 2 := by abel
    rw [← this, ← hβ₀']
    abel
  have hεle : ∀ u v, u ≠ 0 → v ≠ 0 → u ≠ v → ‖ε u v‖ ≤ η := by
    intro u v hu hv huv
    rw [hεeq u v hu hv]
    rcases labelVector_cases hu hv huv with h | ⟨j, h⟩
    · rw [h]
      simpa [cut_zero] using hη
    · rw [← h]
      exact hlab j
  have hv0 : ∀ v : ↥(Y.erase 0), (v : Fin (k + 3)) ≠ 0 := fun v => (mem_erase.mp v.2).1
  have hcard : Fintype.card ↥(Y.erase 0) ≤ k + 3 := by
    rw [Fintype.card_coe]
    simpa using card_le_univ (Y.erase 0)
  have hbin := queryMat_binary x
  have hdiag : ∀ u : ↥(Y.erase 0), pr (fun v : ↥(Y.erase 0) => yhat x' 0 (v : Fin (k + 3))) (Hhat t β₀) u u
      = (2 : ℤ) • β u := by
    intro u
    have := pr_yhat_diag x' t β ε 0 hbin hF (hv0 u)
    rw [hε0 _ (hv0 u), smul_zero, add_zero, hβ0] at this
    exact this
  have hoff : ∀ u v : ↥(Y.erase 0), u ≠ v →
      ‖pr (fun v : ↥(Y.erase 0) => yhat x' 0 (v : Fin (k + 3))) (Hhat t β₀) u v‖ ≤ η := by
    intro u v huv
    have hne' : (u : Fin (k + 3)) ≠ v := fun h => huv (Subtype.ext h)
    have := pr_yhat_offdiag x' t β ε 0 (fun s => hbin s 0) hF hne' (hv0 u) (hv0 v)
    rw [hε0 _ (hv0 u), hε0 _ (hv0 v), zero_add, zero_sub, hβ0] at this
    change ‖pr (yhat x' 0) (Hhat t β₀) u v‖ ≤ η
    rw [this, norm_neg]
    exact hεle _ _ (hv0 u) (hv0 v) hne'
  have hbig : ∀ u : ↥(Y.erase 0), (G : ℝ) *
      (((Fintype.card ↥(Y.erase 0)) ^ 2 * (Fintype.card ↥(Y.erase 0)).factorial : ℕ) : ℝ) * η
      < ‖(G : ℤ) • ((2 : ℤ) • β u)‖ := by
    intro u
    have hu0 := hv0 u
    have hmem : (u : Fin (k + 3)) ∈ Y := (mem_erase.mp u.2).2
    have hvis := (mem_filter.mp hmem).2
    set w : Fin (k + 3) := u.1 with hw
    set e := helperC w with he
    have he0 : e ≠ 0 := helperC_ne_zero w
    have hwe : w ≠ e := helperC_ne w
    have hsum : ∑ s, cut (shiftVec w) (x s) • t s = (2 : ℤ) • β w + ε w e := by
      rw [sum_cut_shiftVec, helperA_of_ne hu0, ← he]
      change F w 0 + F w e - F 0 e = _
      simp only [ε, hβne w hu0, hβne e he0, hFc w 0, two_smul]
      abel
    rw [hsum, smul_add] at hvis
    have hG0 : (0 : ℝ) ≤ G := Nat.cast_nonneg G
    have h1 : ‖(G : ℤ) • ε w e‖ ≤ (G : ℝ) * η := by
      have := norm_zsmul_le (G : ℤ) (ε w e)
      have h2 : ‖((G : ℕ) : ℤ)‖ = (G : ℝ) := by simp
      rw [h2] at this
      exact this.trans (mul_le_mul_of_nonneg_left (hεle _ _ hu0 he0 hwe) hG0)
    have h2 := norm_add_le ((G : ℤ) • (2 : ℤ) • β w) ((G : ℤ) • ε w e)
    have h3 : ((Fintype.card ↥(Y.erase 0)) ^ 2 * (Fintype.card ↥(Y.erase 0)).factorial : ℕ)
        ≤ (k + 3) ^ 2 * (k + 3).factorial :=
      Nat.mul_le_mul (Nat.pow_le_pow_left hcard 2) (Nat.factorial_le hcard)
    have h4 : (((Fintype.card ↥(Y.erase 0)) ^ 2 * (Fintype.card ↥(Y.erase 0)).factorial : ℕ) : ℝ)
        ≤ (((k + 3) ^ 2 * (k + 3).factorial : ℕ) : ℝ) := by exact_mod_cast h3
    have h5 : (G : ℝ) *
        (((Fintype.card ↥(Y.erase 0)) ^ 2 * (Fintype.card ↥(Y.erase 0)).factorial : ℕ) : ℝ) * η
        ≤ (G : ℝ) * (((k + 3) ^ 2 * (k + 3).factorial : ℕ) : ℝ) * η :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h4 hG0) hη
    have h6 : (((k + 3) ^ 2 * (k + 3).factorial + 3 : ℕ) : ℝ)
        = (((k + 3) ^ 2 * (k + 3).factorial : ℕ) : ℝ) + 3 := by push_cast; ring
    rw [h6] at hvis
    have h7 : 0 ≤ (G : ℝ) * η := mul_nonneg hG0 hη
    nlinarith
  have := near_card_le (W := ↥(Y.erase 0)) (ι := Option (Fin R))
    (fun v => yhat x' 0 (v : Fin (k + 3))) (fun v s => abs_yhat_queryMat_le x _ s)
    (fun _ => Hhat t β₀) (fun v => (2 : ℤ) • β v) η hη hdiag (fun u v h => hoff u v h) G (k + 3) hcard hG
    hbig
  rw [Fintype.card_coe, Fintype.card_option, Fintype.card_fin] at this
  exact this

open scoped Classical in
/-- Lemma 4: few vertices have `G w^v` outside a subgroup of `ℤ^R` that contains all label vectors. -/
theorem visible_card (x : Fin R → Fin (k + 3) → Bool) (L : AddSubgroup (Fin R → ℤ))
    (G : ℕ) (hG : ∀ d : ℕ, 1 ≤ d → d ≤ k + 3 → d ∣ G)
    (hlab : ∀ j : LabelIdx k, (fun s => cut (b j) (x s)) ∈ L) :
    (univ.filter fun v : Fin (k + 3) => (G : ℤ) • (fun s => cut (shiftVec v) (x s)) ∉ L).card
      ≤ 2 * R + 3 := by
  apply card_le_of_erase_zero
  set Y := univ.filter fun v : Fin (k + 3) => (G : ℤ) • (fun s => cut (shiftVec v) (x s)) ∉ L with hY
  set x' := queryMat x with hx'
  have hv0 : ∀ v : ↥(Y.erase 0), (v : Fin (k + 3)) ≠ 0 := fun v => (mem_erase.mp v.2).1
  have hcard : Fintype.card ↥(Y.erase 0) ≤ k + 3 := by
    rw [Fintype.card_coe]
    simpa using card_le_univ (Y.erase 0)
  have hbin := queryMat_binary x
  have hforms : ∀ u : ↥(Y.erase 0), ∃ (t : Fin R → AddCircle (1 : ℚ)) (β : Fin (k + 3) → AddCircle (1 : ℚ)),
      (∀ a b, a ≠ b → cutSum x' t a b = β a + β b) ∧ (G : ℤ) • ((2 : ℤ) • β u) ≠ 0 := by
    intro u
    have hmem : (u : Fin (k + 3)) ∈ Y := (mem_erase.mp u.2).2
    have hvis := (mem_filter.mp hmem).2
    refine exists_forms x' 0 1 2 L (fun a c ha hc hac => labelVec_mem x L hlab a c ha hc hac) (G : ℤ) u
      (helperA u) (helperC u) (helperA_ne _) (helperC_ne _) (helperA_ne_helperC _) ?_
    rw [hx', vertexVec_queryMat]
    exact hvis
  choose t β hF hne using hforms
  have hF0 : ∀ (u : ↥(Y.erase 0)) (a c : Fin (k + 3)), a ≠ c →
      cutSum x' (t u) a c = β u a + β u c + (fun _ _ => (0 : AddCircle (1 : ℚ))) a c :=
    fun u a c h => by simpa using hF u a c h
  have := exact_card_le (W := ↥(Y.erase 0)) (ι := Option (Fin R))
    (fun v => yhat x' 0 (v : Fin (k + 3))) (fun v s => abs_yhat_queryMat_le x _ s)
    (fun u => Hhat (t u) (β u 0)) (fun u => (2 : ℤ) • β u u)
    (fun u => by
      have := pr_yhat_diag x' (t u) (β u) (fun _ _ => 0) 0 hbin (hF0 u) (hv0 u)
      change pr (yhat x' 0) (Hhat (t u) (β u 0)) (u : Fin (k + 3)) (u : Fin (k + 3)) = _
      simpa using this)
    (fun u v huv => by
      have hne' : (u : Fin (k + 3)) ≠ v := fun h => huv (Subtype.ext h)
      have := pr_yhat_offdiag x' (t u) (β u) (fun _ _ => 0) 0 (fun s => hbin s 0) (hF0 u) hne' (hv0 u) (hv0 v)
      change pr (yhat x' 0) (Hhat (t u) (β u 0)) (u : Fin (k + 3)) (v : Fin (k + 3)) = _
      simpa using this)
    (G : ℤ) (k + 3) hcard (fun d h1 h2 => Int.natCast_dvd_natCast.mpr (hG d h1 h2)) hne
  rw [Fintype.card_coe, Fintype.card_option, Fintype.card_fin] at this
  exact this

end CutQuery
