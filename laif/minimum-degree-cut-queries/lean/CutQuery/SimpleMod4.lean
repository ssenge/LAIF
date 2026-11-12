import CutQuery.Modular

/-!
# Simple graphs with cut answers modulo 4

Vertices `v_ℓ, a_ℓ, c_ℓ` for `ℓ < L`, the rest public. The base graph is a clique on the `v_ℓ` and a clique on all
other vertices. For `ℓ ≤ m` the gadget `gad ℓ m = e(v_ℓ c_m) + e(a_ℓ v_m) - e(v_ℓ v_m) - e(a_ℓ c_m)` is switched on by
the bit `U ℓ m`. At `ℓ = m` it raises the degree of `v_ℓ` by 2, and at `ℓ < m` it keeps all degrees. On any vertex set
`x` it contributes `2 Y_ℓ Q_m`, with `Y_ℓ = x(v_ℓ) - x(a_ℓ)` and `Q_m = x(v_m) - x(c_m)`.
-/

open Finset

namespace CutQuery

section Rank

variable {L : ℕ} {σ : Type*} [Fintype σ]

/-- A product of two matrices with `|σ|` columns between them, vanishing strictly above the diagonal, has at most
`|σ|` nonzero diagonal entries. -/
theorem card_diag_le (P Q : σ → Fin L → ZMod 2) (hup : ∀ ℓ m, ℓ < m → ∑ s, P s ℓ * Q s m = 0) :
    (univ.filter fun ℓ => ∑ s, P s ℓ * Q s ℓ ≠ 0).card ≤ Fintype.card σ := by
  classical
  let Z : Finset (Fin L) := univ.filter fun ℓ => ∑ s, P s ℓ * Q s ℓ ≠ 0
  let A : Matrix Z σ (ZMod 2) := fun ℓ s => P s ℓ
  let B : Matrix σ Z (ZMod 2) := fun s m => Q s m
  have hAB : ∀ ℓ m, (A * B) ℓ m = ∑ s, P s ℓ * Q s m := fun ℓ m => by rw [Matrix.mul_apply]
  have hdet : (A * B).det = ∏ ℓ, (A * B) ℓ ℓ := by
    refine Matrix.det_of_isLowerTriangular _ fun i j hij => ?_
    rw [hAB]
    exact hup _ _ hij
  have hne : (A * B).det ≠ 0 := by
    rw [hdet]
    refine prod_ne_zero_iff.mpr fun ℓ _ => ?_
    rw [hAB]
    exact (mem_filter.mp ℓ.2).2
  have hu : IsUnit (A * B) := (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hne)
  have hr := Matrix.rank_of_isUnit _ hu
  have h1 := Matrix.rank_mul_le_left A B
  have h2 := Matrix.rank_le_card_width A
  rw [hr] at h1
  have hc : Fintype.card Z = Z.card := Fintype.card_coe Z
  change Z.card ≤ _
  omega

end Rank

section Graph

variable {k L : ℕ} (hL : 3 * L ≤ k + 3)

/-- The vertex `v_ℓ`. -/
def vV (ℓ : Fin L) : Fin (k + 3) := ⟨ℓ, by omega⟩

/-- The vertex `a_ℓ`. -/
def vA (ℓ : Fin L) : Fin (k + 3) := ⟨L + ℓ, by omega⟩

/-- The vertex `c_ℓ`. -/
def vC (ℓ : Fin L) : Fin (k + 3) := ⟨2 * L + ℓ, by omega⟩

/-- The gadget for `ℓ ≤ m`. -/
def gad (ℓ m : Fin L) : Weights (k + 3) :=
  pairVec (vV hL ℓ) (vC hL m) + pairVec (vA hL ℓ) (vV hL m) - pairVec (vV hL ℓ) (vV hL m)
    - pairVec (vA hL ℓ) (vC hL m)

/-- The base graph: a clique on the first `L` vertices and a clique on the others. -/
def base (k L : ℕ) : Weights (k + 3) := fun e => if (e.1.1.val < L ↔ e.1.2.val < L) then 1 else 0

/-- The coefficient of a gadget: `U ℓ m` on and above the diagonal. -/
def coef (U : Fin L → Fin L → Bool) (ℓ m : Fin L) : ℤ := if ℓ ≤ m then bitZ (U ℓ m) else 0

/-- The graph with bits `U`. -/
def tri (U : Fin L → Fin L → Bool) : Weights (k + 3) :=
  base k L + ∑ ℓ, ∑ m, coef U ℓ m • gad hL ℓ m

theorem cut_gad (ℓ m : Fin L) (x : Fin (k + 3) → Bool) :
    cut (gad hL ℓ m) x = 2 * ((bitZ (x (vV hL ℓ)) - bitZ (x (vA hL ℓ))) * (bitZ (x (vV hL m)) - bitZ (x (vC hL m)))) := by
  unfold gad
  rw [cut_sub, cut_sub, cut_add]
  simp only [cut_pairVec]
  cases x (vV hL ℓ) <;> cases x (vA hL ℓ) <;> cases x (vV hL m) <;> cases x (vC hL m) <;> simp [bitZ]

theorem cut_tri (U : Fin L → Fin L → Bool) (x : Fin (k + 3) → Bool) :
    cut (tri hL U) x = cut (base k L) x + ∑ ℓ, ∑ m, coef U ℓ m * cut (gad hL ℓ m) x := by
  unfold tri
  rw [cut_add, cut_sum]
  congr 1
  refine sum_congr rfl fun ℓ _ => ?_
  rw [cut_sum]
  exact sum_congr rfl fun m _ => cut_zsmul _ _ _

omit hL in
theorem ind_or {n : ℕ} (w u v : Fin n) (h : u ≠ v) :
    (if w = u ∨ w = v then (1 : ℤ) else 0) = (if w = u then 1 else 0) + (if w = v then 1 else 0) := by
  by_cases h1 : w = u
  · subst h1
    simp [h]
  · simp [h1]

theorem vV_ne_vA (ℓ m : Fin L) : vV hL ℓ ≠ vA hL m := by
  intro h
  have := congrArg Fin.val h
  simp only [vV, vA] at this
  omega

theorem vV_ne_vC (ℓ m : Fin L) : vV hL ℓ ≠ vC hL m := by
  intro h
  have := congrArg Fin.val h
  simp only [vV, vC] at this
  omega

theorem vA_ne_vC (ℓ m : Fin L) : vA hL ℓ ≠ vC hL m := by
  intro h
  have := congrArg Fin.val h
  simp only [vA, vC] at this
  omega

theorem vV_inj {ℓ m : Fin L} (h : vV hL ℓ = vV hL m) : ℓ = m := by
  have := congrArg Fin.val h
  simp only [vV] at this
  exact Fin.ext this

theorem degree_gad (ℓ m : Fin L) (w : Fin (k + 3)) :
    degree (gad hL ℓ m) w = if ℓ = m ∧ w = vV hL ℓ then 2 else 0 := by
  unfold gad
  rw [degree_sub, degree_sub, degree_add, degree_pairVec (vV_ne_vC hL ℓ m),
    degree_pairVec (vV_ne_vA hL m ℓ).symm, degree_pairVec (vA_ne_vC hL ℓ m),
    ind_or _ _ _ (vV_ne_vC hL ℓ m), ind_or _ _ _ (vV_ne_vA hL m ℓ).symm, ind_or _ _ _ (vA_ne_vC hL ℓ m)]
  by_cases hlm : ℓ = m
  · subst hlm
    rw [pairVec_self]
    have hz : degree (0 : Weights (k + 3)) w = 0 := by simp [degree]
    rw [hz]
    by_cases hw : w = vV hL ℓ
    · simp only [hw, true_and, ite_true]
      ring
    · simp only [hw, true_and, ite_false]
      ring
  · have hne : vV hL ℓ ≠ vV hL m := fun h => hlm (vV_inj hL h)
    rw [degree_pairVec hne, ind_or _ _ _ hne]
    simp only [hlm, false_and, ite_false]
    ring

/-- The degree of the base graph. -/
theorem degree_base (w : Fin (k + 3)) (hLk : L ≤ k + 3) :
    degree (base k L) w = if w.val < L then (L : ℤ) - 1 else (k : ℤ) + 2 - L := by
  classical
  have hsym : ∀ a b : Fin (k + 3), a ≠ b →
      (if (a.val < L ↔ b.val < L) then (1 : ℤ) else 0) = if (b.val < L ↔ a.val < L) then 1 else 0 := by
    intro a b _
    simp only [iff_comm]
  have h := degree_of_symm (fun a b : Fin (k + 3) => if (a.val < L ↔ b.val < L) then (1 : ℤ) else 0) hsym w
  have hb : base k L = fun e : Edge (k + 3) => if (e.1.1.val < L ↔ e.1.2.val < L) then (1 : ℤ) else 0 := rfl
  rw [hb, h, sum_boole]
  have hcard : (univ.filter fun u : Fin (k + 3) => u.val < L).card = L := by
    rw [Fin.card_filter_val_lt]
    omega
  have hcompl : (univ.filter fun u : Fin (k + 3) => ¬ u.val < L).card = k + 3 - L := by
    have := card_filter_add_card_filter_not (s := (univ : Finset (Fin (k + 3)))) (fun u => u.val < L)
    simp only [card_univ, Fintype.card_fin] at this
    omega
  by_cases hw : w.val < L
  · have hf : ((univ.erase w).filter fun u : Fin (k + 3) => (u.val < L ↔ w.val < L))
        = (univ.filter fun u : Fin (k + 3) => u.val < L).erase w := by
      ext u
      simp [hw, and_comm]
    have hm : w ∈ univ.filter fun u : Fin (k + 3) => u.val < L := mem_filter.mpr ⟨mem_univ _, hw⟩
    rw [hf, card_erase_of_mem hm, hcard]
    simp only [hw, ↓reduceIte]
    have : 0 < L := by omega
    push_cast [Nat.cast_sub (show 1 ≤ L by omega)]
    ring
  · have hf : ((univ.erase w).filter fun u : Fin (k + 3) => (u.val < L ↔ w.val < L))
        = (univ.filter fun u : Fin (k + 3) => ¬ u.val < L).erase w := by
      ext u
      simp [hw, and_comm]
    have hm : w ∈ univ.filter fun u : Fin (k + 3) => ¬ u.val < L := mem_filter.mpr ⟨mem_univ _, hw⟩
    rw [hf, card_erase_of_mem hm, hcompl]
    simp only [hw, ↓reduceIte]
    have : 0 < k + 3 - L := by omega
    rw [Nat.cast_sub (by omega), Nat.cast_sub hLk]
    push_cast
    ring

/-- The degree of the graph with bits `U`. -/
theorem degree_tri (U : Fin L → Fin L → Bool) (w : Fin (k + 3)) :
    degree (tri hL U) w = degree (base k L) w
      + ∑ ℓ, if w = vV hL ℓ then 2 * bitZ (U ℓ ℓ) else 0 := by
  unfold tri
  rw [degree_add, degree_sum]
  congr 1
  refine sum_congr rfl fun ℓ _ => ?_
  rw [degree_sum]
  simp_rw [degree_zsmul, degree_gad]
  rw [sum_eq_single ℓ]
  · by_cases hw : w = vV hL ℓ
    · simp [hw, coef]
      ring
    · simp [hw]
  · intro m _ hm
    simp [hm.symm]
  · simp

omit hL in
theorem pair_val {u v : Fin (k + 3)} (huv : u < v) (e : Edge (k + 3)) (h : pairVec u v e ≠ 0) :
    e.1.1 = u ∧ e.1.2 = v := by
  unfold pairVec at h
  by_cases h1 : e.1.1 = u ∧ e.1.2 = v
  · exact h1
  · by_cases h2 : e.1.1 = v ∧ e.1.2 = u
    · have := e.2
      rw [h2.1, h2.2] at this
      exact absurd this (not_lt_of_gt huv)
    · simp [h1, h2] at h

omit hL in
theorem pair_zero_or_one (u v : Fin (k + 3)) (e : Edge (k + 3)) : pairVec u v e = 0 ∨ pairVec u v e = 1 := by
  unfold pairVec
  split_ifs <;> simp

omit hL in
theorem coef_zero_or_one (U : Fin L → Fin L → Bool) (ℓ m : Fin L) : coef U ℓ m = 0 ∨ coef U ℓ m = 1 := by
  unfold coef bitZ
  split_ifs <;> simp

omit hL in
/-- A sum of coefficients over indicators with at most one nonzero term is `0` or `1`. -/
theorem sum_coef_ind (U : Fin L → Fin L → Bool) (f : Fin L → Fin L → ℤ) (hf : ∀ ℓ m, f ℓ m = 0 ∨ f ℓ m = 1)
    (huniq : ∀ ℓ m ℓ' m', f ℓ m ≠ 0 → f ℓ' m' ≠ 0 → ℓ = ℓ' ∧ m = m') :
    ∑ ℓ, ∑ m, coef U ℓ m * f ℓ m = 0 ∨ ∑ ℓ, ∑ m, coef U ℓ m * f ℓ m = 1 := by
  classical
  by_cases hex : ∃ ℓ m, f ℓ m ≠ 0
  · obtain ⟨ℓ, m, hne⟩ := hex
    have h1 : f ℓ m = 1 := (hf ℓ m).resolve_left hne
    have hz : ∀ ℓ' m', (ℓ', m') ≠ (ℓ, m) → f ℓ' m' = 0 := by
      intro ℓ' m' h
      by_contra h'
      obtain ⟨h1', h2'⟩ := huniq ℓ' m' ℓ m h' hne
      exact h (by rw [h1', h2'])
    have hS : ∑ ℓ', ∑ m', coef U ℓ' m' * f ℓ' m' = coef U ℓ m := by
      rw [sum_eq_single ℓ, sum_eq_single m]
      · rw [h1, mul_one]
      · intro m' _ hm'
        rw [hz ℓ m' (by simp [hm']), mul_zero]
      · simp
      · intro ℓ' _ hℓ'
        refine sum_eq_zero fun m' _ => ?_
        rw [hz ℓ' m' (by simp [hℓ']), mul_zero]
      · simp
    rw [hS]
    exact coef_zero_or_one U ℓ m
  · push Not at hex
    left
    exact sum_eq_zero fun ℓ _ => sum_eq_zero fun m _ => by rw [hex ℓ m, mul_zero]

/-- The graph with bits `U` is simple. -/
theorem isSimple_tri (U : Fin L → Fin L → Bool) : IsSimple (tri hL U) := by
  classical
  intro e
  have hpq : e.1.1.val < e.1.2.val := e.2
  let f1 : Fin L → Fin L → ℤ := fun ℓ m => pairVec (vV hL ℓ) (vC hL m) e
  let f2 : Fin L → Fin L → ℤ := fun ℓ m => pairVec (vA hL ℓ) (vV hL m) e
  let f3 : Fin L → Fin L → ℤ := fun ℓ m => if ℓ < m then pairVec (vV hL ℓ) (vV hL m) e else 0
  let f4 : Fin L → Fin L → ℤ := fun ℓ m => pairVec (vA hL ℓ) (vC hL m) e
  have v1 : ∀ ℓ m, f1 ℓ m ≠ 0 → e.1.1.val = ℓ.val ∧ e.1.2.val = 2 * L + m.val := by
    intro ℓ m h
    have hlt : vV hL ℓ < vC hL m := by
      rw [Fin.lt_def]
      simp only [vV, vC]
      omega
    obtain ⟨h1, h2⟩ := pair_val hlt e h
    rw [h1, h2]
    exact ⟨rfl, rfl⟩
  have v2 : ∀ ℓ m, f2 ℓ m ≠ 0 → e.1.1.val = m.val ∧ e.1.2.val = L + ℓ.val := by
    intro ℓ m h
    have hlt : vV hL m < vA hL ℓ := by
      rw [Fin.lt_def]
      simp only [vV, vA]
      omega
    have h' : pairVec (vV hL m) (vA hL ℓ) e ≠ 0 := by rwa [pairVec_comm]
    obtain ⟨h1, h2⟩ := pair_val hlt e h'
    rw [h1, h2]
    exact ⟨rfl, rfl⟩
  have v3 : ∀ ℓ m, f3 ℓ m ≠ 0 → e.1.1.val = ℓ.val ∧ e.1.2.val = m.val := by
    intro ℓ m h
    by_cases hlm : ℓ < m
    · have hlt : vV hL ℓ < vV hL m := by
        rw [Fin.lt_def]
        exact hlm
      have h' : pairVec (vV hL ℓ) (vV hL m) e ≠ 0 := by simpa [f3, hlm] using h
      obtain ⟨h1, h2⟩ := pair_val hlt e h'
      rw [h1, h2]
      exact ⟨rfl, rfl⟩
    · simp [f3, hlm] at h
  have v4 : ∀ ℓ m, f4 ℓ m ≠ 0 → e.1.1.val = L + ℓ.val ∧ e.1.2.val = 2 * L + m.val := by
    intro ℓ m h
    have hlt : vA hL ℓ < vC hL m := by
      rw [Fin.lt_def]
      simp only [vA, vC]
      omega
    obtain ⟨h1, h2⟩ := pair_val hlt e h
    rw [h1, h2]
    exact ⟨rfl, rfl⟩
  have s1 := sum_coef_ind U f1 (fun ℓ m => pair_zero_or_one _ _ e) (fun ℓ m ℓ' m' h h' => by
    have a := v1 ℓ m h
    have b := v1 ℓ' m' h'
    exact ⟨Fin.ext (by omega), Fin.ext (by omega)⟩)
  have s2 := sum_coef_ind U f2 (fun ℓ m => pair_zero_or_one _ _ e) (fun ℓ m ℓ' m' h h' => by
    have a := v2 ℓ m h
    have b := v2 ℓ' m' h'
    exact ⟨Fin.ext (by omega), Fin.ext (by omega)⟩)
  have s3 := sum_coef_ind U f3 (fun ℓ m => by
      simp only [f3]
      split_ifs
      · exact pair_zero_or_one _ _ e
      · exact Or.inl rfl) (fun ℓ m ℓ' m' h h' => by
    have a := v3 ℓ m h
    have b := v3 ℓ' m' h'
    exact ⟨Fin.ext (by omega), Fin.ext (by omega)⟩)
  have s4 := sum_coef_ind U f4 (fun ℓ m => pair_zero_or_one _ _ e) (fun ℓ m ℓ' m' h h' => by
    have a := v4 ℓ m h
    have b := v4 ℓ' m' h'
    exact ⟨Fin.ext (by omega), Fin.ext (by omega)⟩)
  have hentry : tri hL U e = base k L e + ∑ ℓ, ∑ m, coef U ℓ m * f1 ℓ m + ∑ ℓ, ∑ m, coef U ℓ m * f2 ℓ m
      - ∑ ℓ, ∑ m, coef U ℓ m * f3 ℓ m - ∑ ℓ, ∑ m, coef U ℓ m * f4 ℓ m := by
    have hg : ∀ ℓ m, coef U ℓ m * gad hL ℓ m e
        = coef U ℓ m * f1 ℓ m + coef U ℓ m * f2 ℓ m - coef U ℓ m * f3 ℓ m - coef U ℓ m * f4 ℓ m := by
      intro ℓ m
      rcases lt_trichotomy ℓ m with h | h | h
      · simp only [gad, f1, f2, f3, f4, h, ↓reduceIte, Pi.sub_apply, Pi.add_apply]
        ring
      · subst h
        simp only [gad, f1, f2, f3, f4, lt_irrefl, ↓reduceIte, Pi.sub_apply, Pi.add_apply, pairVec_self,
          Pi.zero_apply]
        ring
      · have hc : coef U ℓ m = 0 := by simp [coef, not_le.mpr h]
        simp [hc]
    have ht : tri hL U e = base k L e + ∑ ℓ, ∑ m, coef U ℓ m * gad hL ℓ m e := by
      simp [tri, Finset.sum_apply]
    rw [ht]
    simp_rw [hg, sum_sub_distrib, sum_add_distrib]
    ring
  have z1 : (∀ ℓ m, f1 ℓ m = 0) → ∑ ℓ, ∑ m, coef U ℓ m * f1 ℓ m = 0 := fun h =>
    sum_eq_zero fun ℓ _ => sum_eq_zero fun m _ => by rw [h, mul_zero]
  have z2 : (∀ ℓ m, f2 ℓ m = 0) → ∑ ℓ, ∑ m, coef U ℓ m * f2 ℓ m = 0 := fun h =>
    sum_eq_zero fun ℓ _ => sum_eq_zero fun m _ => by rw [h, mul_zero]
  have z3 : (∀ ℓ m, f3 ℓ m = 0) → ∑ ℓ, ∑ m, coef U ℓ m * f3 ℓ m = 0 := fun h =>
    sum_eq_zero fun ℓ _ => sum_eq_zero fun m _ => by rw [h, mul_zero]
  have z4 : (∀ ℓ m, f4 ℓ m = 0) → ∑ ℓ, ∑ m, coef U ℓ m * f4 ℓ m = 0 := fun h =>
    sum_eq_zero fun ℓ _ => sum_eq_zero fun m _ => by rw [h, mul_zero]
  have nz : ∀ (f : Fin L → Fin L → ℤ) (P : Prop), (∀ ℓ m, f ℓ m ≠ 0 → P) → ¬ P → ∀ ℓ m, f ℓ m = 0 := by
    intro f P h hP ℓ m
    by_contra h'
    exact hP (h ℓ m h')
  have hmL : ∀ m : Fin L, m.val < L := fun m => m.2
  by_cases hp : e.1.1.val < L
  · by_cases hq : e.1.2.val < L
    · have b1 : base k L e = 1 := by simp [base, hp, hq]
      have e1 := z1 (nz f1 (e.1.2.val ≥ 2 * L) (fun ℓ m h => by have := v1 ℓ m h; omega) (by omega))
      have e2 := z2 (nz f2 (e.1.2.val ≥ L) (fun ℓ m h => by have := v2 ℓ m h; omega) (by omega))
      have e4 := z4 (nz f4 (e.1.1.val ≥ L) (fun ℓ m h => by have := v4 ℓ m h; omega) (by omega))
      rw [hentry, b1, e1, e2, e4]
      rcases s3 with h | h <;> rw [h] <;> simp
    · have b1 : base k L e = 0 := by simp [base, hp, hq]
      have e3 := z3 (nz f3 (e.1.2.val < L) (fun ℓ m h => by have := v3 ℓ m h; have := hmL m; omega) hq)
      have e4 := z4 (nz f4 (e.1.1.val ≥ L) (fun ℓ m h => by have := v4 ℓ m h; omega) (by omega))
      by_cases hq2 : e.1.2.val < 2 * L
      · have e1 := z1 (nz f1 (e.1.2.val ≥ 2 * L) (fun ℓ m h => by have := v1 ℓ m h; omega) (by omega))
        rw [hentry, b1, e1, e3, e4]
        rcases s2 with h | h <;> rw [h] <;> simp
      · have e2 := z2 (nz f2 (e.1.2.val < 2 * L)
          (fun ℓ m h => by have := v2 ℓ m h; have := hmL ℓ; omega) hq2)
        rw [hentry, b1, e2, e3, e4]
        rcases s1 with h | h <;> rw [h] <;> simp
  · have hq : ¬ e.1.2.val < L := by omega
    have b1 : base k L e = 1 := by simp [base, hp, hq]
    have e1 := z1 (nz f1 (e.1.1.val < L) (fun ℓ m h => by have := v1 ℓ m h; have := hmL ℓ; omega) hp)
    have e2 := z2 (nz f2 (e.1.1.val < L) (fun ℓ m h => by have := v2 ℓ m h; have := hmL m; omega) hp)
    have e3 := z3 (nz f3 (e.1.1.val < L) (fun ℓ m h => by have := v3 ℓ m h; have := hmL ℓ; omega) hp)
    rw [hentry, b1, e1, e2, e3]
    rcases s4 with h | h <;> rw [h] <;> simp

/-- The degree of `v_ℓ`. -/
theorem degree_tri_v (U : Fin L → Fin L → Bool) (ℓ : Fin L) :
    degree (tri hL U) (vV hL ℓ) = (L : ℤ) - 1 + 2 * bitZ (U ℓ ℓ) := by
  have hle : L ≤ k + 3 := by omega
  rw [degree_tri, degree_base _ hle]
  have hlt : (vV hL ℓ).val < L := ℓ.2
  simp only [hlt, ↓reduceIte]
  rw [sum_eq_single ℓ]
  · simp
  · intro m _ hm
    have hne : vV hL ℓ ≠ vV hL m := fun h => hm (vV_inj hL h).symm
    simp [hne]
  · simp

/-- The degree of any other vertex. -/
theorem degree_tri_other (U : Fin L → Fin L → Bool) (w : Fin (k + 3)) (hw : ¬ w.val < L) :
    degree (tri hL U) w = (k : ℤ) + 2 - L := by
  have hle : L ≤ k + 3 := by omega
  rw [degree_tri, degree_base _ hle]
  simp only [hw, ↓reduceIte]
  rw [sum_eq_zero, add_zero]
  intro m _
  have hne : w ≠ vV hL m := fun h => hw (by rw [h]; exact m.2)
  simp [hne]

/-- All vertices have degree at least the value of `deg`, which is attained. -/
theorem minDegree_eq {n : ℕ} [NeZero n] (A : Weights n) (D : ℤ) (h1 : ∀ w, D ≤ degree A w) (w : Fin n)
    (h2 : degree A w = D) : minDegree A = D := by
  unfold minDegree
  refine le_antisymm ?_ (le_inf' _ _ fun w _ => h1 w)
  rw [← h2]
  exact inf'_le _ (mem_univ w)

/-- With a diagonal bit unset the minimum degree is `L - 1`. -/
theorem minDegree_low [NeZero (k + 3)] (U : Fin L → Fin L → Bool) (ℓ : Fin L) (hℓ : U ℓ ℓ = false) (hL2 : 2 ≤ L) :
    minDegree (tri hL U) = (L : ℤ) - 1 := by
  refine minDegree_eq _ _ (fun w => ?_) (vV hL ℓ) (by rw [degree_tri_v, hℓ]; simp [bitZ])
  by_cases hw : w.val < L
  · have hv : w = vV hL ⟨w.val, hw⟩ := Fin.ext rfl
    rw [hv, degree_tri_v]
    have : 0 ≤ bitZ (U ⟨w.val, hw⟩ ⟨w.val, hw⟩) := by unfold bitZ; split_ifs <;> simp
    linarith
  · rw [degree_tri_other hL U w hw]
    have : (3 : ℤ) * L ≤ k + 3 := by exact_mod_cast hL
    linarith

/-- With all diagonal bits set the minimum degree is `L + 1`. -/
theorem minDegree_high [NeZero (k + 3)] (U : Fin L → Fin L → Bool) (hU : ∀ ℓ, U ℓ ℓ = true) (hL2 : 2 ≤ L) :
    minDegree (tri hL U) = (L : ℤ) + 1 := by
  have hv0 : degree (tri hL U) (vV hL ⟨0, by omega⟩) = (L : ℤ) + 1 := by
    rw [degree_tri_v, hU]
    simp [bitZ]
    ring
  refine minDegree_eq _ _ (fun w => ?_) _ hv0
  by_cases hw : w.val < L
  · have hv : w = vV hL ⟨w.val, hw⟩ := Fin.ext rfl
    rw [hv, degree_tri_v, hU]
    simp [bitZ]
    linarith
  · rw [degree_tri_other hL U w hw]
    have h3 : (3 : ℤ) * L ≤ k + 3 := by exact_mod_cast hL
    have h2 : (2 : ℤ) ≤ L := by exact_mod_cast hL2
    linarith

end Graph

section Characters

local notation "ω" => ZMod.stdAddChar

/-- `ω (2 t)` in `ZMod 4`. -/
noncomputable def sg (t : ℤ) : ℂ := ω (((2 * t : ℤ) : ZMod 4))

theorem sg_even {t : ℤ} (ht : ((t : ℤ) : ZMod 2) = 0) : sg t = 1 := by
  obtain ⟨r, rfl⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd t 2).mp ht
  have h : ((2 * (((2 : ℕ) : ℤ) * r) : ℤ) : ZMod 4) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ 4).mpr ⟨r, by push_cast; ring⟩
  unfold sg
  rw [h, AddChar.map_zero_eq_one]

theorem sg_odd {t : ℤ} (ht : ((t : ℤ) : ZMod 2) ≠ 0) : sg t = -1 := by
  have h2 : ¬ (2 : ℤ) ∣ t := fun h => ht ((ZMod.intCast_zmod_eq_zero_iff_dvd t 2).mpr (by exact_mod_cast h))
  obtain ⟨r, hr⟩ : ∃ r, t = 2 * r + 1 := ⟨t / 2, by omega⟩
  have hc : ((2 * t : ℤ) : ZMod 4) = ((2 : ℤ) : ZMod 4) :=
    (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ 4).mpr ⟨-r, by rw [hr]; push_cast; ring⟩
  unfold sg
  rw [hc, ZMod.stdAddChar_coe]
  have he : (2 * (Real.pi : ℂ) * Complex.I * ((2 : ℤ) : ℂ) / ((4 : ℕ) : ℂ)) = Real.pi * Complex.I := by
    push_cast
    ring
  rw [he, Complex.exp_pi_mul_I]

variable {L : ℕ}

/-- The bits with diagonal `h` and off-diagonal part `a`. -/
def mkU (h : Fin L → Bool) (a : Fin L × Fin L → Bool) : Fin L → Fin L → Bool :=
  fun ℓ m => if ℓ = m then h ℓ else a (ℓ, m)

/-- The factor of a diagonal bit. -/
noncomputable def dgF (M : Fin L → Fin L → ℤ) (h : Fin L → Bool) (ℓ : Fin L) : ℂ :=
  if h ℓ then sg (M ℓ ℓ) else 1

/-- The factor of an off-diagonal bit. -/
noncomputable def offF (M : Fin L → Fin L → ℤ) (o : Fin L × Fin L) (b : Bool) : ℂ :=
  if o.1 < o.2 then (if b then sg (M o.1 o.2) else 1) else 1

theorem char_coef (M : Fin L → Fin L → ℤ) (h : Fin L → Bool) (a : Fin L × Fin L → Bool) :
    ω (((∑ ℓ, ∑ m, coef (mkU h a) ℓ m * (2 * M ℓ m) : ℤ)) : ZMod 4)
      = (∏ ℓ, dgF M h ℓ) * ∏ o, offF M o (a o) := by
  classical
  rw [← Fintype.sum_prod_type' (fun ℓ m => coef (mkU h a) ℓ m * (2 * M ℓ m)), Int.cast_sum, char_sum]
  have hD : ∏ ℓ, dgF M h ℓ = ∏ o : Fin L × Fin L, if o.1 = o.2 then dgF M h o.1 else 1 := by
    rw [Fintype.prod_prod_type]
    refine prod_congr rfl fun ℓ _ => ?_
    rw [prod_eq_single ℓ]
    · simp
    · intro m _ hm
      simp [hm.symm]
    · simp
  rw [hD, ← prod_mul_distrib]
  refine prod_congr rfl fun o _ => ?_
  obtain ⟨ℓ, m⟩ := o
  rcases lt_trichotomy ℓ m with hlm | hlm | hlm
  · have hne : ℓ ≠ m := hlm.ne
    cases hb : a (ℓ, m)
    · simp [coef, mkU, hne, hlm.le, hb, offF, hlm, bitZ]
    · simp [coef, mkU, hne, hlm.le, hb, offF, hlm, bitZ, sg]
  · subst hlm
    cases hb : h ℓ
    · simp [coef, mkU, hb, dgF, offF, bitZ]
    · simp [coef, mkU, hb, dgF, offF, bitZ, sg]
  · have hne : ℓ ≠ m := hlm.ne'
    simp [coef, not_le.mpr hlm, hne, offF, not_lt.mpr hlm.le]

/-- Averaging over the off-diagonal bits keeps exactly the terms with even entries above the diagonal. -/
theorem avg_off (M : Fin L → Fin L → ℤ) :
    ((2 : ℂ) ^ Fintype.card (Fin L × Fin L))⁻¹ * ∑ a : Fin L × Fin L → Bool, ∏ o, offF M o (a o)
      = if (∀ ℓ m, ℓ < m → ((M ℓ m : ℤ) : ZMod 2) = 0) then 1 else 0 := by
  classical
  have hsum : ∑ a : Fin L × Fin L → Bool, ∏ o, offF M o (a o) = ∏ o, (offF M o true + offF M o false) := by
    have := prod_univ_sum (fun _ : Fin L × Fin L => (univ : Finset Bool)) (fun o b => offF M o b)
    simp only [Fintype.piFinset_univ, Fintype.sum_bool] at this
    exact this.symm
  rw [hsum]
  split_ifs with hg
  · have h2 : ∀ o : Fin L × Fin L, offF M o true + offF M o false = 2 := by
      intro o
      by_cases ho : o.1 < o.2
      · simp only [offF, ho, ↓reduceIte, sg_even (hg _ _ ho)]
        norm_num
      · simp only [offF, ho, ↓reduceIte]
        norm_num
    simp_rw [h2]
    rw [prod_const, card_univ]
    exact inv_mul_cancel₀ (pow_ne_zero _ two_ne_zero)
  · push Not at hg
    obtain ⟨ℓ, m, hlm, hodd⟩ := hg
    rw [prod_eq_zero (mem_univ (ℓ, m)), mul_zero]
    simp [offF, hlm, sg_odd hodd]

/-- The polynomial in the diagonal bits. -/
theorem exists_poly_tri {ι : Type*} [Fintype ι] (M : ι → Fin L → Fin L → ℤ) (β : ι → ℂ) (d : ℕ)
    (hd : ∀ i, (∀ ℓ m, ℓ < m → ((M i ℓ m : ℤ) : ZMod 2) = 0) →
      (univ.filter fun ℓ => ((M i ℓ ℓ : ℤ) : ZMod 2) ≠ 0).card ≤ d) :
    ∃ Q : MvPolynomial (Fin L) ℂ, Q.totalDegree ≤ d ∧ ∀ h : Fin L → Bool,
      MvPolynomial.eval (fun ℓ => (bit (h ℓ) : ℂ)) Q
        = ((2 : ℂ) ^ Fintype.card (Fin L × Fin L))⁻¹ * ∑ a : Fin L × Fin L → Bool, ∑ i,
          β i * ((∏ ℓ, dgF (M i) h ℓ) * ∏ o, offF (M i) o (a o)) := by
  classical
  let Z : ι → Finset (Fin L) := fun i => univ.filter fun ℓ => ((M i ℓ ℓ : ℤ) : ZMod 2) ≠ 0
  let good : ι → Prop := fun i => ∀ ℓ m, ℓ < m → ((M i ℓ m : ℤ) : ZMod 2) = 0
  let piece : ι → MvPolynomial (Fin L) ℂ := fun i =>
    MvPolynomial.C (β i) * ∏ ℓ ∈ Z i, ((1 : MvPolynomial (Fin L) ℂ)
      + MvPolynomial.C (sg (M i ℓ ℓ) - 1) * MvPolynomial.X ℓ)
  refine ⟨∑ i, if good i then piece i else 0, ?_, fun h => ?_⟩
  · refine MvPolynomial.totalDegree_finsetSum_le fun i _ => ?_
    split_ifs with hi
    · refine (MvPolynomial.totalDegree_mul _ _).trans ?_
      simp only [MvPolynomial.totalDegree_C, zero_add]
      exact (totalDegree_prod_factor (Z i) _).trans (hd i hi)
    · simp
  · rw [sum_comm, mul_sum, map_sum]
    refine sum_congr rfl fun i _ => ?_
    have hfac : ∑ a : Fin L × Fin L → Bool, β i * ((∏ ℓ, dgF (M i) h ℓ) * ∏ o, offF (M i) o (a o))
        = β i * (∏ ℓ, dgF (M i) h ℓ) * ∑ a : Fin L × Fin L → Bool, ∏ o, offF (M i) o (a o) := by
      rw [mul_sum]
      exact sum_congr rfl fun a _ => by ring
    rw [hfac, mul_left_comm, avg_off]
    by_cases hi : good i
    · have hi' : ∀ ℓ m, ℓ < m → ((M i ℓ m : ℤ) : ZMod 2) = 0 := hi
      rw [ite_eq_left hi', ite_eq_left hi', mul_one]
      simp only [piece, map_mul, MvPolynomial.eval_C, map_prod]
      congr 1
      rw [← prod_subset (subset_univ (Z i))]
      · refine prod_congr rfl fun ℓ _ => ?_
        simp only [map_add, map_one, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X, dgF]
        cases h ℓ <;> simp [bit]
      · intro ℓ _ hℓ
        have he : ((M i ℓ ℓ : ℤ) : ZMod 2) = 0 := by
          by_contra hne
          exact hℓ (mem_filter.mpr ⟨mem_univ _, hne⟩)
        simp [dgF, sg_even he]
    · have hi' : ¬ ∀ ℓ m, ℓ < m → ((M i ℓ m : ℤ) : ZMod 2) = 0 := hi
      simp [hi, hi']

end Characters

section Chain

local notation "ω" => ZMod.stdAddChar

variable {k L : ℕ} (hL : 3 * L ≤ k + 3)

/-- `Y_ℓ` on a vertex set. -/
def Yv (x : Fin (k + 3) → Bool) (ℓ : Fin L) : ℤ := bitZ (x (vV hL ℓ)) - bitZ (x (vA hL ℓ))

/-- `Q_m` on a vertex set. -/
def Qv (x : Fin (k + 3) → Bool) (m : Fin L) : ℤ := bitZ (x (vV hL m)) - bitZ (x (vC hL m))

/-- The matrix `∑_s y_s Y^s (Q^s)^T`. -/
def MZ {σ : Type*} [Fintype σ] (x : σ → Fin (k + 3) → Bool) (y : σ → ℤ) (ℓ m : Fin L) : ℤ :=
  ∑ s, y s * (Yv hL (x s) ℓ * Qv hL (x s) m)

theorem pairing_tri {σ : Type*} [Fintype σ] (x : σ → Fin (k + 3) → Bool) (y : σ → ℤ) (U : Fin L → Fin L → Bool) :
    pairing x y (tri hL U) = pairing x y (base k L) + ∑ ℓ, ∑ m, coef U ℓ m * (2 * MZ hL x y ℓ m) := by
  unfold pairing MZ
  simp_rw [cut_tri, cut_gad, mul_add, sum_add_distrib, mul_sum]
  congr 1
  rw [sum_comm]
  refine sum_congr rfl fun ℓ _ => ?_
  rw [sum_comm]
  refine sum_congr rfl fun m _ => sum_congr rfl fun s _ => ?_
  simp only [Yv, Qv]
  ring

/-- `|{ℓ : M_ℓℓ odd}| ≤ |σ|` when `M` is even above the diagonal. -/
theorem card_odd_diag {σ : Type*} [Fintype σ] (x : σ → Fin (k + 3) → Bool) (y : σ → ℤ)
    (hup : ∀ ℓ m : Fin L, ℓ < m → ((MZ hL x y ℓ m : ℤ) : ZMod 2) = 0) :
    (univ.filter fun ℓ : Fin L => ((MZ hL x y ℓ ℓ : ℤ) : ZMod 2) ≠ 0).card ≤ Fintype.card σ := by
  classical
  have hc : ∀ ℓ m : Fin L, ((MZ hL x y ℓ m : ℤ) : ZMod 2)
      = ∑ s, (((y s * Yv hL (x s) ℓ : ℤ)) : ZMod 2) * ((Qv hL (x s) m : ℤ) : ZMod 2) := by
    intro ℓ m
    simp only [MZ]
    push_cast
    exact sum_congr rfl fun s _ => by ring
  have := card_diag_le (L := L) (fun s ℓ => (((y s * Yv hL (x s) ℓ : ℤ)) : ZMod 2))
    (fun s m => ((Qv hL (x s) m : ℤ) : ZMod 2)) (fun ℓ m hlm => by rw [← hc]; exact hup ℓ m hlm)
  simpa only [← hc] using this

variable {T : ℕ} {S : Type*} [Fintype S] [DecidableEq S]

include hL in
open scoped Classical in
/-- An algorithm correct on simple graphs with mod 4 answers gives a polynomial of degree at most `2 T` approximating
`AND_L`. -/
theorem exists_and_approx_tri [NeZero (k + 3)] (q : QAlg (k + 3) T S) (hL2 : 2 ≤ L)
    (herr : ∀ A : Weights (k + 3), IsSimple A → q.errAt 4 A (minDegree A) ≤ 1 / 3) :
    ∃ r : MvPolynomial (Fin L) ℝ, r.totalDegree ≤ 2 * T ∧
      ∀ x : Fin L → Bool,
        |MvPolynomial.eval (fun i => if x i then (1 : ℝ) else 0) r - andBool x| ≤ 1 / 3 := by
  have hNe : NeZero 4 := ⟨by norm_num⟩
  let d : ℤ := (L : ℤ) - 1
  obtain ⟨α, hα⟩ := q.exists_acc_expansion 4 d
  let X : (Fin T → S) × (Fin T → S) × S → Fin T ⊕ Fin T → Fin (k + 3) → Bool := fun i =>
    Sum.elim (fun t => q.x (i.1 t)) (fun t => q.x (i.2.1 t))
  let Y : (Fin T → S) × (Fin T → S) × S → Fin T ⊕ Fin T → ℤ := fun i =>
    Sum.elim (fun t => q.z (i.1 t)) (fun t => - q.z (i.2.1 t))
  let M : (Fin T → S) × (Fin T → S) × S → Fin L → Fin L → ℤ := fun i => MZ hL (X i) (Y i)
  let β : (Fin T → S) × (Fin T → S) × S → ℂ := fun i =>
    α i * ω ((pairing (X i) (Y i) (base k L) : ℤ) : ZMod 4)
  let A : (Fin L → Bool) → (Fin L × Fin L → Bool) → Weights (k + 3) := fun h a => tri hL (mkU h a)
  have hacc0 : ∀ h a, 0 ≤ q.acc 4 (A h a) d := fun h a => q.acc_nonneg _ _ _
  have hacc1 : ∀ h a, q.acc 4 (A h a) d ≤ 1 := fun h a => q.acc_le_one _ _ _
  have hlow : ∀ h a (ℓ : Fin L), h ℓ = false → 2 / 3 ≤ q.acc 4 (A h a) d := by
    intro h a ℓ hℓ
    have hm : minDegree (A h a) = d := minDegree_low hL _ ℓ (by simp [mkU, hℓ]) hL2
    have he := herr (A h a) (isSimple_tri hL _)
    rw [hm] at he
    have hs := q.acc_add_errAt 4 (A h a) d
    linarith
  have hhigh : ∀ a, q.acc 4 (A (fun _ => true) a) d ≤ 1 / 3 := by
    intro a
    have hm : minDegree (A (fun _ => true) a) = (L : ℤ) + 1 :=
      minDegree_high hL _ (fun ℓ => by simp [mkU]) hL2
    have he := herr (A (fun _ => true) a) (isSimple_tri hL _)
    rw [hm] at he
    exact (q.acc_le_errAt 4 _ (d := d) (d' := (L : ℤ) + 1) (by simp only [d]; omega)).trans he
  let u : ℝ := ((2 : ℝ) ^ Fintype.card (Fin L × Fin L))⁻¹
  have hu0 : 0 ≤ u := by positivity
  have hu1 : ∑ _a : Fin L × Fin L → Bool, u = 1 := by
    rw [sum_const, card_univ, Fintype.card_fun, Fintype.card_bool, nsmul_eq_mul]
    push_cast
    exact mul_inv_cancel₀ (pow_ne_zero _ two_ne_zero)
  let P : (Fin L → Bool) → ℝ := fun h => ∑ a, u * q.acc 4 (A h a) d
  have hP0 : ∀ h, 0 ≤ P h := fun h => sum_nonneg fun a _ => mul_nonneg hu0 (hacc0 h a)
  have hP1 : ∀ h, P h ≤ 1 := by
    intro h
    calc P h ≤ ∑ _a : Fin L × Fin L → Bool, u * 1 :=
          sum_le_sum fun a _ => mul_le_mul_of_nonneg_left (hacc1 h a) hu0
      _ = 1 := by simpa using hu1
  have hPlow : ∀ h (ℓ : Fin L), h ℓ = false → 2 / 3 ≤ P h := by
    intro h ℓ hℓ
    calc (2 / 3 : ℝ) = ∑ _a : Fin L × Fin L → Bool, u * (2 / 3) := by rw [← sum_mul, hu1, one_mul]
      _ ≤ P h := sum_le_sum fun a _ => mul_le_mul_of_nonneg_left (hlow h a ℓ hℓ) hu0
  have hPhigh : P (fun _ => true) ≤ 1 / 3 := by
    calc P (fun _ => true) ≤ ∑ _a : Fin L × Fin L → Bool, u * (1 / 3) :=
          sum_le_sum fun a _ => mul_le_mul_of_nonneg_left (hhigh a) hu0
      _ = 1 / 3 := by rw [← sum_mul, hu1, one_mul]
  obtain ⟨Q, hQd, hQ⟩ := exists_poly_tri (L := L) M β (2 * T) (fun i hi => by
    have hc := card_odd_diag hL (X i) (Y i) hi
    simpa [two_mul] using hc)
  have hexp : ∀ h a, ((q.acc 4 (A h a) d : ℝ) : ℂ)
      = ∑ i, β i * ((∏ ℓ, dgF (M i) h ℓ) * ∏ o, offF (M i) o (a o)) := by
    intro h a
    rw [hα]
    refine sum_congr rfl fun i _ => ?_
    have hp : pairing (X i) (Y i) (A h a)
        = q.pathPhase (A h a) i.1 - q.pathPhase (A h a) i.2.1 := pairing_elim _ _ _ _ _
    rw [← hp, pairing_tri, Int.cast_add, AddChar.map_add_eq_mul, char_coef]
    simp only [β, M]
    ring
  have heval : ∀ h : Fin L → Bool, MvPolynomial.eval (fun ℓ => (bit (h ℓ) : ℂ)) Q = ((P h : ℝ) : ℂ) := by
    intro h
    rw [hQ h]
    simp_rw [← hexp]
    simp only [P, u]
    push_cast
    rw [mul_sum]
  obtain ⟨R, hRd, hR⟩ := exists_re_poly Q
  have hRval : ∀ h : Fin L → Bool, MvPolynomial.eval (fun ℓ => bit (h ℓ)) R = P h := by
    intro h
    rw [hR, heval h]
    simp
  refine ⟨1 - R, ?_, ?_⟩
  · refine (MvPolynomial.totalDegree_sub _ _).trans (max_le ?_ (hRd.trans hQd))
    simp
  · intro x
    have hev : (fun i => if x i then (1 : ℝ) else 0) = fun ℓ => bit (x ℓ) := rfl
    rw [hev, map_sub, map_one, hRval]
    have h0 := hP0 x
    have h1 := hP1 x
    by_cases hall : ∀ i, x i = true
    · have hxe : x = fun _ => true := funext hall
      have hand : andBool x = 1 := by simp [andBool, hall]
      rw [hand]
      have hP := hPhigh
      rw [← hxe] at hP
      rw [abs_le]
      constructor <;> linarith
    · have hand : andBool x = 0 := by simp only [andBool, hall, ↓reduceIte]
      rw [hand, sub_zero]
      push Not at hall
      obtain ⟨ℓ, hℓ⟩ := hall
      have hP := hPlow x ℓ (by simpa using hℓ)
      rw [abs_le]
      constructor <;> linarith

end Chain

/-- **Simple graphs with cut answers modulo 4.** A quantum algorithm that computes the minimum degree of every simple
graph with error at most `1/3`, where each query returns the cut modulo 4, makes `Ω(√n)` queries. -/
theorem mod4_simple_bound (hA : AndApproxDegree) : ∃ c₀ : ℝ, 0 < c₀ ∧
    ∀ (n : ℕ) [NeZero n] (T : ℕ) (S : Type) [Fintype S] [DecidableEq S] (q : QAlg n T S),
    (∀ A : Weights n, IsSimple A → q.errAt 4 A (minDegree A) ≤ 1 / 3) →
    c₀ * Real.sqrt n ≤ T + 1 := by
  obtain ⟨c, hc, hdeg⟩ := hA
  refine ⟨min (c / 8) (1 / 3), by positivity, ?_⟩
  intro n _ T S _ _ q herr
  have hT : (0 : ℝ) ≤ T := by positivity
  have hsq0 : 0 ≤ Real.sqrt n := Real.sqrt_nonneg _
  by_cases hn : n < 6
  · have h1 : Real.sqrt n ≤ 3 := by
      rw [Real.sqrt_le_left (by norm_num)]
      have : (n : ℝ) ≤ 5 := by exact_mod_cast (by omega : n ≤ 5)
      linarith
    have h2 : min (c / 8) (1 / 3) * Real.sqrt n ≤ (1 / 3) * 3 :=
      mul_le_mul (min_le_right _ _) h1 hsq0 (by norm_num)
    linarith
  · obtain ⟨k, rfl⟩ : ∃ k, n = k + 3 := ⟨n - 3, by omega⟩
    let L := (k + 3) / 3
    have hL : 3 * L ≤ k + 3 := Nat.mul_div_le _ _
    have hL2 : 2 ≤ L := by
      have : 2 * 3 ≤ k + 3 := by omega
      exact (Nat.le_div_iff_mul_le (by norm_num)).mpr this
    obtain ⟨r, hrd, hr⟩ := exists_and_approx_tri hL q hL2 herr
    have h1 := hdeg L r hr
    have h2 : (r.totalDegree : ℝ) ≤ 2 * T := by exact_mod_cast hrd
    have hnL : ((k + 3 : ℕ) : ℝ) ≤ 4 * L := by
      have : k + 3 ≤ 4 * L := by omega
      exact_mod_cast this
    have hs : Real.sqrt ((k + 3 : ℕ) : ℝ) ≤ 2 * Real.sqrt L := by
      calc Real.sqrt ((k + 3 : ℕ) : ℝ) ≤ Real.sqrt (4 * L) := Real.sqrt_le_sqrt hnL
        _ = 2 * Real.sqrt L := by
          rw [Real.sqrt_mul (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num,
            Real.sqrt_sq (by norm_num)]
    have h3 : min (c / 8) (1 / 3) * Real.sqrt ((k + 3 : ℕ) : ℝ) ≤ (c / 8) * (2 * Real.sqrt L) :=
      mul_le_mul (min_le_left _ _) hs hsq0 (by positivity)
    nlinarith

end CutQuery
