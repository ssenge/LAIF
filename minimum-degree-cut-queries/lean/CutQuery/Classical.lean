import CutQuery.Core

/-!
# Characters and the injection used for the count of visible vertices

Notation follows Section 10 of the write-up:
* `exists_character_of_notMem`, `exists_forms`: the character step of Lemma 4;
* `prod_le_natAbs_det`: the injection into `ℤ^ρ / M ℤ^ρ`, also the Counting step of Lemma 2.
-/

open Finset

namespace CutQuery

section Character

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A vector outside a subgroup of `ℤ^ι` is separated from it by a character given by some `t`. -/
theorem exists_character_of_notMem (L : AddSubgroup (ι → ℤ)) (w : ι → ℤ) (hw : w ∉ L) :
    ∃ t : ι → AddCircle (1 : ℚ), (∀ l ∈ L, ∑ s, l s • t s = 0) ∧ ∑ s, w s • t s ≠ 0 := by
  have ha : (QuotientAddGroup.mk w : (ι → ℤ) ⧸ L) ≠ 0 := by
    rwa [Ne, QuotientAddGroup.eq_zero_iff]
  obtain ⟨c, hc⟩ := CharacterModule.exists_character_apply_ne_zero_of_ne_zero ha
  let ψ : (ι → ℤ) →+ AddCircle (1 : ℚ) :=
    AddMonoidHom.comp (show ((ι → ℤ) ⧸ L) →+ AddCircle (1 : ℚ) from c) (QuotientAddGroup.mk' L)
  have hψ : ∀ x, ψ x = ∑ s, x s • ψ (Pi.single s 1) := by
    intro x
    have hx : x = ∑ s, x s • (Pi.single s 1 : ι → ℤ) := by
      funext i
      simp [Finset.sum_apply, Pi.single_apply]
    conv_lhs => rw [hx]
    rw [map_sum]
    exact sum_congr rfl fun s _ => map_zsmul ψ _ _
  refine ⟨fun s => ψ (Pi.single s 1), ?_, ?_⟩
  · intro l hl
    rw [← hψ l]
    change c (QuotientAddGroup.mk l) = 0
    rw [(QuotientAddGroup.eq_zero_iff l).mpr hl]
    exact map_zero (show ((ι → ℤ) ⧸ L) →+ AddCircle (1 : ℚ) from c)
  · rw [← hψ w]
    exact hc

end Character

section Injection

variable {ρ κ : Type*} [Fintype ρ] [DecidableEq ρ] [Fintype κ]

/-- `ℤ^ρ / M ℤ^ρ` has `|det M|` elements. -/
theorem card_quotient_range (M : Matrix ρ ρ ℤ) (hdet : M.det ≠ 0) :
    Nat.card ((ρ → ℤ) ⧸ LinearMap.range (Matrix.toLin' M)) = M.det.natAbs := by
  have hinj : Function.Injective (Matrix.toLin' M) := by
    intro x y hxy
    have hxy' : M.mulVec x = M.mulVec y := by simpa [Matrix.toLin'_apply] using hxy
    have h := congrArg M.adjugate.mulVec hxy'
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec,
      Matrix.smul_mulVec, Matrix.one_mulVec, Matrix.one_mulVec] at h
    funext i
    have hi := congrFun h i
    simp only [Pi.smul_apply, smul_eq_mul] at hi
    exact mul_left_cancel₀ hdet hi
  let e := LinearEquiv.ofInjective (Matrix.toLin' M) hinj
  have := Submodule.natAbs_det_equiv (LinearMap.range (Matrix.toLin' M)) e
  rw [← this]
  have hcomp : (LinearMap.range (Matrix.toLin' M)).subtype ∘ₗ AddMonoidHom.toIntLinearMap (e : (ρ → ℤ) →+ _)
      = Matrix.toLin' M := by
    ext x
    rfl
  rw [hcomp, LinearMap.det_toLin']

/-- The injection of Lemma 4. If `N z = M p` forces `g_q ∣ z_q`, then `∏ g_q ≤ |det M|`. -/
theorem prod_le_natAbs_det (M : Matrix ρ ρ ℤ) (N : Matrix ρ κ ℤ) (hdet : M.det ≠ 0) (g : κ → ℕ)
    (hdep : ∀ (z : κ → ℤ) (p : ρ → ℤ), N.mulVec z = M.mulVec p → ∀ q, (g q : ℤ) ∣ z q) :
    ∏ q, g q ≤ M.det.natAbs := by
  classical
  let R := LinearMap.range (Matrix.toLin' M)
  have hcard := card_quotient_range M hdet
  have hpos : Nat.card ((ρ → ℤ) ⧸ R) ≠ 0 := by
    rw [hcard]; exact Int.natAbs_ne_zero.mpr hdet
  have : Finite ((ρ → ℤ) ⧸ R) := Nat.finite_of_card_ne_zero hpos
  let φ : (∀ q, Fin (g q)) → (ρ → ℤ) ⧸ R := fun z =>
    Submodule.Quotient.mk (N.mulVec fun q => ((z q : ℕ) : ℤ))
  have hφ : Function.Injective φ := by
    intro z z' h
    have h' := (Submodule.Quotient.eq R).mp h
    obtain ⟨p, hp⟩ := h'
    have hsub : N.mulVec (fun q => ((z q : ℕ) : ℤ) - ((z' q : ℕ) : ℤ)) = M.mulVec p := by
      have : (fun q => ((z q : ℕ) : ℤ) - ((z' q : ℕ) : ℤ))
          = (fun q => ((z q : ℕ) : ℤ)) - (fun q => ((z' q : ℕ) : ℤ)) := rfl
      rw [this, Matrix.mulVec_sub]
      simpa [Matrix.toLin'_apply] using hp.symm
    funext q
    have hd := hdep _ p hsub q
    have hz := (z q).2
    have hz' := (z' q).2
    have habs : |((z q : ℕ) : ℤ) - ((z' q : ℕ) : ℤ)| < (g q : ℤ) := by
      rw [abs_lt]; constructor <;> omega
    have h0 := Int.eq_zero_of_abs_lt_dvd hd habs
    exact Fin.ext (by omega)
  have hle := Nat.card_le_card_of_injective φ hφ
  rw [hcard] at hle
  have hc : Nat.card (∀ q, Fin (g q)) = ∏ q, g q := by
    rw [Nat.card_eq_fintype_card, Fintype.card_pi]
    simp
  rwa [hc] at hle

end Injection

section Lemma4

variable {V ι ρ : Type*} [Fintype V] [DecidableEq V] [Fintype ι] [DecidableEq ι] [Fintype ρ]
  [DecidableEq ρ]

/-- The indicator of edge `ab` crossing query `s`. -/
def cutInd (x : ι → V → ℤ) (s : ι) (a b : V) : ℤ := x s a + x s b - 2 * (x s a * x s b)

/-- The answers `(⟨b_ab, δ_{x^s}⟩)_s` to the label vector
`b_ab = e_ab - e_oa - e_ob + e_op + e_oq - e_pq`. -/
def labelVec (x : ι → V → ℤ) (o p q a b : V) : ι → ℤ := fun s =>
  cutInd x s a b - cutInd x s o a - cutInd x s o b + cutInd x s o p + cutInd x s o q - cutInd x s p q

/-- The answers `(⟨B_u, δ_{x^s}⟩)_s` to `B_u = e_ua + e_uc - e_ac`. -/
def vertexVec (x : ι → V → ℤ) (u a c : V) : ι → ℤ := fun s =>
  cutInd x s u a + cutInd x s u c - cutInd x s a c

omit [Fintype V] [DecidableEq V] [DecidableEq ι] in
theorem cutSum_comm {A : Type*} [AddCommGroup A] (x : ι → V → ℤ) (t : ι → A) (a b : V) :
    cutSum x t a b = cutSum x t b a := by
  unfold cutSum
  exact sum_congr rfl fun s _ => by congr 1; ring

theorem two_divisible (y : AddCircle (1 : ℚ)) : ∃ b : AddCircle (1 : ℚ), (2 : ℤ) • b = y := by
  obtain ⟨r, rfl⟩ := QuotientAddGroup.mk_surjective y
  refine ⟨QuotientAddGroup.mk (r / 2), ?_⟩
  have h : (2 : ℤ) • (r / 2) = r := by simp only [zsmul_eq_mul]; push_cast; ring
  exact (map_zsmul (QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : ℚ))) 2 (r / 2)).symm.trans
    (congrArg _ h)

omit [Fintype V] in
/-- Lemma 4, first paragraph: a visible vertex carries a form with vanishing labels (`ε = 0` in (1)) and
`G · 2 β_u ≠ 0`. -/
theorem exists_forms (x : ι → V → ℤ) (o p q : V) (L : AddSubgroup (ι → ℤ))
    (hlab : ∀ a b, a ≠ o → b ≠ o → a ≠ b → labelVec x o p q a b ∈ L) (G : ℤ) (u a c : V)
    (hua : u ≠ a) (huc : u ≠ c) (hac : a ≠ c) (hvis : G • vertexVec x u a c ∉ L) :
    ∃ (t : ι → AddCircle (1 : ℚ)) (β : V → AddCircle (1 : ℚ)),
      (∀ a b, a ≠ b → cutSum x t a b = β a + β b) ∧ G • ((2 : ℤ) • β u) ≠ 0 := by
  obtain ⟨t, ht, hw⟩ := exists_character_of_notMem L _ hvis
  obtain ⟨βo, hβo⟩ := two_divisible (cutSum x t o p + cutSum x t o q - cutSum x t p q)
  have hβo' : βo + βo = cutSum x t o p + cutSum x t o q - cutSum x t p q := by
    rw [← two_smul ℤ βo]; exact hβo
  let β : V → AddCircle (1 : ℚ) := fun a => if a = o then βo else cutSum x t o a - βo
  have hβ1 : β o = βo := by simp [β]
  have hβ2 : ∀ a, a ≠ o → β a = cutSum x t o a - βo := fun a ha => by simp [β, ha]
  have hF : ∀ a b, a ≠ b → cutSum x t a b = β a + β b := by
    have hO : ∀ b, b ≠ o → cutSum x t o b = β o + β b := fun b hb => by
      rw [hβ1, hβ2 b hb]; abel
    intro a b hab
    by_cases ha : a = o
    · subst ha; exact hO b hab.symm
    by_cases hb : b = o
    · subst hb; rw [cutSum_comm, add_comm]; exact hO a ha
    have hl := ht _ (hlab a b ha hb hab)
    have hl' : cutSum x t a b - cutSum x t o a - cutSum x t o b + cutSum x t o p + cutSum x t o q
        - cutSum x t p q = 0 := by
      rw [← hl]
      simp only [labelVec, sub_smul, add_smul, sum_sub_distrib, sum_add_distrib]
      rfl
    rw [hβ2 a ha, hβ2 b hb]
    calc cutSum x t a b
        = (cutSum x t a b - cutSum x t o a - cutSum x t o b + cutSum x t o p + cutSum x t o q
            - cutSum x t p q) + cutSum x t o a + cutSum x t o b
            - (cutSum x t o p + cutSum x t o q - cutSum x t p q) := by abel
      _ = _ := by rw [hl', ← hβo']; abel
  refine ⟨t, β, hF, ?_⟩
  have h2 : (2 : ℤ) • β u = ∑ s, vertexVec x u a c s • t s := by
    have : ∑ s, vertexVec x u a c s • t s = cutSum x t u a + cutSum x t u c - cutSum x t a c := by
      simp only [vertexVec, sub_smul, add_smul, sum_sub_distrib, sum_add_distrib]
      rfl
    rw [this, hF u a hua, hF u c huc, hF a c hac, two_smul]
    abel
  have h3 : ∑ s, (G • vertexVec x u a c) s • t s = G • ∑ s, vertexVec x u a c s • t s := by
    rw [smul_sum]
    exact sum_congr rfl fun s _ => by simp [mul_smul]
  rw [h2, ← h3]
  exact hw

end Lemma4

end CutQuery
