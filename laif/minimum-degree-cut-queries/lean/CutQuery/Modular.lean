import CutQuery.QPath
import CutQuery.QPoly
import CutQuery.QuantumBound

/-!
# The modular model

Weights live modulo `M = 2^K` with `K ≥ 2`, and phase queries have modulus `M`. Under the promise that every degree is
`d` or `d + 2` modulo `M`, deciding whether some degree is `d` needs `Ω(√n)` queries.

* `sparsity_two_group`: the exact sparsity lemma over a 2-group, at the level of the family;
* `exists_base`: a weight vector with all degrees equal to `d`, when `n d` is even;
* `exists_and_approx_mod`: averaging over the uniform labels leaves the indices with all labels zero, so the
  acceptance probability is exactly a polynomial of degree at most `2 T + 2` on the cube;
* `modular_bound`: the bound `c₀ √n ≤ T + 1`.
-/

open Finset

namespace CutQuery

local notation "ω" => ZMod.stdAddChar

section TwoGroup

variable {k R : ℕ}

/-- Exact sparsity over a 2-group: if all labels vanish, at most `R + 2` vertices have a nonzero shift value. -/
theorem sparsity_two_group (x : Fin R → Fin (k + 3) → Bool) (t : Fin R → AddCircle (1 : ℝ)) (K : ℕ)
    (ht : ∀ s, ((2 : ℤ) ^ K) • t s = 0) (hlab : ∀ j : LabelIdx k, ∑ s, cut (b j) (x s) • t s = 0) :
    (univ.filter fun v : Fin (k + 3) => ∑ s, cut (shiftVec v) (x s) • t s ≠ 0).card ≤ R + 2 := by
  set x' := queryMat x with hx'
  set F := cutSum x' t with hFdef
  have hFc : ∀ a c, F a c = F c a := fun a c => cutSum_comm x' t a c
  obtain ⟨β₀, hβ₀⟩ := two_divisible_real (F 0 1 + F 0 2 - F 1 2)
  have hβ₀' : β₀ + β₀ = F 0 1 + F 0 2 - F 1 2 := by rw [← two_smul ℤ β₀]; exact hβ₀
  let β : Fin (k + 3) → AddCircle (1 : ℝ) := fun a => if a = 0 then β₀ else F 0 a - β₀
  have hβ0 : β 0 = β₀ := by simp [β]
  have hβne : ∀ a, a ≠ 0 → β a = F 0 a - β₀ := fun a ha => by simp [β, ha]
  have hF0 : ∀ c, c ≠ 0 → F 0 c = β 0 + β c := by
    intro c hc
    rw [hβ0, hβne c hc]
    abel
  have hF : ∀ a c, a ≠ c → cutSum x' t a c = β a + β c := by
    intro a c hac
    change F a c = β a + β c
    by_cases ha : a = 0
    · subst ha
      exact hF0 c (Ne.symm hac)
    by_cases hc : c = 0
    · subst hc
      rw [hFc, hF0 a ha, add_comm]
    have hl : ∑ s, cut (labelVector a c) (x s) • t s = 0 := by
      rcases labelVector_cases ha hc hac with h | ⟨j, h⟩
      · rw [h]
        simp [cut_zero]
      · rw [← h]
        exact hlab j
    rw [sum_cut_labelVector] at hl
    change F a c - F 0 a - F 0 c + F 0 1 + F 0 2 - F 1 2 = 0 at hl
    rw [hβne a ha, hβne c hc]
    have h2 : F a c - F 0 a - F 0 c + (β₀ + β₀) = 0 := by
      rw [hβ₀', ← hl]
      abel
    have h3 : F a c = F 0 a + F 0 c - (β₀ + β₀) := by
      have : F a c = (F a c - F 0 a - F 0 c + (β₀ + β₀)) + (F 0 a + F 0 c - (β₀ + β₀)) := by abel
      rw [this, h2, zero_add]
    rw [h3]
    abel
  have hshift : ∀ v, v ≠ 0 → ∑ s, cut (shiftVec v) (x s) • t s = (2 : ℤ) • β v := by
    intro v hv
    rw [sum_cut_shiftVec, helperA_of_ne hv]
    set e := helperC v with he
    have he0 : e ≠ 0 := helperC_ne_zero v
    have hve : v ≠ e := helperC_ne v
    rw [hF v 0 hv, hF v e hve, hF 0 e he0.symm, two_smul]
    abel
  set Y := (univ.filter fun v : Fin (k + 3) => ∑ s, cut (shiftVec v) (x s) • t s ≠ 0).erase 0 with hY
  have hY0 : (0 : Fin (k + 3)) ∉ Y := notMem_erase _ _
  have hmemY : ∀ v ∈ Y, v ≠ 0 ∧ ∑ s, cut (shiftVec v) (x s) • t s ≠ 0 := by
    intro v hv
    have := mem_erase.mp hv
    exact ⟨this.1, (mem_filter.mp this.2).2⟩
  have hcard := exact_sparsity_two_group x' t β 0 (queryMat_binary x) hF Y hY0
    (fun v hv => by
      have h1 := hmemY v hv
      rw [← hshift v h1.1]
      exact h1.2)
    (fun v hv => by
      refine ⟨K, ?_⟩
      rw [← hshift v (hmemY v hv).1, smul_sum]
      refine sum_eq_zero fun s _ => ?_
      rw [smul_comm, ht s, smul_zero])
  rw [Fintype.card_fin] at hcard
  have hpred := pred_card_le_card_erase (s := univ.filter fun v : Fin (k + 3) =>
    ∑ s, cut (shiftVec v) (x s) • t s ≠ 0) (a := 0)
  rw [← hY] at hpred
  omega

variable {σ : Type*} [Fintype σ]

/-- The sparsity for a finite index type: with all labels zero modulo `2^K`, at most `card σ + 2` vertices have a
shift value that is nonzero modulo `2^K`. -/
theorem sparsity_two_group_pairing (K : ℕ) (x : σ → Fin (k + 3) → Bool) (y : σ → ℤ)
    (hlab : ∀ j : LabelIdx k, ((pairing x y (b j) : ℤ) : ZMod (2 ^ K)) = 0) :
    (univ.filter fun v : Fin (k + 3) => ((pairing x y (shiftVec v) : ℤ) : ZMod (2 ^ K)) ≠ 0).card
      ≤ Fintype.card σ + 2 := by
  classical
  let e := Fintype.equivFin σ
  have hsum : ∀ A : Weights (k + 3),
      ∑ s : Fin (Fintype.card σ), cut A (x (e.symm s)) • circ (2 ^ K) (y (e.symm s))
        = circ (2 ^ K) (pairing x y A) := by
    intro A
    rw [e.symm.sum_comp (fun s => cut A (x s) • circ (2 ^ K) (y s)), sum_zsmul_circ]
    rfl
  have hpow : ((2 : ℤ) ^ K : ℤ) = ((2 ^ K : ℕ) : ℤ) := by push_cast; rfl
  have h := sparsity_two_group (fun s => x (e.symm s)) (fun s => circ (2 ^ K) (y (e.symm s))) K
    (fun s => by
      rw [zsmul_circ, circ_eq_zero_iff, hpow]
      push_cast
      have h0 : (2 : ZMod (2 ^ K)) ^ K = 0 := by
        have := ZMod.natCast_self (2 ^ K)
        push_cast at this
        exact this
      rw [h0, zero_mul])
    (fun j => by
      rw [hsum, circ_eq_zero_iff]
      exact hlab j)
  simp only [hsum] at h
  convert h using 3
  rw [ne_eq, ne_eq, circ_eq_zero_iff]

end TwoGroup

section Family

variable {k : ℕ}

/-- The star at vertex `0`. -/
def starVec (k : ℕ) : Weights (k + 3) := ∑ u ∈ univ.erase (0 : Fin (k + 3)), pairVec 0 u

theorem degree_starVec (w : Fin (k + 3)) : degree (starVec k) w = if w = 0 then (k : ℤ) + 2 else 1 := by
  unfold starVec
  rw [degree_sum]
  have h : ∀ u ∈ univ.erase (0 : Fin (k + 3)), degree (pairVec 0 u) w = if w = 0 ∨ w = u then 1 else 0 :=
    fun u hu => degree_pairVec (mem_erase.mp hu).1.symm w
  rw [sum_congr rfl h]
  by_cases hw : w = 0
  · simp only [hw, true_or, ↓reduceIte, sum_const, card_erase_of_mem (mem_univ _), card_univ,
      Fintype.card_fin, nsmul_eq_mul, mul_one]
    push_cast
    omega
  · simp only [hw, false_or, ↓reduceIte]
    rw [sum_ite_eq]
    have hmem : w ∈ univ.erase (0 : Fin (k + 3)) := mem_erase.mpr ⟨hw, mem_univ _⟩
    simp only [hmem, ↓reduceIte]

/-- A weight vector with all degrees equal to `d`, when `n d` is even. -/
theorem exists_base (d : ℤ) (hd : Even (((k + 3 : ℕ) : ℤ) * d)) :
    ∃ A₀ : Weights (k + 3), ∀ w, degree A₀ w = d := by
  obtain ⟨l, hl⟩ := hd
  refine ⟨d • starVec k - (l - d) • shiftVec 0, fun w => ?_⟩
  rw [degree_sub, degree_zsmul, degree_zsmul, degree_starVec, degree_shiftVec]
  push_cast at hl
  by_cases hw : w = 0
  · simp only [hw, ↓reduceIte]
    linarith
  · simp only [hw, ↓reduceIte]
    ring

/-- The input before reduction: `A₀ + ∑ h_v B_v + ∑ a_j b_j`. -/
def modFam (A₀ : Weights (k + 3)) (h : Fin (k + 3) → Bool) (a : LabelIdx k → ℤ) : Weights (k + 3) :=
  A₀ + ∑ v, bitZ (h v) • shiftVec v + ∑ j, a j • b j

theorem degree_modFam (A₀ : Weights (k + 3)) (h : Fin (k + 3) → Bool) (a : LabelIdx k → ℤ) (w : Fin (k + 3)) :
    degree (modFam A₀ h a) w = degree A₀ w + 2 * bitZ (h w) := by
  unfold modFam
  rw [degree_add, degree_add, degree_sum, degree_sum]
  simp only [degree_zsmul, degree_b, degree_shiftVec, mul_zero, sum_const_zero, add_zero]
  rw [sum_eq_single w]
  · simp only [↓reduceIte]
    ring
  · intro u _ hu
    simp only [hu.symm, ↓reduceIte, mul_zero]
  · intro hw
    exact absurd (mem_univ _) hw

theorem pairing_modFam {σ : Type*} [Fintype σ] (x : σ → Fin (k + 3) → Bool) (y : σ → ℤ) (A₀ : Weights (k + 3))
    (h : Fin (k + 3) → Bool) (a : LabelIdx k → ℤ) :
    pairing x y (modFam A₀ h a) = pairing x y A₀ + ∑ v, bitZ (h v) * pairing x y (shiftVec v)
      + ∑ j, a j * pairing x y (b j) := by
  unfold pairing modFam
  simp only [cut_add, cut_sum, cut_zsmul, mul_add, sum_add_distrib, mul_sum]
  congr 1
  · congr 1
    rw [sum_comm]
    exact sum_congr rfl fun v _ => sum_congr rfl fun s _ => by ring
  · rw [sum_comm]
    exact sum_congr rfl fun j _ => sum_congr rfl fun s _ => by ring

/-- Entrywise reduction into `[0, M - 1]`. -/
def red (M : ℤ) (A : Weights (k + 3)) : Weights (k + 3) := fun e => A e % M

theorem red_eq (M : ℤ) (A : Weights (k + 3)) : red M A = A - M • fun e => A e / M := by
  funext e
  simp [red, Int.emod_def]

theorem inClass_red {M : ℤ} (hM : 0 < M) (A : Weights (k + 3)) : InClass (M - 1) (red M A) := by
  intro e
  have h1 := Int.emod_nonneg (A e) hM.ne'
  have h2 := Int.emod_lt_of_pos (A e) hM
  simp only [red]
  constructor <;> omega

theorem degree_red (M : ℤ) (A : Weights (k + 3)) (w : Fin (k + 3)) :
    degree (red M A) w ≡ degree A w [ZMOD M] := by
  rw [red_eq, degree_sub, degree_zsmul]
  exact (Int.modEq_iff_dvd.mpr ⟨degree (fun e => A e / M) w, by ring⟩)

theorem pairing_red {σ : Type*} [Fintype σ] (x : σ → Fin (k + 3) → Bool) (y : σ → ℤ) (M : ℤ) (A : Weights (k + 3)) :
    pairing x y (red M A) = pairing x y A - M * pairing x y (fun e => A e / M) := by
  rw [red_eq]
  unfold pairing
  simp only [cut_sub, cut_zsmul, mul_sub, sum_sub_distrib, mul_sum]
  congr 1
  exact sum_congr rfl fun s _ => by ring

end Family

section Average

variable {k N : ℕ} [NeZero N] {ι σ : Type*} [Fintype ι] [Fintype σ]

/-- Averaging over uniform labels keeps the indices with all labels zero, and these give a polynomial of low degree
when each of them sees few vertices. -/
theorem exists_poly_average (X : ι → σ → Fin (k + 3) → Bool) (Y : ι → σ → ℤ) (α : ι → ℂ) (A₀ : Weights (k + 3))
    (d₂ : ℕ)
    (hsp : ∀ i, lab X Y N i = 0 → ∃ Z : Finset (Fin (k + 3)), Z.card ≤ d₂ ∧
      ∀ v ∉ Z, ((pairing (X i) (Y i) (shiftVec v) : ℤ) : ZMod N) = 0) :
    ∃ Q : MvPolynomial (Fin (k + 3)) ℂ, Q.totalDegree ≤ d₂ ∧ ∀ h : Fin (k + 3) → Bool,
      MvPolynomial.eval (fun v => (bit (h v) : ℂ)) Q
        = ((N : ℂ) ^ Fintype.card (LabelIdx k))⁻¹ * ∑ c : LabelIdx k → ZMod N, ∑ i,
          (α i * ω ((pairing (X i) (Y i) A₀ : ℤ) : ZMod N)
            * ω ((∑ v, bitZ (h v) * pairing (X i) (Y i) (shiftVec v) : ℤ) : ZMod N))
          * ω (∑ j, c j * lab X Y N i j) := by
  classical
  have hdiff : ∀ i, ∃ Z : Finset (Fin (k + 3)), lab X Y N i = 0 → Z.card ≤ d₂ ∧
      ∀ v ∉ Z, ((pairing (X i) (Y i) (shiftVec v) : ℤ) : ZMod N) = 0 := by
    intro i
    by_cases hi : lab X Y N i = 0
    · obtain ⟨Z, h1, h2⟩ := hsp i hi
      exact ⟨Z, fun _ => ⟨h1, h2⟩⟩
    · exact ⟨∅, fun h => absurd h hi⟩
  choose Z hZ using hdiff
  let piece : ι → MvPolynomial (Fin (k + 3)) ℂ := fun i =>
    MvPolynomial.C (α i * ω ((pairing (X i) (Y i) A₀ : ℤ) : ZMod N))
      * ∏ v ∈ Z i, ((1 : MvPolynomial (Fin (k + 3)) ℂ)
        + MvPolynomial.C (ω ((pairing (X i) (Y i) (shiftVec v) : ℤ) : ZMod N) - 1) * MvPolynomial.X v)
  refine ⟨∑ i, if lab X Y N i = 0 then piece i else 0, ?_, fun h => ?_⟩
  · refine MvPolynomial.totalDegree_finsetSum_le fun i _ => ?_
    split_ifs with hi
    · refine (MvPolynomial.totalDegree_mul _ _).trans ?_
      simp only [MvPolynomial.totalDegree_C, zero_add]
      exact (totalDegree_prod_factor (Z i) _).trans (hZ i hi).1
    · simp
  · have hNC : (N : ℂ) ^ Fintype.card (LabelIdx k) ≠ 0 :=
      pow_ne_zero _ (by exact_mod_cast NeZero.ne N)
    rw [sum_comm, mul_sum, map_sum]
    refine sum_congr rfl fun i _ => ?_
    rw [← mul_sum, sum_char_dot]
    by_cases hi : lab X Y N i = 0
    · simp only [hi, ↓reduceIte, piece, map_mul, MvPolynomial.eval_C]
      rw [eval_factors (Z i) _ (hZ i hi).2 h]
      field_simp
    · simp [hi]

end Average

section Chain

variable {k T N : ℕ} [NeZero N] {S : Type*} [Fintype S] [DecidableEq S]

open scoped Classical in
/-- From an algorithm that is correct under the promise modulo `M`, with phase queries of modulus `N`, a real
polynomial approximating `AND` on the cube. Here `M` vanishes in `ZMod N`, `2` does not vanish modulo `M`, and at most
`2 T + 2` vertices are visible for a pair of paths with zero labels. -/
theorem exists_and_approx_mod (q : QAlg (k + 3) T S) (M : ℤ) (d : ℤ) (hMpos : 0 < M)
    (hMN : ((M : ℤ) : ZMod N) = 0) (hne : ¬ (d + 2 ≡ d [ZMOD M]))
    (hsparse : ∀ (x : Fin T ⊕ Fin T → Fin (k + 3) → Bool) (y : Fin T ⊕ Fin T → ℤ),
      (∀ j : LabelIdx k, ((pairing x y (b j) : ℤ) : ZMod N) = 0) →
      (univ.filter fun v : Fin (k + 3) => ((pairing x y (shiftVec v) : ℤ) : ZMod N) ≠ 0).card ≤ 2 * T + 2)
    (hd : Even (((k + 3 : ℕ) : ℤ) * d))
    (herr : ∀ A : Weights (k + 3), InClass (M - 1) A →
      (∀ v, degree A v ≡ d [ZMOD M] ∨ degree A v ≡ d + 2 [ZMOD M]) →
      q.errAt N A (if ∃ v, degree A v ≡ d [ZMOD M] then 1 else 0) ≤ 1 / 3) :
    ∃ r : MvPolynomial (Fin (k + 3)) ℝ, r.totalDegree ≤ 2 * T + 2 ∧
      ∀ x : Fin (k + 3) → Bool,
        |MvPolynomial.eval (fun i => if x i then (1 : ℝ) else 0) r - andBool x| ≤ 1 / 3 := by
  obtain ⟨A₀, hA₀⟩ := exists_base d hd
  obtain ⟨α, hα⟩ := q.exists_acc_expansion N 1
  let X : (Fin T → S) × (Fin T → S) × S → Fin T ⊕ Fin T → Fin (k + 3) → Bool := fun i =>
    Sum.elim (fun t => q.x (i.1 t)) (fun t => q.x (i.2.1 t))
  let Y : (Fin T → S) × (Fin T → S) × S → Fin T ⊕ Fin T → ℤ := fun i =>
    Sum.elim (fun t => q.z (i.1 t)) (fun t => - q.z (i.2.1 t))
  let A : (Fin (k + 3) → Bool) → (LabelIdx k → ZMod N) → Weights (k + 3) := fun h c =>
    red M (modFam A₀ h fun j => (c j).valMinAbs)
  have hdeg : ∀ h c w, degree (A h c) w ≡ d + 2 * bitZ (h w) [ZMOD M] := by
    intro h c w
    refine (degree_red _ _ w).trans ?_
    rw [degree_modFam, hA₀]
  have hprom : ∀ h c v, degree (A h c) v ≡ d [ZMOD M] ∨ degree (A h c) v ≡ d + 2 [ZMOD M] := by
    intro h c v
    have := hdeg h c v
    cases hb : h v
    · left
      simpa [hb, bitZ] using this
    · right
      simpa [hb, bitZ] using this
  have hacc0 : ∀ h c, 0 ≤ q.acc N (A h c) 1 := fun h c => q.acc_nonneg _ _ _
  have hacc1 : ∀ h c, q.acc N (A h c) 1 ≤ 1 := fun h c => q.acc_le_one _ _ _
  have hlow : ∀ h c (v : Fin (k + 3)), h v = false → 2 / 3 ≤ q.acc N (A h c) 1 := by
    intro h c v hv
    have hex : ∃ v, degree (A h c) v ≡ d [ZMOD M] := by
      refine ⟨v, ?_⟩
      have := hdeg h c v
      simpa [hv, bitZ] using this
    have he := herr (A h c) (inClass_red hMpos _) (hprom h c)
    simp only [hex, ↓reduceIte] at he
    have hs := q.acc_add_errAt N (A h c) 1
    linarith
  have hhigh : ∀ c, q.acc N (A (fun _ => true) c) 1 ≤ 1 / 3 := by
    intro c
    have hex : ¬ ∃ v, degree (A (fun _ => true) c) v ≡ d [ZMOD M] := by
      rintro ⟨v, hv⟩
      have h1 := hdeg (fun _ => true) c v
      simp only [bitZ, ↓reduceIte, mul_one] at h1
      exact hne (h1.symm.trans hv)
    have he := herr (A (fun _ => true) c) (inClass_red hMpos _) (hprom _ c)
    simp only [hex, ↓reduceIte] at he
    exact (q.acc_le_errAt N _ (d := 1) (d' := 0) (by norm_num)).trans he
  let u : ℝ := ((N : ℝ) ^ Fintype.card (LabelIdx k))⁻¹
  have hu0 : 0 ≤ u := by positivity
  have hNR : (N : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne N
  have hu1 : ∑ _c : LabelIdx k → ZMod N, u = 1 := by
    rw [sum_const, card_univ, Fintype.card_fun, ZMod.card, nsmul_eq_mul]
    push_cast
    exact mul_inv_cancel₀ (pow_ne_zero _ hNR)
  let P : (Fin (k + 3) → Bool) → ℝ := fun h => ∑ c, u * q.acc N (A h c) 1
  have hP0 : ∀ h, 0 ≤ P h := fun h => sum_nonneg fun c _ => mul_nonneg hu0 (hacc0 h c)
  have hP1 : ∀ h, P h ≤ 1 := by
    intro h
    calc P h ≤ ∑ _c : LabelIdx k → ZMod N, u * 1 :=
          sum_le_sum fun c _ => mul_le_mul_of_nonneg_left (hacc1 h c) hu0
      _ = 1 := by simpa using hu1
  have hPlow : ∀ h (v : Fin (k + 3)), h v = false → 2 / 3 ≤ P h := by
    intro h v hv
    calc (2 / 3 : ℝ) = ∑ _c : LabelIdx k → ZMod N, u * (2 / 3) := by rw [← sum_mul, hu1, one_mul]
      _ ≤ P h := sum_le_sum fun c _ => mul_le_mul_of_nonneg_left (hlow h c v hv) hu0
  have hPhigh : P (fun _ => true) ≤ 1 / 3 := by
    calc P (fun _ => true) ≤ ∑ _c : LabelIdx k → ZMod N, u * (1 / 3) :=
          sum_le_sum fun c _ => mul_le_mul_of_nonneg_left (hhigh c) hu0
      _ = 1 / 3 := by rw [← sum_mul, hu1, one_mul]
  obtain ⟨Q, hQd, hQ⟩ := exists_poly_average (N := N) X Y α A₀ (2 * T + 2) (fun i hi => ⟨_,
    hsparse (X i) (Y i) (fun j => congrFun hi j), fun v hv => by
      by_contra hne'
      exact hv (mem_filter.mpr ⟨mem_univ _, hne'⟩)⟩)
  have hexp : ∀ h c, (q.acc N (A h c) 1 : ℂ)
      = ∑ i, (α i * ω ((pairing (X i) (Y i) A₀ : ℤ) : ZMod N)
          * ω ((∑ v, bitZ (h v) * pairing (X i) (Y i) (shiftVec v) : ℤ) : ZMod N))
        * ω (∑ j, c j * lab X Y N i j) := by
    intro h c
    rw [hα]
    refine sum_congr rfl fun i _ => ?_
    have hp : pairing (X i) (Y i) (A h c)
        = q.pathPhase (A h c) i.1 - q.pathPhase (A h c) i.2.1 := pairing_elim _ _ _ _ _
    have hc : ((pairing (X i) (Y i) (A h c) : ℤ) : ZMod N)
        = ((pairing (X i) (Y i) A₀ : ℤ) : ZMod N)
          + ((∑ v, bitZ (h v) * pairing (X i) (Y i) (shiftVec v) : ℤ) : ZMod N)
          + ∑ j, c j * lab X Y N i j := by
      simp only [A]
      rw [pairing_red, pairing_modFam]
      simp only [lab, Int.cast_add, Int.cast_sub, Int.cast_mul, Int.cast_sum, ZMod.coe_valMinAbs, hMN,
        zero_mul, sub_zero]
    rw [← hp, hc, AddChar.map_add_eq_mul, AddChar.map_add_eq_mul]
    ring
  have heval : ∀ h : Fin (k + 3) → Bool, MvPolynomial.eval (fun v => (bit (h v) : ℂ)) Q = ((P h : ℝ) : ℂ) := by
    intro h
    rw [hQ h]
    simp_rw [← hexp]
    simp only [P, u]
    push_cast
    rw [mul_sum]
  obtain ⟨R, hRd, hR⟩ := exists_re_poly Q
  have hRval : ∀ h : Fin (k + 3) → Bool, MvPolynomial.eval (fun v => bit (h v)) R = P h := by
    intro h
    rw [hR, heval h]
    simp
  refine ⟨1 - R, ?_, ?_⟩
  · refine (MvPolynomial.totalDegree_sub _ _).trans (max_le ?_ (hRd.trans hQd))
    simp
  · intro x
    have hev : (fun i => if x i then (1 : ℝ) else 0) = fun v => bit (x v) := rfl
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
      obtain ⟨v, hv⟩ := hall
      have hP := hPlow x v (by simpa using hv)
      rw [abs_le]
      constructor <;> linarith

end Chain

theorem two_not_modEq (d : ℤ) {K : ℕ} (hK : 2 ≤ K) : ¬ (d + 2 ≡ d [ZMOD (2 : ℤ) ^ K]) := by
  intro h
  have hM4 : (4 : ℤ) ≤ (2 : ℤ) ^ K := by
    calc (4 : ℤ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ K := pow_le_pow_right₀ (by norm_num) hK
  have h1 : (2 : ℤ) ^ K ∣ d - (d + 2) := Int.modEq_iff_dvd.mp h
  have h2 : (2 : ℤ) ^ K ∣ 2 := by
    have h3 : d - (d + 2) = -2 := by ring
    rw [h3, dvd_neg] at h1
    exact h1
  have := Int.le_of_dvd (by norm_num) h2
  omega

open scoped Classical in
/-- The lower bound in the modular model. -/
theorem modular_bound (hA : AndApproxDegree) : ∃ c₀ : ℝ, 0 < c₀ ∧
    ∀ (n : ℕ) [NeZero n] (T : ℕ) (S : Type) [Fintype S] [DecidableEq S] (q : QAlg n T S)
      (k : ℕ) (d : ℤ), 2 ≤ k → Even ((n : ℤ) * d) →
    (∀ A : Weights n, InClass ((2 : ℤ) ^ k - 1) A →
      (∀ v, degree A v ≡ d [ZMOD 2 ^ k] ∨ degree A v ≡ d + 2 [ZMOD 2 ^ k]) →
      q.errAt (2 ^ k) A (if ∃ v, degree A v ≡ d [ZMOD 2 ^ k] then 1 else 0) ≤ 1 / 3) →
    c₀ * Real.sqrt n ≤ T + 1 := by
  obtain ⟨c, hc, hdeg⟩ := hA
  refine ⟨min (c / 2) (1 / 2), by positivity, ?_⟩
  intro n _ T S _ _ q K d hK hd herr
  have hT : (0 : ℝ) ≤ T := by positivity
  have hsq0 : 0 ≤ Real.sqrt n := Real.sqrt_nonneg _
  by_cases hn : n < 3
  · have h1 : Real.sqrt n ≤ 2 := by
      rw [Real.sqrt_le_left (by norm_num)]
      have : (n : ℝ) ≤ 2 := by exact_mod_cast (by omega : n ≤ 2)
      linarith
    have h2 : min (c / 2) (1 / 2) * Real.sqrt n ≤ (1 / 2) * 2 :=
      mul_le_mul (min_le_right _ _) h1 hsq0 (by norm_num)
    linarith
  · obtain ⟨k, rfl⟩ : ∃ k, n = k + 3 := ⟨n - 3, by omega⟩
    have hNne : NeZero (2 ^ K) := ⟨by positivity⟩
    have hMN : (((2 : ℤ) ^ K : ℤ) : ZMod (2 ^ K)) = 0 := by
      have := ZMod.natCast_self (2 ^ K)
      push_cast at this ⊢
      exact this
    obtain ⟨r, hrd, hr⟩ := exists_and_approx_mod (N := 2 ^ K) q ((2 : ℤ) ^ K) d (by positivity) hMN
      (two_not_modEq d hK)
      (fun x y hl => (sparsity_two_group_pairing K x y hl).trans (by simp [two_mul]))
      hd herr
    have h1 := hdeg (k + 3) r hr
    have h2 : (r.totalDegree : ℝ) ≤ 2 * T + 2 := by exact_mod_cast hrd
    have h3 : min (c / 2) (1 / 2) * Real.sqrt ((k + 3 : ℕ) : ℝ) ≤ (c / 2) * Real.sqrt ((k + 3 : ℕ) : ℝ) :=
      mul_le_mul_of_nonneg_right (min_le_left _ _) hsq0
    linarith

end CutQuery
