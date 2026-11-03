import CutQuery.Core

/-!
# Classical lower bound for minimum degree with cut queries

Notation follows `QC/cutquery/RESULTS.md`, Section 10:
* `invisible_change`, `invisible_degree`: Lemma 3;
* `exists_character_of_notMem`, `exists_forms`: the character step of Lemma 4;
* `prod_le_natAbs_det`: the injection into `ℤ^ρ / M ℤ^ρ`;
* `visible_count`, `card_le_two_mul`: the counting of Lemma 4, with `|det M| ≤ ρ!` in place of Hadamard;
* `lemma4_count`: the count of Lemma 4 stated for cut queries and vertices outside the lattice;
* `round_solution`: the rounding of Lemma 5;
* `prod_sub_le`, `geom_le`, `xi_value`: the pointwise step and the final sum of Lemma 6;
* `average_visible`, `classical_constants`: the averaging and the constants of Theorem 7.
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

section Visible

variable {W ι ρ A : Type*} [Fintype W] [DecidableEq W] [Fintype ι] [Fintype ρ] [DecidableEq ρ]
  [AddCommGroup A]

omit [Fintype ι] [DecidableEq ρ] in
/-- The combined dependency `(-p, z)` on `W = P(ρ) ⊔ Q`. -/
theorem dep_of_blocks (c : W → ι → ℤ) (row : ρ → ι) (P : ρ → W) (hP : Function.Injective P)
    (hrows : ∀ lam : W → ℤ, (∀ i, ∑ v, lam v * c v (row i) = 0) → IsDep c lam)
    (z : ↥(Set.range P)ᶜ → ℤ) (p : ρ → ℤ)
    (h : (Matrix.of fun i (q : ↥(Set.range P)ᶜ) => c q (row i)).mulVec z
      = (Matrix.of fun i j => c (P j) (row i)).mulVec p) :
    ∃ lam : W → ℤ, IsDep c lam ∧ ∀ q : ↥(Set.range P)ᶜ, lam q = z q := by
  classical
  let e : ρ ⊕ ↥(Set.range P)ᶜ ≃ W :=
    (Equiv.sumCongr (Equiv.ofInjective P hP) (Equiv.refl _)).trans (Equiv.Set.sumCompl (Set.range P))
  have he1 : ∀ j, e (Sum.inl j) = P j := fun j => rfl
  have he2 : ∀ q, e (Sum.inr q) = (q : W) := fun q => rfl
  let lam : W → ℤ := fun v => Sum.elim (fun j => -p j) z (e.symm v)
  have hl1 : ∀ j, lam (P j) = -p j := fun j => by
    change Sum.elim _ _ (e.symm (P j)) = _
    rw [← he1, Equiv.symm_apply_apply]; rfl
  have hl2 : ∀ q : ↥(Set.range P)ᶜ, lam q = z q := fun q => by
    change Sum.elim _ _ (e.symm (q : W)) = _
    rw [← he2, Equiv.symm_apply_apply]; rfl
  refine ⟨lam, hrows lam ?_, hl2⟩
  intro i
  rw [← Equiv.sum_comp e, Fintype.sum_sum_type]
  simp only [he1, he2, hl1, hl2]
  have hi := congrFun h i
  simp only [Matrix.mulVec, dotProduct, Matrix.of_apply] at hi
  have h1 : ∑ q : ↥(Set.range P)ᶜ, z q * c q (row i) = ∑ q : ↥(Set.range P)ᶜ, c q (row i) * z q :=
    sum_congr rfl fun q _ => mul_comm _ _
  have h2 : ∑ j, -p j * c (P j) (row i) = -∑ j, c (P j) (row i) * p j := by
    rw [← sum_neg_distrib]
    exact sum_congr rfl fun j _ => by ring
  rw [h1, h2, hi]
  ring

/-- Lemma 4, counting step. Each `u` has its own form `H u`, with `⟨c_u, c_v⟩ = 0` off the diagonal and
`D u` on it, and `G • D u ≠ 0`, where `G` is divisible by `1, …, m`. An invertible block on `P` then gives
`(m+1)^|Q| ≤ |det M|` for the remaining vertices `Q`. -/
theorem visible_count (c : W → ι → ℤ) (H : W → ι → A) (D : W → A)
    (hd : ∀ u, pr c (H u) u u = D u) (ho : ∀ u v, u ≠ v → pr c (H u) u v = 0)
    (G : ℤ) (m : ℕ) (hG : ∀ k : ℕ, 1 ≤ k → k ≤ m → (k : ℤ) ∣ G) (hne : ∀ u, G • D u ≠ 0)
    (row : ρ → ι) (P : ρ → W) (hP : Function.Injective P)
    (hrows : ∀ lam : W → ℤ, (∀ i, ∑ v, lam v * c v (row i) = 0) → IsDep c lam)
    (hM : (Matrix.of fun i j => c (P j) (row i)).det ≠ 0) :
    (m + 1) ^ Fintype.card ↥(Set.range P)ᶜ ≤ (Matrix.of fun i j => c (P j) (row i)).det.natAbs := by
  classical
  set M : Matrix ρ ρ ℤ := Matrix.of fun i j => c (P j) (row i) with hMdef
  set N : Matrix ρ ↥(Set.range P)ᶜ ℤ := Matrix.of fun i (q : ↥(Set.range P)ᶜ) => c q (row i) with hNdef
  -- the subgroup of values of coordinate `q` over all dependencies
  let S : ↥(Set.range P)ᶜ → AddSubgroup ℤ := fun q =>
    { carrier := {l | ∃ lam : W → ℤ, IsDep c lam ∧ lam q = l}
      zero_mem' := ⟨0, fun s => by simp, rfl⟩
      add_mem' := by
        rintro _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
        refine ⟨a + b, fun s => ?_, rfl⟩
        have := ha s
        have := hb s
        simp only [Pi.add_apply, add_mul, sum_add_distrib]
        omega
      neg_mem' := by
        rintro _ ⟨a, ha, rfl⟩
        refine ⟨-a, fun s => ?_, rfl⟩
        have := ha s
        simp only [Pi.neg_apply, neg_mul, sum_neg_distrib]
        omega }
  have hcyc : ∀ q, ∃ a : ℤ, a ∈ S q ∧ ∀ l ∈ S q, a ∣ l := by
    intro q
    have : IsAddCyclic (S q) := AddSubgroup.isAddCyclic _
    obtain ⟨g, hg⟩ := IsAddCyclic.exists_generator (α := S q)
    refine ⟨g, g.2, fun l hl => ?_⟩
    obtain ⟨k, hk⟩ := AddSubgroup.mem_zmultiples_iff.mp (hg ⟨l, hl⟩)
    have hk' : k • (g : ℤ) = l := congrArg Subtype.val hk
    exact ⟨k, by rw [← hk', smul_eq_mul, mul_comm]⟩
  choose a ha_mem ha_dvd using hcyc
  -- a Cramer dependency: its coordinate `q` is `det M`
  have hdetmem : ∀ q, M.det ∈ S q := by
    intro q
    let z : ↥(Set.range P)ᶜ → ℤ := fun q' => if q' = q then M.det else 0
    have hz : N.mulVec z = M.mulVec (M.adjugate.mulVec (N.mulVec (Pi.single q 1))) := by
      rw [Matrix.mulVec_mulVec, Matrix.mul_adjugate, Matrix.smul_mulVec, Matrix.one_mulVec]
      funext i
      simp [Matrix.mulVec, dotProduct, z, mul_comm]
    obtain ⟨lam, hl, hlz⟩ := dep_of_blocks c row P hP hrows z _ hz
    exact ⟨lam, hl, by rw [hlz q]; simp [z]⟩
  have ha_ne : ∀ q, a q ≠ 0 := fun q h0 => by
    have := ha_dvd q _ (hdetmem q)
    rw [h0, zero_dvd_iff] at this
    exact hM this
  have ha_large : ∀ q, m + 1 ≤ (a q).natAbs := by
    intro q
    by_contra hlt
    push Not at hlt
    have h1 : 1 ≤ (a q).natAbs := Nat.one_le_iff_ne_zero.mpr (Int.natAbs_ne_zero.mpr (ha_ne q))
    obtain ⟨k, hk⟩ := hG _ h1 (by omega)
    obtain ⟨lam, hl, hlq⟩ := ha_mem q
    have hkill : a q • D q = 0 := by
      have h := sum_smul_pr_eq_zero c (H q) lam hl q
      rw [← add_sum_erase _ _ (mem_univ (q : W)), sum_eq_zero, add_zero, hd, hlq] at h
      · exact h
      · intro v hv
        rw [ho q v (ne_of_mem_erase hv).symm, smul_zero]
    apply hne q
    have hkill' : (((a q).natAbs : ℕ) : ℤ) • D q = 0 := by
      rcases Int.natAbs_eq (a q) with h | h
      · rw [← h]; exact hkill
      · have : (((a q).natAbs : ℕ) : ℤ) = -a q := by omega
        rw [this, neg_smul, hkill, neg_zero]
    rw [hk, mul_smul, smul_comm, hkill', smul_zero]
  have hbound := prod_le_natAbs_det M N hM (fun q => (a q).natAbs)
    (fun z p hzp q => by
      obtain ⟨lam, hl, hlz⟩ := dep_of_blocks c row P hP hrows z p hzp
      have hmem : z q ∈ S q := ⟨lam, hl, hlz q⟩
      exact Int.natAbs_dvd.mpr (ha_dvd q _ hmem))
  refine le_trans ?_ hbound
  calc (m + 1) ^ Fintype.card ↥(Set.range P)ᶜ
      = ∏ _q : ↥(Set.range P)ᶜ, (m + 1) := by simp
    _ ≤ ∏ q, (a q).natAbs := prod_le_prod fun q _ => ha_large q

/-- Lemma 4 with the crude bound `|det M| ≤ ρ!` in place of Hadamard: for entries in `{0, ±1}` and
`m ≥ ρ ≥ 1`, at most `2 ρ` vertices. -/
theorem card_le_two_mul (c : W → ι → ℤ) (H : W → ι → A) (D : W → A)
    (hd : ∀ u, pr c (H u) u u = D u) (ho : ∀ u v, u ≠ v → pr c (H u) u v = 0)
    (G : ℤ) (m : ℕ) (hG : ∀ k : ℕ, 1 ≤ k → k ≤ m → (k : ℤ) ∣ G) (hne : ∀ u, G • D u ≠ 0)
    (row : ρ → ι) (P : ρ → W) (hP : Function.Injective P)
    (hrows : ∀ lam : W → ℤ, (∀ i, ∑ v, lam v * c v (row i) = 0) → IsDep c lam)
    (hM : (Matrix.of fun i j => c (P j) (row i)).det ≠ 0)
    (hent : ∀ v s, |c v s| ≤ 1) (hm : Fintype.card ρ ≤ m) (hm1 : 1 ≤ m) :
    Fintype.card W ≤ 2 * Fintype.card ρ := by
  classical
  have h := visible_count c H D hd ho G m hG hne row P hP hrows hM
  have hdet' : (Matrix.of fun i j => c (P j) (row i)).det.natAbs ≤ (Fintype.card ρ) ^ Fintype.card ρ := by
    have h1 := Matrix.det_le (A := Matrix.of fun i j => c (P j) (row i))
      (abv := (AbsoluteValue.abs : AbsoluteValue ℤ ℤ)) (x := 1) (fun i j => hent (P j) (row i))
    rw [nsmul_eq_mul, one_pow, mul_one] at h1
    change |_| ≤ _ at h1
    rw [Int.abs_eq_natAbs] at h1
    have h2 : (Matrix.of fun i j => c (P j) (row i)).det.natAbs ≤ (Fintype.card ρ).factorial := by
      exact_mod_cast h1
    exact h2.trans (Nat.factorial_le_pow _)
  have hpow : (m + 1) ^ Fintype.card ↥(Set.range P)ᶜ ≤ (m + 1) ^ Fintype.card ρ :=
    h.trans (hdet'.trans (Nat.pow_le_pow_left (by omega) _))
  have hκ : Fintype.card ↥(Set.range P)ᶜ ≤ Fintype.card ρ :=
    (Nat.pow_le_pow_iff_right (by omega)).mp hpow
  have hcard : Fintype.card W = Fintype.card (Set.range P) + Fintype.card ↥(Set.range P)ᶜ := by
    rw [← Fintype.card_sum]
    exact Fintype.card_congr (Equiv.Set.sumCompl (Set.range P)).symm
  have hr : Fintype.card (Set.range P) = Fintype.card ρ := Set.card_range_of_injective hP
  omega

end Visible

section Small

variable {J Q ι : Type*} [Fintype Q] [Fintype ι]

/-- Lemma 5: rounding along integer kernel vectors keeps an integer solution and bounds it by the rational
solution `e'` plus the kernel vectors. -/
theorem round_solution (e₀ : J → ℤ) (e' : J → ℚ) (κ : Q → J → ℤ) (r : Q → ℚ)
    (h : ∀ j, (e₀ j : ℚ) - e' j = ∑ q, r q * κ q j) :
    ∃ e : J → ℤ, (∀ j, e j = e₀ j - ∑ q, ⌊r q⌋ * κ q j) ∧
      ∀ j, |(e j : ℚ)| ≤ |e' j| + ∑ q, |(κ q j : ℚ)| := by
  refine ⟨fun j => e₀ j - ∑ q, ⌊r q⌋ * κ q j, fun _ => rfl, fun j => ?_⟩
  have hcast : ((e₀ j - ∑ q, ⌊r q⌋ * κ q j : ℤ) : ℚ) = e' j + ∑ q, Int.fract (r q) * κ q j := by
    push_cast
    have := h j
    have hf : ∑ q, Int.fract (r q) * (κ q j : ℚ) = ∑ q, r q * κ q j - ∑ q, (⌊r q⌋ : ℚ) * κ q j := by
      rw [← sum_sub_distrib]
      exact sum_congr rfl fun q _ => by rw [Int.fract]; ring
    rw [hf]
    linarith
  simp only
  rw [hcast]
  refine (abs_add_le _ _).trans (add_le_add_right ?_ _)
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun q _ => ?_)
  rw [abs_mul, abs_of_nonneg (Int.fract_nonneg _)]
  have h1 := (Int.fract_lt_one (r q)).le
  calc Int.fract (r q) * |(κ q j : ℚ)| ≤ 1 * |(κ q j : ℚ)| :=
        mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
    _ = _ := one_mul _

omit [Fintype ι] in
/-- A solution in the kernel direction stays a solution. -/
theorem round_solution_mulVec (w : ι → J → ℤ) [Fintype J] (e₀ : J → ℤ) (κ : Q → J → ℤ) (f : Q → ℤ)
    (hκ : ∀ q i, ∑ j, κ q j * w i j = 0) (i : ι) :
    ∑ j, (e₀ j - ∑ q, f q * κ q j) * w i j = ∑ j, e₀ j * w i j := by
  have : ∀ j, (e₀ j - ∑ q, f q * κ q j) * w i j = e₀ j * w i j - ∑ q, f q * (κ q j * w i j) := by
    intro j
    rw [sub_mul, sum_mul]
    congr 1
    exact sum_congr rfl fun q _ => by ring
  simp_rw [this]
  rw [sum_sub_distrib, sum_comm]
  have h0 : ∑ q, ∑ j, f q * (κ q j * w i j) = 0 :=
    sum_eq_zero fun q _ => by rw [← mul_sum, hκ q i, mul_zero]
  rw [h0, sub_zero]

end Small

section Averaging

variable {V Leaf : Type*} [Fintype V] [DecidableEq V] [Fintype Leaf]

/-- Averaging over `v`: if each leaf has at most `y` visible vertices, the average over `v` of the weight of
the leaves not seeing `v` is at least `α (1 - y / n)`. -/
theorem average_visible (p : Leaf → ℝ) (hp : ∀ l, 0 ≤ p l) (Y : Leaf → Finset V) (y : ℕ)
    (hY : ∀ l, (Y l).card ≤ y) :
    (∑ l, p l) * ((Fintype.card V : ℝ) - y) ≤ ∑ v, ∑ l, if v ∈ Y l then 0 else p l := by
  rw [sum_comm, sum_mul]
  refine sum_le_sum fun l _ => ?_
  have h1 : ∑ v, (if v ∈ Y l then 0 else p l) = ((univ \ Y l).card : ℝ) * p l := by
    rw [← sum_filter_add_sum_filter_not univ (· ∈ Y l)]
    have hA : ∑ v ∈ univ.filter (· ∈ Y l), (if v ∈ Y l then (0 : ℝ) else p l) = 0 :=
      sum_eq_zero fun v hv => by simp only [(mem_filter.mp hv).2, ↓reduceIte]
    have hB : ∑ v ∈ univ.filter (· ∉ Y l), (if v ∈ Y l then (0 : ℝ) else p l)
        = ∑ _v ∈ univ.filter (· ∉ Y l), p l :=
      sum_congr rfl fun v hv => by simp only [(mem_filter.mp hv).2, ↓reduceIte]
    have hC : univ.filter (· ∉ Y l) = univ \ Y l := by
      ext v; simp
    rw [hA, hB, hC, zero_add, sum_const, nsmul_eq_mul]
  rw [h1, mul_comm (p l)]
  refine mul_le_mul_of_nonneg_right ?_ (hp l)
  have h2 : (Fintype.card V : ℝ) - y ≤ (Fintype.card V : ℝ) - (Y l).card :=
    sub_le_sub_left (by exact_mod_cast hY l) _
  have h3 : ((univ \ Y l).card : ℝ) = (Fintype.card V : ℝ) - (Y l).card := by
    rw [card_sdiff_of_subset (subset_univ _), card_univ, Nat.cast_sub (card_le_univ _)]
  rw [h3]
  exact h2

/-- The constants of Theorem 7. -/
theorem classical_constants (α x ξ : ℝ) (hα1 : α ≤ 1) (hx : 0 ≤ x) (hξ : ξ ≤ 0.007)
    (herr : (1 / 2) * (1 - α) + (1 / 2) * (α * (1 - x) - ξ) ≤ 1 / 3 + 1 / 100) : 0.30 ≤ x := by
  by_contra h
  push Not at h
  nlinarith [mul_le_mul_of_nonneg_right hα1 hx]

/-- From `(1.5 T + 2.5) / n ≥ 0.30` to `T ≥ n / 5 - 2`. -/
theorem queries_of_ratio (T n : ℝ) (hn : 0 < n) (h : 0.30 ≤ (1.5 * T + 2.5) / n) : n / 5 - 2 ≤ T := by
  rw [le_div_iff₀ hn] at h
  linarith

end Averaging

section Lemma3

variable {E J V ι : Type*} [Fintype E] [Fintype J] [Fintype ι]

omit [Fintype ι] in
/-- Lemma 3: a multiple of `w^v` in the lattice of the `w_j` gives a change invisible to all queries. -/
theorem invisible_change (δ : ι → E → ℤ) (b : J → E → ℤ) (B : E → ℤ) (G : ℤ)
    (hmem : G • (fun s => ∑ i, B i * δ s i)
      ∈ AddSubgroup.closure (Set.range fun j s => ∑ i, b j i * δ s i)) :
    ∃ e : J → ℤ, ∀ s, ∑ i, (G • B - ∑ j, e j • b j) i * δ s i = 0 := by
  rw [← Submodule.span_int_eq_addSubgroupClosure, Submodule.mem_toAddSubgroup,
    Submodule.mem_span_range_iff_exists_fun] at hmem
  obtain ⟨e, he⟩ := hmem
  refine ⟨e, fun s => ?_⟩
  have h := congrFun he s
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_sum] at h
  simp only [Pi.sub_apply, Pi.smul_apply, Finset.sum_apply, smul_eq_mul, sub_mul, sum_sub_distrib, sum_mul]
  have h1 : ∑ i, G * B i * δ s i = ∑ i, G * (B i * δ s i) :=
    sum_congr rfl fun i _ => mul_assoc _ _ _
  have h2 : ∑ j, ∑ i, e j * b j i * δ s i = ∑ j, ∑ i, e j * (b j i * δ s i) :=
    sum_congr rfl fun j _ => sum_congr rfl fun i _ => mul_assoc _ _ _
  rw [sum_comm, h1, h2, h, sub_self]

omit [Fintype E] in
/-- Lemma 3, degrees: the change has the degrees of `G B`. -/
theorem invisible_degree (deg : (E → ℤ) →+ (V → ℤ)) (b : J → E → ℤ) (B : E → ℤ) (G : ℤ) (e : J → ℤ)
    (hb : ∀ j, deg (b j) = 0) : deg (G • B - ∑ j, e j • b j) = G • deg B := by
  rw [map_sub, map_zsmul, map_sum, sum_eq_zero, sub_zero]
  intro j _
  rw [map_zsmul, hb, smul_zero]

end Lemma3

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

omit [Fintype V] in
/-- Lemma 4 for cut queries: vertices visible to the queries `x`, outside the reference vertex `o`, obey
the count of `visible_count` for the vectors `ŷ_v`. -/
theorem lemma4_count (x : ι → V → ℤ) (hx : ∀ s v, x s v = 0 ∨ x s v = 1) (o p q : V)
    (L : AddSubgroup (ι → ℤ))
    (hlab : ∀ a b, a ≠ o → b ≠ o → a ≠ b → labelVec x o p q a b ∈ L)
    (Y : Finset V) (hY : o ∉ Y) (a c : V → V)
    (hac : ∀ u ∈ Y, u ≠ a u ∧ u ≠ c u ∧ a u ≠ c u)
    (G : ℤ) (hvis : ∀ u ∈ Y, G • vertexVec x u (a u) (c u) ∉ L)
    (m : ℕ) (hG : ∀ k : ℕ, 1 ≤ k → k ≤ m → (k : ℤ) ∣ G)
    (row : ρ → Option ι) (P : ρ → Y) (hP : Function.Injective P)
    (hrows : ∀ lam : Y → ℤ, (∀ i, ∑ v, lam v * yhat x o v (row i) = 0) →
      IsDep (fun v : Y => yhat x o v) lam)
    (hM : (Matrix.of fun i j => yhat x o (P j) (row i)).det ≠ 0) :
    (m + 1) ^ Fintype.card ↥(Set.range P)ᶜ
      ≤ (Matrix.of fun i j => yhat x o (P j) (row i)).det.natAbs := by
  have hforms : ∀ u : Y, ∃ (t : ι → AddCircle (1 : ℚ)) (β : V → AddCircle (1 : ℚ)),
      (∀ a b, a ≠ b → cutSum x t a b = β a + β b) ∧ G • ((2 : ℤ) • β u) ≠ 0 := fun u =>
    exists_forms x o p q L hlab G u (a u) (c u) (hac u u.2).1 (hac u u.2).2.1 (hac u u.2).2.2
      (hvis u u.2)
  choose t β hF hne using hforms
  have hu0 : ∀ u : Y, (u : V) ≠ o := fun u h => hY (h ▸ u.2)
  have hF0 : ∀ (u : Y) (a b : V), a ≠ b →
      cutSum x (t u) a b = β u a + β u b + (fun _ _ => (0 : AddCircle (1 : ℚ))) a b := fun u a b h => by
    simpa using hF u a b h
  refine visible_count (fun v : Y => yhat x o v) (fun u => Hhat (t u) (β u o))
    (fun u => (2 : ℤ) • β u u) ?_ ?_ G m hG hne row P hP hrows hM
  · intro u
    have := pr_yhat_diag x (t u) (β u) (fun _ _ => 0) o hx (hF0 u) (hu0 u)
    change pr (yhat x o) (Hhat (t u) (β u o)) (u : V) (u : V) = _
    simpa using this
  · intro u v huv
    have hne' : (u : V) ≠ v := fun h => huv (Subtype.ext h)
    have := pr_yhat_offdiag x (t u) (β u) (fun _ _ => 0) o (fun s => hx s o) (hF0 u) hne' (hu0 u) (hu0 v)
    change pr (yhat x o) (Hhat (t u) (β u o)) (u : V) (v : V) = _
    simpa using this

end Lemma4

section Shifts

/-- Lemma 6, pointwise step: replacing coordinates one at a time. -/
theorem prod_sub_le (J : ℕ) (x y M V : ℕ → ℝ) (h0x : ∀ i, 0 ≤ x i) (h0y : ∀ i, 0 ≤ y i)
    (hM : ∀ i, x i ≤ M i) (hV : ∀ i, |x i - y i| ≤ V i) :
    |∏ i ∈ range J, x i - ∏ i ∈ range J, y i|
      ≤ ∑ j ∈ range J, (∏ i ∈ range j, M i) * V j * ∏ i ∈ Ico (j + 1) J, y i := by
  induction J with
  | zero => simp
  | succ J ih =>
    have hx0 : 0 ≤ ∏ i ∈ range J, x i := prod_nonneg fun i _ => h0x i
    have hxM : ∏ i ∈ range J, x i ≤ ∏ i ∈ range J, M i :=
      prod_le_prod₀ (fun i _ => h0x i) fun i _ => hM i
    have hsplit : ∏ i ∈ range (J + 1), x i - ∏ i ∈ range (J + 1), y i
        = (∏ i ∈ range J, x i) * (x J - y J)
          + (∏ i ∈ range J, x i - ∏ i ∈ range J, y i) * y J := by
      rw [prod_range_succ, prod_range_succ]; ring
    have hRHS : ∑ j ∈ range (J + 1), (∏ i ∈ range j, M i) * V j * ∏ i ∈ Ico (j + 1) (J + 1), y i
        = (∑ j ∈ range J, (∏ i ∈ range j, M i) * V j * ∏ i ∈ Ico (j + 1) J, y i) * y J
          + (∏ i ∈ range J, M i) * V J := by
      rw [sum_range_succ, sum_mul]
      congr 1
      · refine sum_congr rfl fun j hj => ?_
        rw [prod_Ico_succ_top (by have := mem_range.mp hj; omega)]
        ring
      · simp
    rw [hsplit, hRHS, add_comm ((∑ j ∈ range J, _) * y J)]
    refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [abs_mul, abs_of_nonneg hx0]
      exact mul_le_mul hxM (hV J) (abs_nonneg _) (hx0.trans hxM)
    · rw [abs_mul, abs_of_nonneg (h0y J)]
      exact mul_le_mul_of_nonneg_right ih (h0y J)

/-- Lemma 6, the final sum. -/
theorem geom_le (J : ℕ) (u : ℝ) (hu : 0 ≤ u) :
    ∑ j ∈ range J, (1 + u) ^ j * u ≤ (J * u) * Real.exp (J * u) := by
  have hbase : 1 + u ≤ Real.exp u := by linarith [Real.add_one_le_exp u]
  have hterm : ∀ j ∈ range J, (1 + u) ^ j * u ≤ Real.exp (J * u) * u := by
    intro j hj
    refine mul_le_mul_of_nonneg_right ?_ hu
    calc (1 + u) ^ j ≤ (1 + u) ^ J :=
          pow_le_pow_right₀ (by linarith) (mem_range.mp hj).le
      _ ≤ Real.exp u ^ J := pow_le_pow_left₀ (by linarith) hbase _
      _ = Real.exp (J * u) := by rw [← Real.exp_nat_mul]
  calc ∑ j ∈ range J, (1 + u) ^ j * u ≤ ∑ _j ∈ range J, Real.exp (J * u) * u := sum_le_sum hterm
    _ = (J * u) * Real.exp (J * u) := by rw [sum_const, card_range, nsmul_eq_mul]; ring

/-- The value of `ξ` for `η = 1 / (1000 J E)`. -/
theorem xi_value : (0.006 : ℝ) * Real.exp 0.006 ≤ 0.007 := by
  have h := Real.exp_bound_div_one_sub_of_interval (x := 0.006) (by norm_num) (by norm_num)
  have h2 : (1 : ℝ) / (1 - 0.006) ≤ 7 / 6 := by norm_num
  nlinarith [h.trans h2]

end Shifts

end CutQuery
