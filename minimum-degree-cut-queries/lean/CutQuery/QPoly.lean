import CutQuery.Family
import CutQuery.Sparsity
import CutQuery.Counting
import CutQuery.Fejer

/-!
# The low-degree polynomial for the averaged acceptance probability

Write `ω` for `ZMod.stdAddChar`, so `ω (y : ZMod N) = e(y / N)`. Fix a finite family `ι` of integer combinations
`D_i = ∑_s y_i(s) δ_{x_i(s)}` with coefficients `α i`, and consider

  `acc(h, c) = ∑_i α_i ω ⟨A(h, rep c), D_i⟩`,  `A(h, a) = family W₀ G h a`.

`label_expansion` writes this as `∑_u ω (c · u) K_u(h)`, where `K_u` collects the indices with label `u`, the label
being `⟨b_j, D_i⟩ mod N`. Orthogonality on `(ZMod N)^J` bounds `‖K_u(h)‖ ≤ 1` as soon as `‖acc‖ ≤ 1`.
`exists_low_degree` builds the polynomial from `sparsity_cut` and `polynomial_assembly`.
-/

open Finset

namespace CutQuery

local notation "ω" => ZMod.stdAddChar

section Pairing

variable {k : ℕ} {σ : Type*} [Fintype σ]

/-- The pairing `⟨A, ∑_s y_s δ_{x_s}⟩`. -/
def pairing (x : σ → Fin (k + 3) → Bool) (y : σ → ℤ) (A : Weights (k + 3)) : ℤ := ∑ s, y s * cut A (x s)

theorem pairing_family (x : σ → Fin (k + 3) → Bool) (y : σ → ℤ) (W₀ G : ℤ) (h : Fin (k + 3) → Bool)
    (a : LabelIdx k → ℤ) :
    pairing x y (family W₀ G h a) = W₀ * pairing x y (fun _ => 1)
      + G * ∑ v, bitZ (h v) * pairing x y (shiftVec v) + ∑ j, a j * pairing x y (b j) := by
  unfold pairing
  simp_rw [cut_family]
  simp only [mul_add, sum_add_distrib, mul_sum]
  congr 1
  · congr 1
    · exact sum_congr rfl fun s _ => by ring
    · rw [sum_comm]
      exact sum_congr rfl fun v _ => sum_congr rfl fun s _ => by ring
  · rw [sum_comm]
    exact sum_congr rfl fun j _ => sum_congr rfl fun s _ => by ring

theorem pairing_elim {σ' : Type*} [Fintype σ'] (x : σ → Fin (k + 3) → Bool) (y : σ → ℤ)
    (x' : σ' → Fin (k + 3) → Bool) (y' : σ' → ℤ) (A : Weights (k + 3)) :
    pairing (Sum.elim x x') (Sum.elim y fun s => - y' s) A = pairing x y A - pairing x' y' A := by
  unfold pairing
  rw [Fintype.sum_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr, neg_mul, sum_neg_distrib]
  ring

end Pairing

section Circle

variable {N : ℕ} [NeZero N]

/-- The class of `Z / N` in `ℝ / ℤ`. -/
noncomputable def circ (N : ℕ) (Z : ℤ) : AddCircle (1 : ℝ) := (((Z : ℝ) / N : ℝ) : AddCircle (1 : ℝ))

omit [NeZero N] in
theorem sum_zsmul_circ {σ : Type*} [Fintype σ] (c y : σ → ℤ) :
    ∑ s, c s • circ N (y s) = circ N (∑ s, y s * c s) := by
  unfold circ
  have h : (((∑ s, y s * c s : ℤ) : ℝ) / N : ℝ) = ∑ s, c s • ((y s : ℝ) / N) := by
    push_cast
    rw [sum_div]
    refine sum_congr rfl fun s _ => ?_
    rw [zsmul_eq_mul]
    ring
  rw [h]
  let f : ℝ →+ AddCircle (1 : ℝ) := QuotientAddGroup.mk' _
  change ∑ s, c s • f ((y s : ℝ) / N) = f (∑ s, c s • ((y s : ℝ) / N))
  rw [map_sum]
  exact sum_congr rfl fun s _ => (map_zsmul f _ _).symm

omit [NeZero N] in
theorem zsmul_circ (g Z : ℤ) : g • circ N Z = circ N (g * Z) := by
  have := sum_zsmul_circ (N := N) (σ := Unit) (fun _ => g) (fun _ => Z)
  simpa [mul_comm] using this

theorem circ_eq_zero_iff (Z : ℤ) : circ N Z = 0 ↔ (Z : ZMod N) = 0 := by
  have hN : (N : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne N
  unfold circ
  rw [AddCircle.coe_eq_zero_iff, ZMod.intCast_zmod_eq_zero_iff_dvd]
  constructor
  · rintro ⟨l, hl⟩
    refine ⟨l, ?_⟩
    have : (l : ℝ) = (Z : ℝ) / N := by simpa using hl
    rw [eq_div_iff hN] at this
    have h2 : (Z : ℝ) = (N : ℝ) * l := by linarith
    exact_mod_cast h2
  · rintro ⟨l, rfl⟩
    refine ⟨l, ?_⟩
    push_cast
    simp only [zsmul_eq_mul, mul_one]
    field_simp

omit [NeZero N] in
theorem norm_circ (Z : ℤ) : ‖circ N Z‖ = |(Z : ℝ) / N - round ((Z : ℝ) / N)| :=
  UnitAddCircle.norm_eq

theorem norm_circ_le (Z : ℤ) : ‖circ N Z‖ ≤ |((Z : ZMod N).valMinAbs : ℝ)| / N := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  set r := (Z : ZMod N).valMinAbs with hr
  have hzero : circ N (Z - r) = 0 := by
    rw [circ_eq_zero_iff]
    push_cast
    rw [hr, ZMod.coe_valMinAbs]
    ring
  have hsplit : circ N Z = circ N r := by
    have h : circ N (Z - r) = circ N Z - circ N r := by
      unfold circ
      rw [← AddCircle.coe_sub]
      congr 1
      push_cast
      ring
    rw [h, sub_eq_zero] at hzero
    exact hzero
  rw [hsplit, norm_circ]
  have h1 := round_le ((r : ℝ) / N) 0
  simp only [Int.cast_zero, sub_zero] at h1
  rw [abs_div, abs_of_pos hNpos] at h1
  exact h1

/-- A character turns finite sums into products. -/
theorem char_sum {β : Type*} (s : Finset β) (f : β → ZMod N) : ω (∑ i ∈ s, f i) = ∏ i ∈ s, ω (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => rw [sum_insert hi, prod_insert hi, AddChar.map_add_eq_mul, ih]

theorem exp_frac (Z : ℤ) :
    Complex.exp (2 * Real.pi * Complex.I * (((Z : ℝ) / N - round ((Z : ℝ) / N) : ℝ) : ℂ))
      = ω ((Z : ℤ) : ZMod N) := by
  rw [ZMod.stdAddChar_coe]
  push_cast
  have h : 2 * (Real.pi : ℂ) * Complex.I * ((Z : ℂ) / N - (round ((Z : ℝ) / N) : ℂ))
      = 2 * Real.pi * Complex.I * Z / N + (-(round ((Z : ℝ) / N) : ℤ) : ℤ) * (2 * Real.pi * Complex.I) := by
    push_cast
    ring
  rw [h, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

end Circle

section Sparse

variable {k : ℕ} {σ : Type*} [Fintype σ] {N : ℕ}

/-- `sparsity_cut` for a finite index type and integer multipliers divided by `N`. -/
theorem sparsity_pairing (x : σ → Fin (k + 3) → Bool) (y : σ → ℤ) (η : ℝ) (hη : 0 ≤ η)
    (G : ℕ) (hG : ∀ d : ℕ, 1 ≤ d → d ≤ k + 3 → d ∣ G)
    (hlab : ∀ j : LabelIdx k, ‖circ N (pairing x y (b j))‖ ≤ η) :
    (univ.filter fun v : Fin (k + 3) =>
      (G : ℝ) * (((k + 3) ^ 2 * (k + 3).factorial + 3 : ℕ) : ℝ) * η
        < ‖circ N ((G : ℤ) * pairing x y (shiftVec v))‖).card ≤ 2 * Fintype.card σ + 3 := by
  classical
  let e := Fintype.equivFin σ
  have hsum : ∀ A : Weights (k + 3),
      ∑ s : Fin (Fintype.card σ), cut A (x (e.symm s)) • circ N (y (e.symm s)) = circ N (pairing x y A) := by
    intro A
    rw [e.symm.sum_comp (fun s => cut A (x s) • circ N (y s)), sum_zsmul_circ]
    rfl
  have h := sparsity_cut (fun s => x (e.symm s)) (fun s => circ N (y (e.symm s))) η hη G hG
    (fun j => by rw [hsum]; exact hlab j)
  simp only [hsum] at h
  simp only [zsmul_circ] at h
  convert h

end Sparse

section Labels

variable {k N : ℕ} [NeZero N] {ι σ : Type*} [Fintype ι] [Fintype σ]
  (X : ι → σ → Fin (k + 3) → Bool) (Y : ι → σ → ℤ) (α : ι → ℂ) (W₀ G : ℤ)

/-- The label of an index: `⟨b_j, D_i⟩ mod N`. -/
def lab (N : ℕ) (i : ι) (j : LabelIdx k) : ZMod N := ((pairing (X i) (Y i) (b j) : ℤ) : ZMod N)

/-- The sum `∑_i α_i ω ⟨A(h, rep c), D_i⟩`. -/
noncomputable def accFn (h : Fin (k + 3) → Bool) (c : LabelIdx k → ZMod N) : ℂ :=
  ∑ i, α i * ω ((pairing (X i) (Y i) (family W₀ G h fun j => (c j).valMinAbs) : ℤ) : ZMod N)

/-- The part of the sum with label `u`. -/
noncomputable def labelPart (u : LabelIdx k → ZMod N)
    (h : Fin (k + 3) → Bool) : ℂ :=
  ∑ i, if lab X Y N i = u then
    α i * ω ((pairing (X i) (Y i) (family W₀ G h fun _ => 0) : ℤ) : ZMod N) else 0

omit [Fintype ι] in
theorem char_pairing (i : ι) (h : Fin (k + 3) → Bool) (c : LabelIdx k → ZMod N) :
    ω ((pairing (X i) (Y i) (family W₀ G h fun j => (c j).valMinAbs) : ℤ) : ZMod N)
      = ω ((pairing (X i) (Y i) (family W₀ G h fun _ => 0) : ℤ) : ZMod N)
        * ω (∑ j, c j * lab X Y N i j) := by
  rw [← AddChar.map_add_eq_mul]
  congr 1
  rw [pairing_family, pairing_family]
  simp only [zero_mul, sum_const_zero, add_zero]
  push_cast
  congr 1

theorem label_expansion (h : Fin (k + 3) → Bool) (c : LabelIdx k → ZMod N) :
    accFn X Y α W₀ G h c = ∑ u, ω (∑ j, c j * u j) * labelPart X Y α W₀ G u h := by
  unfold accFn labelPart
  simp_rw [mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single (lab X Y N i)]
  · simp only [↓reduceIte]
    rw [char_pairing]
    ring
  · intro u _ hu
    simp [hu.symm]
  · intro hu
    exact absurd (mem_univ _) hu

theorem char_dot (c u : LabelIdx k → ZMod N) :
    ω (∑ j, c j * u j) = ∏ j, ω (c j * u j) :=
  char_sum _ _

/-- Orthogonality on `(ZMod N)^J`. -/
theorem sum_char_dot (v : LabelIdx k → ZMod N) :
    ∑ c : LabelIdx k → ZMod N, ω (∑ j, c j * v j)
      = if v = 0 then ((N : ℂ) ^ Fintype.card (LabelIdx k)) else 0 := by
  classical
  simp_rw [char_dot]
  rw [sum_prod_apply (fun j a => ω (a * v j))]
  simp_rw [AddChar.sum_mulShift _ (ZMod.isPrimitive_stdAddChar N), ZMod.card]
  split_ifs with hv
  · subst hv
    simp [card_univ]
  · obtain ⟨j, hj⟩ := Function.ne_iff.mp hv
    exact prod_eq_zero (mem_univ j) (by simp [show v j ≠ 0 from hj])

/-- Each part is bounded by the supremum of the full sum. -/
theorem norm_labelPart_le (hacc : ∀ h (c : LabelIdx k → ZMod N), ‖accFn X Y α W₀ G h c‖ ≤ 1)
    (u : LabelIdx k → ZMod N) (h : Fin (k + 3) → Bool) : ‖labelPart X Y α W₀ G u h‖ ≤ 1 := by
  classical
  have hNpos : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have hinv : ∑ c : LabelIdx k → ZMod N, ω (- ∑ j, c j * u j) * accFn X Y α W₀ G h c
      = (N : ℂ) ^ Fintype.card (LabelIdx k) * labelPart X Y α W₀ G u h := by
    simp_rw [label_expansion, mul_sum]
    rw [sum_comm]
    have hterm : ∀ u' : LabelIdx k → ZMod N,
        ∑ c : LabelIdx k → ZMod N, ω (- ∑ j, c j * u j) * (ω (∑ j, c j * u' j) * labelPart X Y α W₀ G u' h)
        = (if u' - u = 0 then (N : ℂ) ^ Fintype.card (LabelIdx k) else 0) * labelPart X Y α W₀ G u' h := by
      intro u'
      rw [← sum_char_dot (u' - u), sum_mul]
      refine sum_congr rfl fun c _ => ?_
      rw [← mul_assoc, ← AddChar.map_add_eq_mul]
      congr 2
      simp only [Pi.sub_apply, mul_sub, sum_sub_distrib]
      ring
    simp_rw [hterm]
    rw [Finset.sum_eq_single u]
    · simp
    · intro u' _ hu'
      simp [sub_eq_zero, hu']
    · intro hu'
      exact absurd (mem_univ _) hu'
  have hnorm := congrArg norm hinv
  rw [norm_mul, norm_pow, Complex.norm_natCast] at hnorm
  have hle : ‖∑ c : LabelIdx k → ZMod N, ω (- ∑ j, c j * u j) * accFn X Y α W₀ G h c‖
      ≤ (N : ℝ) ^ Fintype.card (LabelIdx k) := by
    refine (norm_sum_le _ _).trans ?_
    calc ∑ c : LabelIdx k → ZMod N, ‖ω (- ∑ j, c j * u j) * accFn X Y α W₀ G h c‖
        ≤ ∑ _c : LabelIdx k → ZMod N, (1 : ℝ) := sum_le_sum fun c _ => by
          rw [norm_mul, norm_char, one_mul]
          exact hacc h c
      _ = (N : ℝ) ^ Fintype.card (LabelIdx k) := by
          simp [Fintype.card_pi]
  rw [hnorm] at hle
  have hpow : 0 < (N : ℝ) ^ Fintype.card (LabelIdx k) := by positivity
  exact le_of_mul_le_mul_left (by simpa using hle) hpow

/-- The average of the sum under the product Fejér weights. -/
theorem average_accFn (m : ℕ) (hm : 0 < m) (h : Fin (k + 3) → Bool) :
    ∑ c : LabelIdx k → ZMod N, ((∏ j, fejer m (c j) : ℝ) : ℂ) * accFn X Y α W₀ G h c
      = ∑ u : LabelIdx k → ZMod N, ((∏ j, fejerHat m (u j) : ℝ) : ℂ) * labelPart X Y α W₀ G u h := by
  classical
  simp_rw [label_expansion, mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun u _ => ?_
  have h1 : ∀ c : LabelIdx k → ZMod N, ((∏ j, fejer m (c j) : ℝ) : ℂ)
      * (ω (∑ j, c j * u j) * labelPart X Y α W₀ G u h)
      = (∏ j, ((fejer m (c j) : ℂ) * ω (c j * u j))) * labelPart X Y α W₀ G u h := by
    intro c
    rw [char_dot, prod_mul_distrib]
    push_cast
    ring
  simp_rw [h1]
  rw [← sum_mul, sum_prod_apply (fun j a => (fejer m a : ℂ) * ω (a * u j))]
  simp_rw [sum_fejer_mul_char hm]
  push_cast
  rfl

end Labels

section Piece

variable {k N : ℕ} [NeZero N] {ι σ : Type*} [Fintype ι] [Fintype σ]
  (X : ι → σ → Fin (k + 3) → Bool) (Y : ι → σ → ℤ) (α : ι → ℂ) (W₀ : ℤ) (G : ℕ)

/-- The constant `n² n! + 3` of the sparsity lemma. -/
def sparsityConst (k : ℕ) : ℕ := (k + 3) ^ 2 * (k + 3).factorial + 3

omit [Fintype ι] in
/-- For two indices with the same label, few vertices see a nonzero difference. -/
theorem exists_sparse_difference (hG : ∀ d : ℕ, 1 ≤ d → d ≤ k + 3 → d ∣ G) (i i₀ : ι)
    (hi : lab X Y N i = lab X Y N i₀) :
    ∃ Z : Finset (Fin (k + 3)), Z.card ≤ 2 * (2 * Fintype.card σ) + 3 ∧ ∀ v ∉ Z,
      ((((G : ℤ) * (pairing (X i) (Y i) (shiftVec v) - pairing (X i₀) (Y i₀) (shiftVec v)) : ℤ)) : ZMod N) = 0 := by
  classical
  have h := sparsity_pairing (k := k) (N := N) (Sum.elim (X i) (X i₀))
    (Sum.elim (Y i) fun s => - Y i₀ s) 0 le_rfl G hG (by
      intro j
      rw [pairing_elim]
      have h0 : circ N (pairing (X i) (Y i) (b j) - pairing (X i₀) (Y i₀) (b j)) = 0 := by
        rw [circ_eq_zero_iff]
        push_cast
        have := congrFun hi j
        unfold lab at this
        rw [this, sub_self]
      rw [h0, norm_zero])
  rw [Fintype.card_sum, ← two_mul] at h
  refine ⟨_, h, ?_⟩
  intro v hv
  simp only [mem_filter, mem_univ, true_and, mul_zero, not_lt, norm_le_zero_iff] at hv
  rw [pairing_elim] at hv
  exact (circ_eq_zero_iff _).mp hv

omit [Fintype ι] in
/-- For an index whose label is small, few vertices have a large shift value. -/
theorem exists_sparse_reference (hG : ∀ d : ℕ, 1 ≤ d → d ≤ k + 3 → d ∣ G) (m : ℕ) (i₀ : ι)
    (hu : ∀ j, |(lab X Y N i₀ j).valMinAbs| ≤ m) :
    ∃ Z : Finset (Fin (k + 3)), Z.card ≤ 2 * Fintype.card σ + 3 ∧ ∀ v ∉ Z,
      ‖circ N ((G : ℤ) * pairing (X i₀) (Y i₀) (shiftVec v))‖
        ≤ (G : ℝ) * (sparsityConst k : ℝ) * ((m : ℝ) / N) := by
  classical
  have hNpos : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have h := sparsity_pairing (k := k) (N := N) (X i₀) (Y i₀) ((m : ℝ) / N) (by positivity) G hG (by
    intro j
    refine (norm_circ_le _).trans ?_
    have h1 := hu j
    unfold lab at h1
    have h2 : |(((pairing (X i₀) (Y i₀) (b j) : ℤ) : ZMod N).valMinAbs : ℝ)| ≤ (m : ℝ) := by
      exact_mod_cast h1
    exact div_le_div_of_nonneg_right h2 hNpos.le)
  refine ⟨_, h, ?_⟩
  intro v hv
  simp only [mem_filter, mem_univ, true_and, not_lt] at hv
  exact hv

theorem char_int_add (a c : ℤ) :
    ω ((a + c : ℤ) : ZMod N) = ω ((a : ℤ) : ZMod N) * ω ((c : ℤ) : ZMod N) := by
  push_cast
  rw [AddChar.map_add_eq_mul]

/-- The exponential of `∑_v h_v p_v`, where `p_v` reduces `Z_v / N` modulo one. -/
theorem exp_sum_bit (Z : Fin (k + 3) → ℤ) (h : Fin (k + 3) → Bool) :
    Complex.exp (2 * Real.pi * Complex.I *
      ((∑ v, bit (h v) * ((Z v : ℝ) / N - round ((Z v : ℝ) / N)) : ℝ) : ℂ))
      = ω ((∑ v, bitZ (h v) * Z v : ℤ) : ZMod N) := by
  have h1 : (2 * (Real.pi : ℂ) * Complex.I *
      ((∑ v, bit (h v) * ((Z v : ℝ) / N - round ((Z v : ℝ) / N)) : ℝ) : ℂ))
      = ∑ v, (2 * (Real.pi : ℂ) * Complex.I *
        ((bit (h v) * ((Z v : ℝ) / N - round ((Z v : ℝ) / N)) : ℝ) : ℂ)) := by
    rw [Complex.ofReal_sum, mul_sum]
  rw [h1, Complex.exp_sum]
  push_cast
  rw [char_sum]
  refine prod_congr rfl fun v _ => ?_
  have hv := exp_frac (N := N) (Z v)
  cases hb : h v
  · simp [bit, bitZ]
  · have h2 : (((bit true : ℝ) : ℂ)) = 1 := by simp [bit]
    have hz : ((bitZ true : ℤ) : ZMod N) = 1 := by simp [bitZ]
    rw [hz, one_mul, h2, one_mul, ← hv]
    push_cast
    rfl

/-- The factor polynomial evaluates to a character on the cube. -/
theorem eval_factors (Z : Finset (Fin (k + 3))) (e : Fin (k + 3) → ℤ)
    (he : ∀ v ∉ Z, ((e v : ℤ) : ZMod N) = 0) (h : Fin (k + 3) → Bool) :
    MvPolynomial.eval (fun v => (bit (h v) : ℂ))
      (∏ v ∈ Z, ((1 : MvPolynomial (Fin (k + 3)) ℂ)
        + MvPolynomial.C (ω ((e v : ℤ) : ZMod N) - 1) * MvPolynomial.X v))
      = ω ((∑ v, bitZ (h v) * e v : ℤ) : ZMod N) := by
  have hf : ∀ v, MvPolynomial.eval (fun v => (bit (h v) : ℂ))
      ((1 : MvPolynomial (Fin (k + 3)) ℂ) + MvPolynomial.C (ω ((e v : ℤ) : ZMod N) - 1) * MvPolynomial.X v)
      = ω ((bitZ (h v) * e v : ℤ) : ZMod N) := by
    intro v
    simp only [map_add, map_one, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X]
    cases h v <;> simp [bit, bitZ]
  rw [map_prod, prod_congr rfl fun v _ => hf v, Int.cast_sum, char_sum]
  refine prod_subset (subset_univ Z) fun v _ hv => ?_
  push_cast
  rw [he v hv, mul_zero, AddChar.map_zero_eq_one]

/-- One part of the label expansion is a character of `h` times a polynomial of low degree. -/
theorem exists_piece (hG : ∀ d : ℕ, 1 ≤ d → d ≤ k + 3 → d ∣ G) (m : ℕ) (u : LabelIdx k → ZMod N)
    (hu : ∀ j, |(u j).valMinAbs| ≤ m) :
    ∃ (p : Fin (k + 3) → ℝ) (Q : MvPolynomial (Fin (k + 3)) ℂ) (Z : Finset (Fin (k + 3))),
      Q.totalDegree ≤ 2 * (2 * Fintype.card σ) + 3 ∧ Z.card ≤ 2 * Fintype.card σ + 3 ∧
      (∀ v ∉ Z, |p v| ≤ (G : ℝ) * (sparsityConst k : ℝ) * ((m : ℝ) / N)) ∧
      ∀ h : Fin (k + 3) → Bool, labelPart X Y α W₀ (G : ℤ) u h
        = Complex.exp (2 * Real.pi * Complex.I * ((∑ v, bit (h v) * p v : ℝ) : ℂ))
          * MvPolynomial.eval (fun v => (bit (h v) : ℂ)) Q := by
  classical
  have hNpos : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  by_cases hex : ∃ i₀, lab X Y N i₀ = u
  swap
  · refine ⟨0, 0, ∅, by simp, by simp, ?_, ?_⟩
    · intro v _
      simp only [Pi.zero_apply, abs_zero]
      positivity
    · intro h
      simp only [map_zero, mul_zero]
      refine sum_eq_zero fun i _ => ?_
      have : lab X Y N i ≠ u := fun hi => hex ⟨i, hi⟩
      simp [this]
  obtain ⟨i₀, rfl⟩ := hex
  obtain ⟨Z₀, hZ₀c, hZ₀⟩ := exists_sparse_reference X Y G hG m i₀ hu
  have hdiff : ∀ i, ∃ Z : Finset (Fin (k + 3)), lab X Y N i = lab X Y N i₀ →
      Z.card ≤ 2 * (2 * Fintype.card σ) + 3 ∧ ∀ v ∉ Z,
      ((((G : ℤ) * (pairing (X i) (Y i) (shiftVec v) - pairing (X i₀) (Y i₀) (shiftVec v)) : ℤ)) : ZMod N) = 0 := by
    intro i
    by_cases hi : lab X Y N i = lab X Y N i₀
    · obtain ⟨Z, h1, h2⟩ := exists_sparse_difference X Y G hG i i₀ hi
      exact ⟨Z, fun _ => ⟨h1, h2⟩⟩
    · exact ⟨∅, fun h => absurd h hi⟩
  choose Zs hZs using hdiff
  let e : ι → Fin (k + 3) → ℤ := fun i v =>
    (G : ℤ) * (pairing (X i) (Y i) (shiftVec v) - pairing (X i₀) (Y i₀) (shiftVec v))
  let Zr : Fin (k + 3) → ℤ := fun v => (G : ℤ) * pairing (X i₀) (Y i₀) (shiftVec v)
  let piece : ι → MvPolynomial (Fin (k + 3)) ℂ := fun i =>
    MvPolynomial.C (α i * ω ((W₀ * pairing (X i) (Y i) (fun _ => 1) : ℤ) : ZMod N))
      * ∏ v ∈ Zs i, ((1 : MvPolynomial (Fin (k + 3)) ℂ)
        + MvPolynomial.C (ω ((e i v : ℤ) : ZMod N) - 1) * MvPolynomial.X v)
  refine ⟨fun v => (Zr v : ℝ) / N - round ((Zr v : ℝ) / N),
    ∑ i, if lab X Y N i = lab X Y N i₀ then piece i else 0, Z₀, ?_, hZ₀c, ?_, ?_⟩
  · refine MvPolynomial.totalDegree_finsetSum_le fun i _ => ?_
    split_ifs with hi
    · refine (MvPolynomial.totalDegree_mul _ _).trans ?_
      simp only [MvPolynomial.totalDegree_C, zero_add]
      exact (totalDegree_prod_factor (Zs i) _).trans (hZs i hi).1
    · simp
  · intro v hv
    have := hZ₀ v hv
    rwa [norm_circ] at this
  · intro h
    rw [exp_sum_bit Zr h, map_sum, mul_sum]
    unfold labelPart
    refine sum_congr rfl fun i _ => ?_
    split_ifs with hi
    · have hpiece : MvPolynomial.eval (fun v => (bit (h v) : ℂ)) (piece i)
          = α i * ω ((W₀ * pairing (X i) (Y i) (fun _ => 1) : ℤ) : ZMod N)
            * ω ((∑ v, bitZ (h v) * e i v : ℤ) : ZMod N) := by
        simp only [piece, map_mul, MvPolynomial.eval_C]
        rw [eval_factors (Zs i) (e i) (hZs i hi).2 h]
      rw [hpiece]
      have hsum : pairing (X i) (Y i) (family W₀ (G : ℤ) h fun _ => 0)
          = (W₀ * pairing (X i) (Y i) (fun _ => 1) + ∑ v, bitZ (h v) * e i v)
            + ∑ v, bitZ (h v) * Zr v := by
        rw [pairing_family]
        simp only [zero_mul, sum_const_zero, add_zero, e, Zr]
        rw [add_assoc, ← sum_add_distrib, mul_sum]
        congr 1
        refine sum_congr rfl fun v _ => ?_
        ring
      rw [hsum, char_int_add, char_int_add]
      ring
    · simp

end Piece

section Assembly

variable {k N : ℕ} [NeZero N] {ι σ : Type*} [Fintype ι] [Fintype σ]
  (X : ι → σ → Fin (k + 3) → Bool) (Y : ι → σ → ℤ) (α : ι → ℂ) (W₀ : ℤ) (G : ℕ)

/-- The polynomial approximation of the average of `accFn` over the product Fejér weights. -/
theorem exists_low_degree (hG : ∀ d : ℕ, 1 ≤ d → d ≤ k + 3 → d ∣ G) {m : ℕ} (hm : 0 < m) (hmN : 2 * m ≤ N)
    (hacc : ∀ h (c : LabelIdx k → ZMod N), ‖accFn X Y α W₀ (G : ℤ) h c‖ ≤ 1) :
    ∃ Q : MvPolynomial (Fin (k + 3)) ℂ,
      Q.totalDegree ≤ (2 * (2 * Fintype.card σ) + 3) + (2 * Fintype.card σ + 3) ∧
      ∀ h : Fin (k + 3) → Bool,
        ‖(∑ c : LabelIdx k → ZMod N, ((∏ j, fejer m (c j) : ℝ) : ℂ) * accFn X Y α W₀ (G : ℤ) h c)
          - MvPolynomial.eval (fun v => (bit (h v) : ℂ)) Q‖
        ≤ (m : ℝ) ^ Fintype.card (LabelIdx k)
          * (2 * Real.pi * (((k + 3 : ℕ) : ℝ) * ((G : ℝ) * (sparsityConst k : ℝ) * ((m : ℝ) / N)))) := by
  classical
  have hNpos : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  let w : (LabelIdx k → ZMod N) → ℝ := fun u => ∏ j, fejerHat m (u j)
  have hw : ∀ u, 0 ≤ w u := fun u => prod_nonneg fun _ _ => fejerHat_nonneg _ _
  set τ : ℝ := (G : ℝ) * (sparsityConst k : ℝ) * ((m : ℝ) / N) with hτdef
  have hτ : 0 ≤ τ := by positivity
  have hpieces : ∀ u : LabelIdx k → ZMod N, ∃ (p : Fin (k + 3) → ℝ) (Q : MvPolynomial (Fin (k + 3)) ℂ)
      (Z : Finset (Fin (k + 3))),
      Q.totalDegree ≤ 2 * (2 * Fintype.card σ) + 3 ∧ Z.card ≤ 2 * Fintype.card σ + 3 ∧
      (∀ v ∉ Z, |p v| ≤ τ) ∧
      (∀ h : Fin (k + 3) → Bool, ‖MvPolynomial.eval (fun v => (bit (h v) : ℂ)) Q‖ ≤ 1) ∧
      (w u ≠ 0 → ∀ h : Fin (k + 3) → Bool, labelPart X Y α W₀ (G : ℤ) u h
        = Complex.exp (2 * Real.pi * Complex.I * ((∑ v, bit (h v) * p v : ℝ) : ℂ))
          * MvPolynomial.eval (fun v => (bit (h v) : ℂ)) Q) := by
    intro u
    by_cases hu : w u = 0
    · refine ⟨0, 0, ∅, by simp, by simp, ?_, ?_, fun h => absurd hu h⟩
      · intro v _
        simpa using hτ
      · intro h
        simp
    · have hsmall : ∀ j, |(u j).valMinAbs| ≤ m := by
        intro j
        have hj : fejerHat m (u j) ≠ 0 := (prod_ne_zero_iff.mp hu) j (mem_univ j)
        exact (abs_valMinAbs_lt_of_fejerHat_ne_zero hmN hj).le
      obtain ⟨p, Q, Z, h1, h2, h3, h4⟩ := exists_piece X Y α W₀ G hG m u hsmall
      refine ⟨p, Q, Z, h1, h2, h3, ?_, fun _ => h4⟩
      intro h
      have hb := norm_labelPart_le X Y α W₀ (G : ℤ) hacc u h
      rw [h4 h, norm_mul] at hb
      have hexp : ‖Complex.exp (2 * Real.pi * Complex.I * ((∑ v, bit (h v) * p v : ℝ) : ℂ))‖ = 1 := by
        have : 2 * Real.pi * Complex.I * ((∑ v, bit (h v) * p v : ℝ) : ℂ)
            = ((2 * Real.pi * ∑ v, bit (h v) * p v : ℝ) : ℂ) * Complex.I := by
          push_cast
          ring
        rw [this, Complex.norm_exp_ofReal_mul_I]
      rwa [hexp, one_mul] at hb
  choose p Q Z h1 h2 h3 h4 h5 using hpieces
  obtain ⟨Q', hdeg, hQ'⟩ := polynomial_assembly w hw p Q Z _ _ τ hτ h1 h2 h3 h4
  refine ⟨Q', hdeg, fun h => ?_⟩
  have hsumw : ∑ u, w u = (m : ℝ) ^ Fintype.card (LabelIdx k) := by
    simp only [w]
    rw [sum_prod_apply_real (fun _ a => fejerHat m a)]
    simp [sum_fejerHat hm, card_univ]
  have hval := hQ' h
  rw [hsumw, Fintype.card_fin] at hval
  rw [average_accFn X Y α W₀ (G : ℤ) m hm h]
  have heq : ∑ u : LabelIdx k → ZMod N, ((∏ j, fejerHat m (u j) : ℝ) : ℂ) * labelPart X Y α W₀ (G : ℤ) u h
      = ∑ u, (w u : ℂ) * (Complex.exp (2 * Real.pi * Complex.I * ((∑ v, bit (h v) * p u v : ℝ) : ℂ))
          * MvPolynomial.eval (fun v => (bit (h v) : ℂ)) (Q u)) := by
    refine sum_congr rfl fun u _ => ?_
    by_cases hu : w u = 0
    · rw [show (∏ j, fejerHat m (u j)) = 0 from hu, hu]
      simp
    · rw [h5 u hu h]
  rw [heq]
  exact_mod_cast hval

end Assembly


end CutQuery
