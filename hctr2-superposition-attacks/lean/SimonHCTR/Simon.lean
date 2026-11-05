import Mathlib

/-!
# The distribution of one Simon sample

Let `G = (ZMod 2)^D` and `f : G → β`. One run of Simon's circuit returns `y` with
probability `P y = Σ_v (2^{-D} Σ_{x : f x = v} (-1)^{x·y})^2`. With the collision
probabilities `p t = #{x : f (x + t) = f x} / 2^D`:

* `simonProb_eq`: `P y = 2^{-D} Σ_t p t (-1)^{t·y}`;
* `sum_simonProb`: for a subspace `Y`, `Σ_{y ∈ Y} P y = (1/|Y^⊥|) Σ_{t ∈ Y^⊥} p t`;
* `card_mul_card_perp`: `|Y| |Y^⊥| = 2^D`;
* Lemma 4 (`simonProb_eq_zero`, `sum_simonProb_le`, `sum_simonProb_le'`): if `f` is
  invariant under a subspace `S`, then `P` vanishes off `S^⊥`, and if `p t ≤ ε` for
  `t ∉ S` then `Σ_{y ∈ Y} P y ≤ |S|/|Y^⊥| + ε = |Y|/|S^⊥| + ε`;
* Theorem 5, numeric part (`lasVegas_sum_le`): for `0 ≤ ε ≤ 1/8`,
  `Σ_{i=1}^{d} 1/(1 - 2^{-i} - ε) ≤ d + 1.61 + 6 d ε`.
-/

open Finset Matrix

namespace SimonHCTR.Simon

noncomputable section

variable {D : ℕ}

/-- The group `(ZMod 2)^D`. -/
abbrev Vec (D : ℕ) := Fin D → ZMod 2

/-- The character `(-1)^{x·y}` as a real number. -/
def chi (x y : Vec D) : ℝ := if x ⬝ᵥ y = 0 then 1 else -1

theorem zmod2_cases (a : ZMod 2) : a = 0 ∨ a = 1 := by
  revert a; decide

theorem chi_add_left (x x' y : Vec D) : chi (x + x') y = chi x y * chi x' y := by
  unfold chi
  rw [add_dotProduct]
  rcases zmod2_cases (x ⬝ᵥ y) with h | h <;> rcases zmod2_cases (x' ⬝ᵥ y) with h' | h' <;>
    simp [h, h', show (1 : ZMod 2) + 1 = 0 from rfl]

theorem chi_comm (x y : Vec D) : chi x y = chi y x := by
  unfold chi; rw [dotProduct_comm]

theorem chi_add_right (x y y' : Vec D) : chi x (y + y') = chi x y * chi x y' := by
  rw [chi_comm, chi_add_left, chi_comm y, chi_comm y']

theorem chi_mul_self (x y : Vec D) : chi x y * chi x y = 1 := by
  unfold chi; split_ifs <;> norm_num

theorem chi_of_eq_zero {x y : Vec D} (h : x ⬝ᵥ y = 0) : chi x y = 1 := by
  simp [chi, h]

theorem chi_of_ne_zero {x y : Vec D} (h : x ⬝ᵥ y ≠ 0) : chi x y = -1 := by
  simp [chi, h]

open Classical

/-- The orthogonal complement `Y^⊥ = {t : ∀ y ∈ Y, t·y = 0}`. -/
def perp (Y : Submodule (ZMod 2) (Vec D)) : Finset (Vec D) :=
  univ.filter (fun t => ∀ y ∈ Y, t ⬝ᵥ y = 0)

theorem mem_perp {Y : Submodule (ZMod 2) (Vec D)} {t : Vec D} :
    t ∈ perp Y ↔ ∀ y ∈ Y, t ⬝ᵥ y = 0 := by
  simp [perp]

theorem zero_mem_perp (Y : Submodule (ZMod 2) (Vec D)) : (0 : Vec D) ∈ perp Y := by
  simp [mem_perp]

/-- Orthogonality of characters on a subspace: `Σ_{y ∈ Y} (-1)^{t·y} = |Y| [t ∈ Y^⊥]`. -/
theorem sum_chi_subspace (Y : Submodule (ZMod 2) (Vec D)) (t : Vec D) :
    ∑ y : Y, chi t y = if t ∈ perp Y then (Fintype.card Y : ℝ) else 0 := by
  split_ifs with ht
  · rw [mem_perp] at ht
    simp [chi_of_eq_zero (ht _ (Subtype.prop _))]
  · rw [mem_perp] at ht
    push Not at ht
    obtain ⟨y0, hy0, hne⟩ := ht
    set s := ∑ y : Y, chi t y
    have h : s = ∑ y : Y, chi t ((y : Vec D) + y0) :=
      (Fintype.sum_equiv (Equiv.addRight (⟨y0, hy0⟩ : Y)) _ _ (fun y => by simp)).symm
    have h2 : ∑ y : Y, chi t ((y : Vec D) + y0) = -s := by
      simp only [chi_add_right, chi_of_ne_zero hne, mul_neg, mul_one, sum_neg_distrib, s]
    linarith

/-- `Σ_t (-1)^{t·y} = 2^D [y = 0]`. -/
theorem sum_chi_all (y : Vec D) :
    ∑ t : Vec D, chi t y = if y = 0 then (2 : ℝ) ^ D else 0 := by
  split_ifs with hy
  · subst hy
    simp [chi, ZMod.card]
  · obtain ⟨i, hi⟩ : ∃ i, y i ≠ 0 := by
      by_contra h; push Not at h; exact hy (funext h)
    set t0 : Vec D := Pi.single i 1
    have hne : t0 ⬝ᵥ y ≠ 0 := by simpa [t0, single_dotProduct] using hi
    set s := ∑ t : Vec D, chi t y
    have h : s = ∑ t : Vec D, chi (t + t0) y :=
      (Fintype.sum_equiv (Equiv.addRight t0) _ _ (fun t => by simp)).symm
    have h2 : ∑ t : Vec D, chi (t + t0) y = -s := by
      simp only [chi_add_left, chi_of_ne_zero hne, mul_neg, mul_one, sum_neg_distrib, s]
    linarith

/-- `|Y| |Y^⊥| = 2^D`. -/
theorem card_mul_card_perp (Y : Submodule (ZMod 2) (Vec D)) :
    (Fintype.card Y : ℝ) * (perp Y).card = 2 ^ D := by
  have h1 : ∑ t : Vec D, ∑ y : Y, chi t y = (Fintype.card Y : ℝ) * (perp Y).card := by
    have hfilt : univ.filter (fun t => t ∈ perp Y) = perp Y := by ext t; simp
    simp only [sum_chi_subspace]
    rw [← sum_filter, hfilt, sum_const, nsmul_eq_mul]
    ring
  have h2 : ∑ y : Y, ∑ t : Vec D, chi t y = 2 ^ D := by
    simp only [sum_chi_all]
    rw [Fintype.sum_eq_single (0 : Y)]
    · simp
    · intro y hy
      simp [hy]
  rw [← h1, Finset.sum_comm, h2]

theorem card_perp_pos (Y : Submodule (ZMod 2) (Vec D)) : (0 : ℝ) < (perp Y).card := by
  exact_mod_cast Finset.card_pos.2 ⟨0, zero_mem_perp Y⟩

variable {β : Type*} [Fintype β] [DecidableEq β] (f : Vec D → β)

/-- The probability that one Simon sample equals `y`:
`P y = Σ_v (2^{-D} Σ_{x : f x = v} (-1)^{x·y})^2`. -/
def simonProb (y : Vec D) : ℝ :=
  ∑ v : β, (((2 : ℝ) ^ D)⁻¹ * ∑ x ∈ univ.filter (fun x => f x = v), chi x y) ^ 2

/-- The collision probability `p t = Pr_x [f (x + t) = f x]`. -/
def pcoll (t : Vec D) : ℝ :=
  ((univ.filter (fun x => f (x + t) = f x)).card : ℝ) / 2 ^ D

omit [Fintype β] in
theorem pcoll_nonneg (t : Vec D) : 0 ≤ pcoll f t := by
  unfold pcoll; positivity

omit [Fintype β] in
theorem pcoll_le_one (t : Vec D) : pcoll f t ≤ 1 := by
  unfold pcoll
  rw [div_le_one (by positivity)]
  have : ((univ.filter (fun x => f (x + t) = f x)).card : ℝ) ≤ (univ : Finset (Vec D)).card := by
    exact_mod_cast card_filter_le _ _
  simpa [Fintype.card_fun, ZMod.card] using this

/-- The sum of squares of the fibre sums is a sum over pairs `(x, x + t)` in one fibre. -/
theorem sum_fibre_sq (y : Vec D) :
    ∑ v : β, (∑ x ∈ univ.filter (fun x => f x = v), chi x y) ^ 2 =
      ∑ t : Vec D, chi t y * ((univ.filter (fun x => f (x + t) = f x)).card : ℝ) := by
  have step1 : ∀ v : β, (∑ x ∈ univ.filter (fun x => f x = v), chi x y) ^ 2 =
      ∑ x ∈ univ.filter (fun x => f x = v),
        chi x y * ∑ x' ∈ univ.filter (fun x' => f x' = f x), chi x' y := by
    intro v
    rw [sq, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun x hx => ?_)
    rw [(mem_filter.1 hx).2, mul_comm]
  simp only [step1]
  rw [Finset.sum_fiberwise univ f
    (fun x => chi x y * ∑ x' ∈ univ.filter (fun x' => f x' = f x), chi x' y)]
  have step2 : ∀ x : Vec D, chi x y * ∑ x' ∈ univ.filter (fun x' => f x' = f x), chi x' y =
      ∑ t : Vec D, if f (x + t) = f x then chi t y else 0 := by
    intro x
    rw [Finset.sum_filter, Finset.mul_sum]
    refine (Fintype.sum_equiv (Equiv.addLeft x) _ _ (fun t => ?_)).symm
    show (if f (x + t) = f x then chi t y else 0) =
      chi x y * (if f (x + t) = f x then chi (x + t) y else 0)
    by_cases h : f (x + t) = f x
    · simp only [h, ↓reduceIte]
      rw [chi_add_left, ← mul_assoc, chi_mul_self, one_mul]
    · simp only [h, ↓reduceIte, mul_zero]
  simp only [step2]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun t _ => ?_)
  rw [← Finset.sum_filter, sum_const, nsmul_eq_mul, mul_comm]

/-- The formula `P y = 2^{-D} Σ_t p t (-1)^{t·y}`. -/
theorem simonProb_eq (y : Vec D) :
    simonProb f y = ((2 : ℝ) ^ D)⁻¹ * ∑ t : Vec D, pcoll f t * chi t y := by
  unfold simonProb
  simp only [mul_pow]
  rw [← Finset.mul_sum, sum_fibre_sq, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun t _ => ?_)
  unfold pcoll
  field_simp

/-- The Fourier identity: for a subspace `Y`,
`Σ_{y ∈ Y} P y = (1/|Y^⊥|) Σ_{t ∈ Y^⊥} p t`. -/
theorem sum_simonProb (Y : Submodule (ZMod 2) (Vec D)) :
    ∑ y : Y, simonProb f y = (1 / (perp Y).card) * ∑ t ∈ perp Y, pcoll f t := by
  simp only [simonProb_eq]
  rw [← Finset.mul_sum, Finset.sum_comm]
  simp only [← Finset.mul_sum, sum_chi_subspace, mul_ite, mul_zero]
  rw [← Finset.sum_filter]
  have hfilt : univ.filter (fun t => t ∈ perp Y) = perp Y := by ext t; simp
  rw [hfilt, ← Finset.sum_mul]
  have hc := card_mul_card_perp Y
  have hp := card_perp_pos Y
  have h2 : ((2 : ℝ) ^ D)⁻¹ = (1 / (perp Y).card) * (Fintype.card Y : ℝ)⁻¹ := by
    rw [← hc]; field_simp
  have hY : (0 : ℝ) < Fintype.card Y := by exact_mod_cast Fintype.card_pos
  rw [h2]
  field_simp

/-- Lemma 4 (support): if `f` is invariant under the subspace `S`, then `P y = 0` for
`y ∉ S^⊥`. -/
theorem simonProb_eq_zero (S : Submodule (ZMod 2) (Vec D))
    (hinv : ∀ s ∈ S, ∀ x, f (x + s) = f x) (y : Vec D) (hy : ¬ ∀ s ∈ S, s ⬝ᵥ y = 0) :
    simonProb f y = 0 := by
  push Not at hy
  obtain ⟨s0, hs0, hne⟩ := hy
  unfold simonProb
  refine Finset.sum_eq_zero (fun v _ => ?_)
  suffices h : ∑ x ∈ univ.filter (fun x => f x = v), chi x y = 0 by simp [h]
  rw [Finset.sum_filter]
  set s := ∑ x : Vec D, if f x = v then chi x y else 0
  have h : s = ∑ x : Vec D, if f (x + s0) = v then chi (x + s0) y else 0 :=
    (Fintype.sum_equiv (Equiv.addRight s0) _ _ (fun x => rfl)).symm
  have h2 : (∑ x : Vec D, if f (x + s0) = v then chi (x + s0) y else 0) = -s := by
    simp only [hinv s0 hs0, chi_add_left, chi_of_ne_zero hne, mul_neg, mul_one, s,
      ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    split_ifs <;> simp
  linarith

/-- Lemma 4 (bound): if `p t ≤ ε` for every `t ∉ S` (with `ε ≥ 0`), then for every
subspace `Y`, `Σ_{y ∈ Y} P y ≤ |S| / |Y^⊥| + ε`. -/
theorem sum_simonProb_le (S Y : Submodule (ZMod 2) (Vec D)) (ε : ℝ) (hε0 : 0 ≤ ε)
    (hε : ∀ t, t ∉ S → pcoll f t ≤ ε) :
    ∑ y : Y, simonProb f y ≤ Fintype.card S / (perp Y).card + ε := by
  rw [sum_simonProb]
  have hp := card_perp_pos Y
  rw [← Finset.sum_filter_add_sum_filter_not (perp Y) (fun t => t ∈ S)]
  have hA : ∑ t ∈ (perp Y).filter (fun t => t ∈ S), pcoll f t ≤ Fintype.card S := by
    calc ∑ t ∈ (perp Y).filter (fun t => t ∈ S), pcoll f t
        ≤ ∑ t ∈ (perp Y).filter (fun t => t ∈ S), (1 : ℝ) :=
          Finset.sum_le_sum (fun t _ => pcoll_le_one f t)
      _ = (((perp Y).filter (fun t => t ∈ S)).card : ℝ) := by simp
      _ ≤ ((univ.filter (fun t => t ∈ S)).card : ℝ) := by
          exact_mod_cast card_le_card (filter_subset_filter _ (subset_univ _))
      _ = Fintype.card S := by
          rw [Fintype.card_subtype]
  have hB : ∑ t ∈ (perp Y).filter (fun t => t ∉ S), pcoll f t ≤ ε * (perp Y).card := by
    calc ∑ t ∈ (perp Y).filter (fun t => t ∉ S), pcoll f t
        ≤ ∑ t ∈ (perp Y).filter (fun t => t ∉ S), ε :=
          Finset.sum_le_sum (fun t ht => hε t (mem_filter.1 ht).2)
      _ = ε * ((perp Y).filter (fun t => t ∉ S)).card := by
          rw [sum_const, nsmul_eq_mul, mul_comm]
      _ ≤ ε * (perp Y).card := by
          apply mul_le_mul_of_nonneg_left _ hε0
          exact_mod_cast card_filter_le _ _
  rw [one_div_mul_eq_div, div_le_iff₀ hp, add_mul, div_mul_cancel₀ _ hp.ne']
  linarith

/-- Lemma 4 (bound) in the form of the notes: `|S| / |Y^⊥| = |Y| / |S^⊥|`, which is
`2^{j-d}` for `dim Y = j` and `dim S^⊥ = d`. -/
theorem sum_simonProb_le' (S Y : Submodule (ZMod 2) (Vec D)) (ε : ℝ) (hε0 : 0 ≤ ε)
    (hε : ∀ t, t ∉ S → pcoll f t ≤ ε) :
    ∑ y : Y, simonProb f y ≤ Fintype.card Y / (perp S).card + ε := by
  have h := sum_simonProb_le f S Y ε hε0 hε
  have e : (Fintype.card S : ℝ) / (perp Y).card = Fintype.card Y / (perp S).card := by
    have hY := card_mul_card_perp Y
    have hS := card_mul_card_perp S
    have p1 := card_perp_pos Y
    have p2 := card_perp_pos S
    rw [div_eq_div_iff p1.ne' p2.ne']
    linarith
  rwa [e] at h

/-! ## Theorem 5, numeric part -/

theorem term_le (q ε : ℝ) (hq : 2 ≤ q) (h0 : 0 ≤ ε) (h1 : ε ≤ 1 / 8) :
    1 / (1 - 1 / q - ε) ≤ 1 / (1 - 1 / q) + 6 * ε := by
  have hq0 : 0 < q := by linarith
  have ha : 1 / q ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hq
  have ha0 : 0 < 1 / q := by positivity
  set b := 1 - 1 / q with hb
  have hb1 : 1 / 2 ≤ b := by linarith
  have hc : 3 / 8 ≤ b - ε := by linarith
  have hbc : 0 < b * (b - ε) := by positivity
  have key : 1 / (b - ε) - 1 / b = ε / (b * (b - ε)) := by
    field_simp
    ring
  have hle : ε / (b * (b - ε)) ≤ 6 * ε := by
    rw [div_le_iff₀ hbc]
    have h3 : 3 / 16 ≤ b * (b - ε) := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left h3 h0]
  linarith

theorem term_le' (q : ℝ) (hq : 16 ≤ q) :
    1 / (1 - 1 / q) ≤ 1 + 16 / 15 * (1 / q) := by
  have hq0 : 0 < q := by linarith
  have h1 : 1 - 1 / q = (q - 1) / q := by field_simp
  rw [h1, one_div_div, div_le_iff₀ (by linarith)]
  field_simp
  nlinarith

theorem sum_inv_le_aux (k : ℕ) :
    ∑ i ∈ Icc 1 (k + 3), 1 / (1 - 1 / (2 : ℝ) ^ i) ≤
      (k + 3 : ℝ) + 169 / 105 - 16 / 15 * (1 / 2 ^ (k + 3)) := by
  induction k with
  | zero =>
    rw [show (0 + 3 : ℕ) = 3 from rfl, Finset.sum_Icc_succ_top (by norm_num),
      Finset.sum_Icc_succ_top (by norm_num), Finset.Icc_self, Finset.sum_singleton]
    norm_num
  | succ k ih =>
    rw [show k + 1 + 3 = (k + 3) + 1 by ring, Finset.sum_Icc_succ_top (by omega)]
    have h16 : (16 : ℝ) ≤ 2 ^ (k + 3 + 1) := by
      calc (16 : ℝ) = 2 ^ 4 := by norm_num
        _ ≤ 2 ^ (k + 3 + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
    have ht := term_le' _ h16
    have hpow : (1 : ℝ) / 2 ^ (k + 3) = 2 * (1 / 2 ^ (k + 3 + 1)) := by
      rw [pow_succ (2 : ℝ) (k + 3)]; field_simp
    push_cast
    rw [hpow] at ih
    linarith

/-- `Σ_{i=1}^{d} 1/(1 - 2^{-i}) ≤ d + 1.61`. -/
theorem sum_inv_le (d : ℕ) :
    ∑ i ∈ Icc 1 d, 1 / (1 - 1 / (2 : ℝ) ^ i) ≤ d + 161 / 100 := by
  rcases Nat.lt_or_ge d 3 with hd | hd
  · interval_cases d
    · norm_num
    · norm_num
    · rw [Finset.sum_Icc_succ_top (by norm_num), Finset.Icc_self, Finset.sum_singleton]
      norm_num
  · obtain ⟨k, rfl⟩ : ∃ k, d = k + 3 := ⟨d - 3, by omega⟩
    have h := sum_inv_le_aux k
    have hpos : (0 : ℝ) < 16 / 15 * (1 / 2 ^ (k + 3)) := by positivity
    push_cast
    linarith

/-- Theorem 5, numeric part: for `0 ≤ ε ≤ 1/8`,
`Σ_{i=1}^{d} 1/(1 - 2^{-i} - ε) ≤ d + 1.61 + 6 d ε`. -/
theorem lasVegas_sum_le (d : ℕ) (ε : ℝ) (h0 : 0 ≤ ε) (h1 : ε ≤ 1 / 8) :
    ∑ i ∈ Icc 1 d, 1 / (1 - 1 / (2 : ℝ) ^ i - ε) ≤ d + 161 / 100 + 6 * d * ε := by
  calc ∑ i ∈ Icc 1 d, 1 / (1 - 1 / (2 : ℝ) ^ i - ε)
      ≤ ∑ i ∈ Icc 1 d, (1 / (1 - 1 / (2 : ℝ) ^ i) + 6 * ε) := by
        refine Finset.sum_le_sum (fun i hi => term_le _ ε ?_ h0 h1)
        have hi1 : 1 ≤ i := (Finset.mem_Icc.1 hi).1
        calc (2 : ℝ) = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ i := pow_le_pow_right₀ (by norm_num) hi1
    _ = ∑ i ∈ Icc 1 d, 1 / (1 - 1 / (2 : ℝ) ^ i) + 6 * d * ε := by
        rw [Finset.sum_add_distrib, sum_const, Nat.card_Icc, nsmul_eq_mul]
        push_cast; ring
    _ ≤ d + 161 / 100 + 6 * d * ε := by
        have := sum_inv_le d
        linarith

/-- Theorem 5, numeric part, the weaker form `d + 2 + 6 d ε`. -/
theorem lasVegas_sum_le_two (d : ℕ) (ε : ℝ) (h0 : 0 ≤ ε) (h1 : ε ≤ 1 / 8) :
    ∑ i ∈ Icc 1 d, 1 / (1 - 1 / (2 : ℝ) ^ i - ε) ≤ d + 2 + 6 * d * ε := by
  have := lasVegas_sum_le d ε h0 h1
  linarith

end

end SimonHCTR.Simon
