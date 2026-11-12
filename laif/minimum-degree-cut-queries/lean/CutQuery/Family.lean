import CutQuery.Model

/-!
# The hard family

Vertices are `Fin (k + 3)`. `pairVec u v` is the indicator of the pair `{u, v}`.
-/

open Finset

namespace CutQuery

variable {k : ℕ}

/-- The indicator vector of the pair `{u, v}`. -/
def pairVec (u v : Fin (k + 3)) : Weights (k + 3) := fun f =>
  if (f.1.1 = u ∧ f.1.2 = v) ∨ (f.1.1 = v ∧ f.1.2 = u) then 1 else 0

/-- `b_uv = e_uv - e_0u - e_0v + e_01 + e_02 - e_12`. -/
def labelVector (u v : Fin (k + 3)) : Weights (k + 3) :=
  pairVec u v - pairVec 0 u - pairVec 0 v + pairVec 0 1 + pairVec 0 2 - pairVec 1 2

/-- The index set of the lattice basis: pairs avoiding vertex `0` other than `{1, 2}`. -/
abbrev LabelIdx (k : ℕ) := {f : Edge (k + 3) // f.1.1 ≠ 0 ∧ f.1 ≠ (1, 2)}

/-- The basis vector with index `j`. -/
def b (j : LabelIdx k) : Weights (k + 3) := labelVector j.1.1.1 j.1.1.2

/-- The first helper vertex of `B_v`. -/
def helperA (v : Fin (k + 3)) : Fin (k + 3) := if v = 0 then 1 else 0

/-- The second helper vertex of `B_v`. -/
def helperC (v : Fin (k + 3)) : Fin (k + 3) := if v = 0 ∨ v = 1 then 2 else 1

/-- `B_v = e_va + e_vc - e_ac`, with `deg B_v = 2 e_v`. -/
def shiftVec (v : Fin (k + 3)) : Weights (k + 3) :=
  pairVec v (helperA v) + pairVec v (helperC v) - pairVec (helperA v) (helperC v)

/-- `0` or `1`. -/
def bitZ (b : Bool) : ℤ := if b then 1 else 0

/-- `A(h, a) = W₀ 1 + G ∑ h_v B_v + ∑ a_j b_j`. -/
def family (W₀ G : ℤ) (h : Fin (k + 3) → Bool) (a : LabelIdx k → ℤ) : Weights (k + 3) := fun f =>
  W₀ + G * ∑ v, bitZ (h v) * shiftVec v f + ∑ j, a j * b j f

/-! ## Linearity of `cut` and `degree` -/

section Linear

variable {n : ℕ}

theorem cut_add (A B : Weights n) (x : Fin n → Bool) : cut (A + B) x = cut A x + cut B x := by
  simp only [cut, Pi.add_apply, add_mul, sum_add_distrib]

theorem cut_sub (A B : Weights n) (x : Fin n → Bool) : cut (A - B) x = cut A x - cut B x := by
  simp only [cut, Pi.sub_apply, sub_mul, sum_sub_distrib]

theorem cut_zero (x : Fin n → Bool) : cut (0 : Weights n) x = 0 := by
  simp only [cut, Pi.zero_apply, zero_mul, sum_const_zero]

theorem cut_zsmul (g : ℤ) (A : Weights n) (x : Fin n → Bool) : cut (g • A) x = g * cut A x := by
  simp only [cut, Pi.smul_apply, smul_eq_mul, mul_sum, mul_assoc]

theorem cut_sum {α : Type*} (s : Finset α) (A : α → Weights n) (x : Fin n → Bool) :
    cut (∑ i ∈ s, A i) x = ∑ i ∈ s, cut (A i) x := by
  simp only [cut, Finset.sum_apply, sum_mul]
  rw [sum_comm]

/-- `degree` as the pairing with the indicator of the edges at `v`. -/
theorem degree_eq_sum_mul (A : Weights n) (v : Fin n) :
    degree A v = ∑ e : Edge n, A e * (if e.1.1 = v ∨ e.1.2 = v then 1 else 0) := by
  unfold degree
  exact sum_congr rfl fun e _ => by split_ifs <;> simp

theorem degree_add (A B : Weights n) (v : Fin n) : degree (A + B) v = degree A v + degree B v := by
  simp only [degree_eq_sum_mul, Pi.add_apply, add_mul, sum_add_distrib]

theorem degree_sub (A B : Weights n) (v : Fin n) : degree (A - B) v = degree A v - degree B v := by
  simp only [degree_eq_sum_mul, Pi.sub_apply, sub_mul, sum_sub_distrib]

theorem degree_zsmul (g : ℤ) (A : Weights n) (v : Fin n) : degree (g • A) v = g * degree A v := by
  simp only [degree_eq_sum_mul, Pi.smul_apply, smul_eq_mul, mul_sum, mul_assoc]

theorem degree_sum {α : Type*} (s : Finset α) (A : α → Weights n) (v : Fin n) :
    degree (∑ i ∈ s, A i) v = ∑ i ∈ s, degree (A i) v := by
  simp only [degree_eq_sum_mul, Finset.sum_apply, sum_mul]
  rw [sum_comm]

/-- The degree of a weight given by a function on vertex pairs that is symmetric on distinct pairs. -/
theorem degree_of_symm (w : Fin n → Fin n → ℤ) (hw : ∀ a b, a ≠ b → w a b = w b a) (v : Fin n) :
    degree (fun e : Edge n => w e.1.1 e.1.2) v = ∑ u ∈ univ.erase v, w u v := by
  unfold degree
  rw [← sum_filter]
  refine sum_bij (fun e _ => if e.1.1 = v then e.1.2 else e.1.1) ?_ ?_ ?_ ?_
  · intro e he
    have he' := (mem_filter.mp he).2
    have hlt : e.1.1 < e.1.2 := e.2
    refine mem_erase.mpr ⟨?_, mem_univ _⟩
    split_ifs with h
    · exact fun h' => absurd (h.trans h'.symm) hlt.ne
    · rcases he' with h1 | h1
      · exact absurd h1 h
      · exact fun h' => absurd (h'.trans h1.symm) hlt.ne
  · intro e he e' he' h
    have h1 := (mem_filter.mp he).2
    have h2 := (mem_filter.mp he').2
    have hlt : e.1.1 < e.1.2 := e.2
    have hlt' : e'.1.1 < e'.1.2 := e'.2
    apply Subtype.ext
    apply Prod.ext
    · by_cases ha : e.1.1 = v <;> by_cases hb : e'.1.1 = v
      · exact ha.trans hb.symm
      · simp only [ha, hb, ↓reduceIte] at h
        have h3 : e'.1.2 = v := by tauto
        rw [h3] at hlt'
        rw [← h] at hlt'
        rw [ha] at hlt
        exact absurd (hlt.trans hlt') (lt_irrefl _)
      · simp only [ha, hb, ↓reduceIte] at h
        have h3 : e.1.2 = v := by tauto
        rw [h3, h] at hlt
        rw [hb] at hlt'
        exact absurd (hlt.trans hlt') (lt_irrefl _)
      · simpa only [ha, hb, ↓reduceIte] using h
    · by_cases ha : e.1.1 = v <;> by_cases hb : e'.1.1 = v
      · simpa only [ha, hb, ↓reduceIte] using h
      · simp only [ha, hb, ↓reduceIte] at h
        have h3 : e'.1.2 = v := by tauto
        rw [h3] at hlt'
        rw [← h] at hlt'
        rw [ha] at hlt
        exact absurd (hlt.trans hlt') (lt_irrefl _)
      · simp only [ha, hb, ↓reduceIte] at h
        have h3 : e.1.2 = v := by tauto
        rw [h3, h] at hlt
        rw [hb] at hlt'
        exact absurd (hlt.trans hlt') (lt_irrefl _)
      · have h3 : e.1.2 = v := by tauto
        have h4 : e'.1.2 = v := by tauto
        exact h3.trans h4.symm
  · intro u hu
    have huv : u ≠ v := (mem_erase.mp hu).1
    rcases lt_or_gt_of_ne huv with h | h
    · refine ⟨⟨(u, v), h⟩, mem_filter.mpr ⟨mem_univ _, Or.inr rfl⟩, ?_⟩
      simp only [huv, ↓reduceIte]
    · refine ⟨⟨(v, u), h⟩, mem_filter.mpr ⟨mem_univ _, Or.inl rfl⟩, ?_⟩
      simp only [↓reduceIte]
  · intro e he
    have he' := (mem_filter.mp he).2
    by_cases ha : e.1.1 = v
    · simp only [ha, ↓reduceIte]
      exact hw v e.1.2 (by have : e.1.1 < e.1.2 := e.2; rw [ha] at this; exact this.ne)
    · have h3 : e.1.2 = v := by tauto
      simp only [ha, ↓reduceIte, h3]

/-- The number of edges at a vertex. -/
theorem degree_const_one (v : Fin n) : degree (fun _ : Edge n => (1 : ℤ)) v = (n : ℤ) - 1 := by
  have h := degree_of_symm (n := n) (fun _ _ => 1) (fun _ _ _ => rfl) v
  rw [h, sum_const, card_erase_of_mem (mem_univ _), card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  have hn : 1 ≤ n := by have := v.2; omega
  rw [Nat.cast_sub hn]
  simp

end Linear

/-! ## The pair indicators -/

section Pairs

theorem pairVec_comm (u v : Fin (k + 3)) : pairVec u v = pairVec v u := by
  funext f
  simp only [pairVec, or_comm]

theorem pairVec_self (u : Fin (k + 3)) : pairVec u u = 0 := by
  funext f
  have hlt : f.1.1 < f.1.2 := f.2
  have : ¬ ((f.1.1 = u ∧ f.1.2 = u) ∨ (f.1.1 = u ∧ f.1.2 = u)) := by
    rintro (⟨h1, h2⟩ | ⟨h1, h2⟩) <;> exact hlt.ne (h1.trans h2.symm)
  simp only [pairVec, this, ↓reduceIte, Pi.zero_apply]

/-- Pairing the pair indicator with any function of edges reads off its value at the pair. -/
theorem sum_pairVec_mul {u v : Fin (k + 3)} (huv : u < v) (g : Edge (k + 3) → ℤ) :
    ∑ f, pairVec u v f * g f = g ⟨(u, v), huv⟩ := by
  rw [sum_eq_single (⟨(u, v), huv⟩ : Edge (k + 3))]
  · simp [pairVec]
  · intro f _ hf
    have hlt : f.1.1 < f.1.2 := f.2
    have : ¬ ((f.1.1 = u ∧ f.1.2 = v) ∨ (f.1.1 = v ∧ f.1.2 = u)) := by
      rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · exact hf (Subtype.ext (Prod.ext h1 h2))
      · rw [h1, h2] at hlt
        exact absurd (hlt.trans huv) (lt_irrefl _)
    simp only [pairVec, this, ↓reduceIte, zero_mul]
  · intro h
    exact absurd (mem_univ _) h

/-- For `u ≠ v` the cut of the pair indicator is the crossing indicator; for `u = v` both sides vanish. -/
theorem cut_pairVec (u v : Fin (k + 3)) (x : Fin (k + 3) → Bool) :
    cut (pairVec u v) x = if x u ≠ x v then 1 else 0 := by
  rcases lt_trichotomy u v with h | h | h
  · unfold cut
    rw [sum_pairVec_mul h]
    rfl
  · subst h
    rw [pairVec_self, cut_zero]
    simp
  · rw [pairVec_comm]
    unfold cut
    rw [sum_pairVec_mul h]
    simp only [crosses, ne_comm]

theorem degree_pairVec {u v : Fin (k + 3)} (huv : u ≠ v) (w : Fin (k + 3)) :
    degree (pairVec u v) w = if w = u ∨ w = v then 1 else 0 := by
  rcases lt_or_gt_of_ne huv with h | h
  · rw [degree_eq_sum_mul, sum_pairVec_mul h]
    simp only [eq_comm]
  · rw [pairVec_comm, degree_eq_sum_mul, sum_pairVec_mul h]
    simp only [eq_comm, or_comm]

theorem val_zero' : ((0 : Fin (k + 3)) : ℕ) = 0 := rfl

theorem val_one' : ((1 : Fin (k + 3)) : ℕ) = 1 := by
  change 1 % (k + 3) = 1
  exact Nat.mod_eq_of_lt (by omega)

theorem val_two' : ((2 : Fin (k + 3)) : ℕ) = 2 := by
  change 2 % (k + 3) = 2
  exact Nat.mod_eq_of_lt (by omega)

theorem zero_ne_one' : (0 : Fin (k + 3)) ≠ 1 := by
  rw [Ne, Fin.ext_iff, val_zero', val_one']; omega

theorem zero_ne_two' : (0 : Fin (k + 3)) ≠ 2 := by
  rw [Ne, Fin.ext_iff, val_zero', val_two']; omega

theorem one_ne_two' : (1 : Fin (k + 3)) ≠ 2 := by
  rw [Ne, Fin.ext_iff, val_one', val_two']; omega

theorem helperA_ne (v : Fin (k + 3)) : v ≠ helperA v := by
  unfold helperA
  split_ifs with h
  · rw [h]; exact zero_ne_one'
  · exact h

theorem helperC_ne (v : Fin (k + 3)) : v ≠ helperC v := by
  unfold helperC
  split_ifs with h
  · rcases h with h | h <;> rw [h]
    · exact zero_ne_two'
    · exact one_ne_two'
  · exact fun h' => h (Or.inr h')

theorem helperA_ne_helperC (v : Fin (k + 3)) : helperA v ≠ helperC v := by
  unfold helperA helperC
  split_ifs with h1 h2 h2
  · exact one_ne_two'
  · exact absurd (Or.inl h1) h2
  · exact zero_ne_two'
  · exact zero_ne_one'

end Pairs

/-! ## Cut values of the basis vectors -/

section Cuts

theorem cut_labelVector (u v : Fin (k + 3)) (x : Fin (k + 3) → Bool) :
    cut (labelVector u v) x = cut (pairVec u v) x - cut (pairVec 0 u) x - cut (pairVec 0 v) x
      + cut (pairVec 0 1) x + cut (pairVec 0 2) x - cut (pairVec 1 2) x := by
  simp only [labelVector, cut_add, cut_sub]

theorem cut_shiftVec (v : Fin (k + 3)) (x : Fin (k + 3) → Bool) :
    cut (shiftVec v) x = cut (pairVec v (helperA v)) x + cut (pairVec v (helperC v)) x
      - cut (pairVec (helperA v) (helperC v)) x := by
  simp only [shiftVec, cut_add, cut_sub]

theorem cut_pairVec_nonneg (u v : Fin (k + 3)) (x : Fin (k + 3) → Bool) : 0 ≤ cut (pairVec u v) x := by
  rw [cut_pairVec]; split_ifs <;> simp

theorem cut_pairVec_le_one (u v : Fin (k + 3)) (x : Fin (k + 3) → Bool) : cut (pairVec u v) x ≤ 1 := by
  rw [cut_pairVec]; split_ifs <;> simp

/-- A label vector has cut values of size at most `6`. -/
theorem abs_cut_b_le (j : LabelIdx k) (x : Fin (k + 3) → Bool) : |cut (b j) x| ≤ 6 := by
  unfold b
  rw [cut_labelVector, abs_le]
  have h0 := fun u v => cut_pairVec_nonneg (k := k) u v x
  have h1 := fun u v => cut_pairVec_le_one (k := k) u v x
  have a0 := h0 j.1.1.1 j.1.1.2
  have a1 := h0 0 j.1.1.1
  have a2 := h0 0 j.1.1.2
  have a3 := h0 0 1
  have a4 := h0 0 2
  have a5 := h0 1 2
  have b0 := h1 j.1.1.1 j.1.1.2
  have b1 := h1 0 j.1.1.1
  have b2 := h1 0 j.1.1.2
  have b3 := h1 0 1
  have b4 := h1 0 2
  have b5 := h1 1 2
  constructor <;> omega

/-- A shift vector has cut values of size at most `3`. -/
theorem abs_cut_shiftVec_le (v : Fin (k + 3)) (x : Fin (k + 3) → Bool) : |cut (shiftVec v) x| ≤ 3 := by
  rw [cut_shiftVec, abs_le]
  have h0 := fun u w => cut_pairVec_nonneg (k := k) u w x
  have h1 := fun u w => cut_pairVec_le_one (k := k) u w x
  have a0 := h0 v (helperA v)
  have a1 := h0 v (helperC v)
  have a2 := h0 (helperA v) (helperC v)
  have b0 := h1 v (helperA v)
  have b1 := h1 v (helperC v)
  have b2 := h1 (helperA v) (helperC v)
  constructor <;> omega

end Cuts

/-! ## Entry bounds -/

section Entries

/-- The three edges of `B_v` are distinct, so the entries of `shiftVec` lie in `{0, ±1}`. -/
theorem abs_shiftVec_le_one (v : Fin (k + 3)) (f : Edge (k + 3)) : |shiftVec v f| ≤ 1 := by
  have h1 := helperA_ne v
  have h2 := helperC_ne v
  have h3 := helperA_ne_helperC v
  have hlt : f.1.1 < f.1.2 := f.2
  simp only [shiftVec, pairVec, Pi.add_apply, Pi.sub_apply]
  generalize helperA v = a at *
  generalize helperC v = c at *
  simp only [Fin.ext_iff, Fin.lt_def, ne_eq] at *
  rw [abs_le]
  split_ifs <;> omega

/-- The entries of `b j` lie in `{0, ±1}`: when `u` is `1` or `2` the overlapping terms cancel, and the
index set excludes `{1, 2}`. -/
theorem abs_b_le_one (j : LabelIdx k) (f : Edge (k + 3)) : |b j f| ≤ 1 := by
  obtain ⟨⟨⟨u, v⟩, huv⟩, hu0, hu12⟩ := j
  have hlt : f.1.1 < f.1.2 := f.2
  have huv' : u < v := huv
  have hu0' : u ≠ 0 := hu0
  have hu12' : ¬ (u = 1 ∧ v = 2) := fun h => hu12 (Prod.ext h.1 h.2)
  simp only [b, labelVector, pairVec, Pi.add_apply, Pi.sub_apply]
  simp only [Fin.ext_iff, Fin.lt_def, ne_eq, val_zero', val_one', val_two'] at *
  rw [abs_le]
  split_ifs <;> omega

theorem sum_abs_shiftVec_le (f : Edge (k + 3)) : ∑ v, |shiftVec v f| ≤ (k : ℤ) + 3 := by
  calc ∑ v, |shiftVec v f| ≤ ∑ _v : Fin (k + 3), (1 : ℤ) := sum_le_sum fun v _ => abs_shiftVec_le_one v f
    _ = (k : ℤ) + 3 := by simp

theorem card_labelIdx_le : Fintype.card (LabelIdx k) ≤ (k + 3) ^ 2 := by
  calc Fintype.card (LabelIdx k) ≤ Fintype.card (Edge (k + 3)) := Fintype.card_subtype_le _
    _ ≤ Fintype.card (Fin (k + 3) × Fin (k + 3)) := Fintype.card_subtype_le _
    _ = (k + 3) ^ 2 := by simp [sq]

theorem sum_abs_b_le (f : Edge (k + 3)) :
    ∑ j : LabelIdx k, |b j f| ≤ (Fintype.card (LabelIdx k) : ℤ) := by
  calc ∑ j : LabelIdx k, |b j f| ≤ ∑ _j : LabelIdx k, (1 : ℤ) := sum_le_sum fun j _ => abs_b_le_one j f
    _ = (Fintype.card (LabelIdx k) : ℤ) := by simp

end Entries

/-! ## Degrees of the family -/

section Degrees

theorem degree_b (j : LabelIdx k) (w : Fin (k + 3)) : degree (b j) w = 0 := by
  obtain ⟨⟨⟨u, v⟩, huv⟩, hu0, hu12⟩ := j
  have hlt : u < v := huv
  have hu0' : u ≠ 0 := hu0
  have hv0 : v ≠ 0 := by
    intro h
    rw [h] at hlt
    exact absurd hlt (Fin.not_lt_zero _)
  change degree (labelVector u v) w = 0
  simp only [labelVector, degree_add, degree_sub]
  rw [degree_pairVec hlt.ne, degree_pairVec hu0'.symm, degree_pairVec hv0.symm,
    degree_pairVec zero_ne_one', degree_pairVec zero_ne_two', degree_pairVec one_ne_two']
  simp only [Fin.ext_iff, Fin.lt_def, ne_eq, val_zero', val_one', val_two'] at *
  split_ifs <;> omega

theorem degree_shiftVec (u v : Fin (k + 3)) : degree (shiftVec u) v = if v = u then 2 else 0 := by
  simp only [shiftVec, degree_add, degree_sub]
  rw [degree_pairVec (helperA_ne u), degree_pairVec (helperC_ne u),
    degree_pairVec (helperA_ne_helperC u)]
  have h1 := helperA_ne u
  have h2 := helperC_ne u
  have h3 := helperA_ne_helperC u
  generalize helperA u = a at *
  generalize helperC u = c at *
  simp only [Fin.ext_iff, ne_eq] at *
  split_ifs <;> omega

/-- The cut of a family member, split into its three parts. -/
theorem cut_family (W₀ G : ℤ) (h : Fin (k + 3) → Bool) (a : LabelIdx k → ℤ) (x : Fin (k + 3) → Bool) :
    cut (family W₀ G h a) x = W₀ * cut (fun _ => 1) x + G * ∑ v, bitZ (h v) * cut (shiftVec v) x
      + ∑ j, a j * cut (b j) x := by
  have hf : family W₀ G h a = W₀ • (fun _ => 1) + G • ∑ v, bitZ (h v) • shiftVec v + ∑ j, a j • b j := by
    funext f
    simp [family, Finset.sum_apply]
  rw [hf, cut_add, cut_add, cut_zsmul, cut_zsmul, cut_sum, cut_sum]
  simp only [cut_zsmul]

/-- The degree of a family member. -/
theorem degree_family (W₀ G : ℤ) (h : Fin (k + 3) → Bool) (a : LabelIdx k → ℤ) (v : Fin (k + 3)) :
    degree (family W₀ G h a) v = ((k : ℤ) + 2) * W₀ + 2 * G * bitZ (h v) := by
  have hf : family W₀ G h a = W₀ • (fun _ => 1) + G • ∑ u, bitZ (h u) • shiftVec u + ∑ j, a j • b j := by
    funext f
    simp [family, Finset.sum_apply]
  rw [hf, degree_add, degree_add, degree_zsmul, degree_zsmul, degree_sum, degree_sum,
    degree_const_one]
  simp only [degree_zsmul, degree_b, degree_shiftVec, mul_zero, sum_const_zero, add_zero]
  rw [sum_eq_single v]
  · simp only [↓reduceIte]
    push_cast
    ring
  · intro u _ hu
    simp only [hu.symm, ↓reduceIte, mul_zero]
  · intro hv
    exact absurd (mem_univ _) hv

theorem bitZ_nonneg (β : Bool) : 0 ≤ bitZ β := by
  unfold bitZ; split_ifs <;> simp

/-- The minimum degree of a family member with all bits set. -/
theorem minDegree_family_all_true [NeZero (k + 3)] (W₀ G : ℤ) (a : LabelIdx k → ℤ) :
    minDegree (family W₀ G (fun _ => true) a) = ((k : ℤ) + 2) * W₀ + 2 * G := by
  unfold minDegree
  apply le_antisymm
  · refine (inf'_le _ (mem_univ (0 : Fin (k + 3)))).trans ?_
    rw [degree_family]
    simp [bitZ]
  · refine le_inf' _ _ fun v _ => ?_
    rw [degree_family]
    simp [bitZ]

/-- The minimum degree of a family member with some bit unset. -/
theorem minDegree_family_of_false [NeZero (k + 3)] (W₀ G : ℤ) (hG : 0 ≤ G) (h : Fin (k + 3) → Bool)
    (a : LabelIdx k → ℤ) (v : Fin (k + 3)) (hv : h v = false) :
    minDegree (family W₀ G h a) = ((k : ℤ) + 2) * W₀ := by
  unfold minDegree
  apply le_antisymm
  · refine (inf'_le _ (mem_univ v)).trans ?_
    rw [degree_family, hv]
    simp [bitZ]
  · refine le_inf' _ _ fun u _ => ?_
    rw [degree_family]
    have := mul_nonneg (mul_nonneg (by norm_num : (0 : ℤ) ≤ 2) hG) (bitZ_nonneg (h u))
    linarith

/-- Lemma 3 for the family: clearing the bit of `v` and moving the labels by `γ` does not change the cut
value on a query set whose shift value is a combination of the label values with coefficients `γ`. -/
theorem cut_family_update (W₀ G : ℤ) (h : Fin (k + 3) → Bool) (v : Fin (k + 3)) (hv : h v = true)
    (a γ : LabelIdx k → ℤ) (x : Fin (k + 3) → Bool)
    (hγ : ∑ j, γ j * cut (b j) x = G * cut (shiftVec v) x) :
    cut (family W₀ G (Function.update h v false) (a + γ)) x = cut (family W₀ G h a) x := by
  rw [cut_family, cut_family]
  have h1 : ∑ u, bitZ (h u) * cut (shiftVec u) x
      = ∑ u, bitZ (Function.update h v false u) * cut (shiftVec u) x + cut (shiftVec v) x := by
    rw [← add_sum_erase _ _ (mem_univ v), ← add_sum_erase _ (fun u => bitZ (Function.update h v false u) * _)
      (mem_univ v)]
    have h2 : ∑ u ∈ univ.erase v, bitZ (Function.update h v false u) * cut (shiftVec u) x
        = ∑ u ∈ univ.erase v, bitZ (h u) * cut (shiftVec u) x :=
      sum_congr rfl fun u hu => by rw [Function.update_of_ne (ne_of_mem_erase hu)]
    rw [h2, hv, Function.update_self]
    simp only [bitZ, ↓reduceIte, Bool.false_eq_true]
    ring
  have h3 : ∑ j, (a + γ) j * cut (b j) x = ∑ j, a j * cut (b j) x + ∑ j, γ j * cut (b j) x := by
    rw [← sum_add_distrib]
    exact sum_congr rfl fun j _ => by rw [Pi.add_apply]; ring
  rw [h1, h3, hγ]
  ring

end Degrees

end CutQuery
