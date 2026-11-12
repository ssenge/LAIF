import CutQuery.Classical

/-!
# Invertible blocks, Cramer dependencies and small solutions

Setting: integer vectors `c v`, `v : W`, indexed by a finite set `ι`.

* `exists_block`: an invertible block on chosen rows and columns, avoiding a given set of columns;
* `exists_cramer_dep`, `abs_cramer_le`: integer dependencies from Cramer's rule and their size;
* `exists_small_solution`: reduction of a solution modulo the block determinant;
* `exists_small_dep`: a dependency attaining the generator of a coordinate with small `ℓ₁` norm;
* `card_le_of_coords`, `exact_card_le`, `near_card_le`: the counting of Lemmas 2 and 4.
-/

open Finset

namespace CutQuery

variable {W ι : Type*} [Fintype W] [DecidableEq W] [Fintype ι]

section ExistsBlock

omit [DecidableEq W] in
/-- An invertible block on columns outside `Avoid`, whose rows control all dependencies. Every vector of
`Avoid` must lie in the rational span of the vectors outside `Avoid`. -/
theorem exists_block (c : W → ι → ℤ) (Avoid : Set W)
    (hAvoid : ∀ u ∈ Avoid, (fun s => (c u s : ℚ)) ∈
      Submodule.span ℚ ((fun v s => (c v s : ℚ)) '' Avoidᶜ)) :
    ∃ (k : ℕ) (row : Fin k → ι) (P : Fin k → W), Function.Injective P ∧ (∀ j, P j ∉ Avoid) ∧
      (Matrix.of fun i j => c (P j) (row i)).det ≠ 0 ∧ k ≤ Fintype.card ι ∧
      ∀ lam : W → ℤ, (∀ i, ∑ v, lam v * c v (row i) = 0) → IsDep c lam := by
  classical
  let cq : W → ι → ℚ := fun v s => (c v s : ℚ)
  obtain ⟨b, hbt, -, hspan, hli⟩ := exists_linearIndepOn_extension (K := ℚ) (v := cq)
    (s := ∅) (t := Avoidᶜ) (linearIndepOn_empty ℚ cq) (Set.empty_subset _)
  have hall : ∀ v, cq v ∈ Submodule.span ℚ (cq '' b) := by
    intro v
    by_cases hv : v ∈ Avoid
    · refine (Submodule.span_le.mpr hspan) (hAvoid v hv)
    · exact hspan ⟨v, hv, rfl⟩
  let e : Fin (Nat.card b) ≃ b := (Finite.equivFin b).symm
  let k := Nat.card b
  let P : Fin k → W := fun j => (e j : W)
  have hPinj : Function.Injective P := fun i j h => e.injective (Subtype.ext h)
  have hPb : cq '' b = Set.range (fun j => cq (P j)) := by
    ext y
    constructor
    · rintro ⟨v, hv, rfl⟩
      exact ⟨e.symm ⟨v, hv⟩, by simp only [P, Equiv.apply_symm_apply]⟩
    · rintro ⟨j, rfl⟩
      exact ⟨P j, (e j).2, rfl⟩
  have hliP : LinearIndependent ℚ (fun j => cq (P j)) :=
    hli.linearIndependent.comp e e.injective
  let A : Matrix ι (Fin k) ℚ := Matrix.of fun i j => cq (P j) i
  have hrank : A.rank = k := by
    have h1 : LinearIndependent ℚ A.transpose.row := hliP
    have h2 := h1.rank_matrix
    rw [Matrix.rank_transpose, Fintype.card_fin] at h2
    exact h2
  obtain ⟨R, -, -, hRspan, hRli⟩ := exists_linearIndepOn_extension (K := ℚ) (v := A.row)
    (s := ∅) (t := Set.univ) (linearIndepOn_empty ℚ A.row) (Set.empty_subset _)
  have hRcard : Nat.card R = k := by
    have h1 := finrank_span_eq_card hRli.linearIndependent
    have h2 : Submodule.span ℚ (Set.range fun x : R => A.row x)
        = Submodule.span ℚ (Set.range A.row) := by
      apply le_antisymm
      · refine Submodule.span_mono ?_
        rintro _ ⟨x, rfl⟩
        exact ⟨x, rfl⟩
      · refine Submodule.span_le.mpr ?_
        rintro _ ⟨i, rfl⟩
        have := hRspan ⟨i, Set.mem_univ i, rfl⟩
        refine Submodule.span_mono ?_ this
        rintro _ ⟨x, hx, rfl⟩
        exact ⟨⟨x, hx⟩, rfl⟩
    rw [h2, ← Matrix.rank_eq_finrank_span_row, hrank] at h1
    rw [Nat.card_eq_fintype_card]
    exact h1.symm
  let e' : Fin k ≃ R := (Finite.equivFinOfCardEq hRcard).symm
  let row : Fin k → ι := fun i => (e' i : ι)
  have hrowinj : Function.Injective row := fun i j h => e'.injective (Subtype.ext h)
  let M : Matrix (Fin k) (Fin k) ℤ := Matrix.of fun i j => c (P j) (row i)
  let Mq : Matrix (Fin k) (Fin k) ℚ := M.map (Int.castRingHom ℚ)
  have hMqli : LinearIndependent ℚ Mq.row := by
    have : Mq.row = fun i => A.row (e' i : ι) := by
      funext i j
      rfl
    rw [this]
    exact hRli.linearIndependent.comp e' e'.injective
  have hMqunit : IsUnit Mq := Matrix.linearIndependent_row_iff_isUnit.mp hMqli
  have hMqdet : Mq.det ≠ 0 := by
    have := (Matrix.isUnit_iff_isUnit_det Mq).mp hMqunit
    exact this.ne_zero
  have hMdet : M.det ≠ 0 := by
    intro h0
    apply hMqdet
    have : Mq.det = (Int.castRingHom ℚ) M.det := (RingHom.map_det (Int.castRingHom ℚ) M).symm
    rw [this, h0, map_zero]
  refine ⟨k, row, P, hPinj, fun j => ?_, hMdet, ?_, ?_⟩
  · exact hbt (e j).2
  · calc k = Fintype.card (Fin k) := (Fintype.card_fin k).symm
      _ ≤ Fintype.card ι := Fintype.card_le_of_injective row hrowinj
  · intro lam hlam s
    have hcomb : ∀ v, ∃ μ : Fin k → ℚ, ∑ j, μ j • cq (P j) = cq v := by
      intro v
      have := hall v
      rw [hPb] at this
      exact (Submodule.mem_span_range_iff_exists_fun ℚ).mp this
    choose μ hμ using hcomb
    let ν : Fin k → ℚ := fun j => ∑ v, (lam v : ℚ) * μ v j
    have hν : ∀ s, ((∑ v, lam v * c v s : ℤ) : ℚ) = ∑ j, ν j * cq (P j) s := by
      intro s
      push_cast
      have h1 : ∀ v, (c v s : ℚ) = ∑ j, μ v j * cq (P j) s := by
        intro v
        have := congrFun (hμ v) s
        simpa [Finset.sum_apply] using this.symm
      simp_rw [h1, mul_sum, ν, sum_mul]
      rw [sum_comm]
      exact sum_congr rfl fun v _ => sum_congr rfl fun j _ => by ring
    have hν0 : ν = 0 := by
      apply Matrix.eq_zero_of_mulVec_eq_zero hMqdet
      funext i
      have h1 := hν (row i)
      rw [hlam i] at h1
      simp only [Matrix.mulVec, dotProduct, Pi.zero_apply]
      have h2 : ∑ j, Mq i j * ν j = ∑ j, ν j * cq (P j) (row i) :=
        sum_congr rfl fun j _ => mul_comm _ _
      rw [h2, ← h1]
      simp
    have h3 := hν s
    rw [hν0] at h3
    simp only [Pi.zero_apply, zero_mul, sum_const_zero] at h3
    exact_mod_cast h3

end ExistsBlock

section Cramer

variable {k : ℕ}

/-- `∑ v, f v` splits into the block columns and the remaining columns. -/
theorem sum_block {P : Fin k → W} (hP : Function.Injective P) (f : W → ℤ) :
    ∑ v, f v = ∑ j, f (P j) + ∑ v ∈ univ \ univ.image P, f v := by
  rw [← sum_sdiff (subset_univ (univ.image P)), sum_image fun _ _ _ _ h => hP h, add_comm]

/-- The vector with values `p` on the block and `z` off it. -/
noncomputable def blockVec (P : Fin k → W) (p : Fin k → ℤ) (z : W → ℤ) : W → ℤ :=
  Function.extend P p z

omit [Fintype W] [DecidableEq W] in
theorem blockVec_block {P : Fin k → W} (hP : Function.Injective P) (p : Fin k → ℤ) (z : W → ℤ)
    (j : Fin k) : blockVec P p z (P j) = p j :=
  hP.extend_apply p z j

theorem blockVec_off {P : Fin k → W} (p : Fin k → ℤ) (z : W → ℤ) {v : W}
    (hv : v ∈ univ \ univ.image P) : blockVec P p z v = z v := by
  apply Function.extend_apply'
  rintro ⟨j, rfl⟩
  exact (mem_sdiff.mp hv).2 (mem_image_of_mem _ (mem_univ _))

omit [Fintype ι] in
/-- The Cramer dependency of a column `q` outside the block: its value at `q` is `det M`, it vanishes
at the other columns outside the block, and on the block it is given by Cramer's rule. -/
theorem exists_cramer_dep (c : W → ι → ℤ) (row : Fin k → ι) (P : Fin k → W) (hP : Function.Injective P)
    (hrows : ∀ lam : W → ℤ, (∀ i, ∑ v, lam v * c v (row i) = 0) → IsDep c lam)
    {q : W} (hq : q ∈ univ \ univ.image P) :
    ∃ κ : W → ℤ, IsDep c κ ∧ κ q = (Matrix.of fun i j => c (P j) (row i)).det ∧
      (∀ v ∈ univ \ univ.image P, v ≠ q → κ v = 0) ∧
      ∀ j, κ (P j) = -(Matrix.of fun i j => c (P j) (row i)).cramer (fun i => c q (row i)) j := by
  set M : Matrix (Fin k) (Fin k) ℤ := Matrix.of fun i j => c (P j) (row i) with hM
  let z : W → ℤ := fun v => if v = q then M.det else 0
  let κ : W → ℤ := blockVec P (fun j => -M.cramer (fun i => c q (row i)) j) z
  have hκq : κ q = M.det := by
    simp only [κ, blockVec_off _ _ hq, z, ↓reduceIte]
  have hκoff : ∀ v ∈ univ \ univ.image P, v ≠ q → κ v = 0 := by
    intro v hv hvq
    simp only [κ, blockVec_off _ _ hv, z, hvq, ↓reduceIte]
  refine ⟨κ, hrows κ ?_, hκq, hκoff, fun j => blockVec_block hP _ _ j⟩
  intro i
  rw [sum_block hP]
  have h1 : ∑ v ∈ univ \ univ.image P, κ v * c v (row i) = M.det * c q (row i) := by
    rw [sum_eq_single q]
    · rw [hκq]
    · intro v hv hvq
      rw [hκoff v hv hvq, zero_mul]
    · intro h
      exact absurd hq h
  have h2 : ∑ j, κ (P j) * c (P j) (row i) = -(M.det * c q (row i)) := by
    have h3 := congrFun (Matrix.mulVec_cramer M (fun i => c q (row i))) i
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at h3
    rw [← h3, ← sum_neg_distrib]
    refine sum_congr rfl fun j _ => ?_
    rw [show κ (P j) = -M.cramer (fun i => c q (row i)) j from blockVec_block hP _ _ j]
    change _ = -(c (P j) (row i) * _)
    ring
  rw [h1, h2]
  ring

/-- A determinant with one column replaced, with all entries bounded by `B`. -/
theorem abs_cramer_le (M : Matrix (Fin k) (Fin k) ℤ) (B : ℕ) (hM : ∀ i j, |M i j| ≤ B)
    (y : Fin k → ℤ) (hy : ∀ i, |y i| ≤ B) (j : Fin k) :
    |M.cramer y j| ≤ (k.factorial : ℤ) * (B : ℤ) ^ k := by
  rw [Matrix.cramer_apply]
  have h := Matrix.det_le (A := M.updateCol j y) (abv := (AbsoluteValue.abs : AbsoluteValue ℤ ℤ))
    (x := (B : ℤ)) (fun a b => by
      rw [Matrix.updateCol_apply]
      split_ifs
      · exact hy a
      · exact hM a b)
  rw [Fintype.card_fin, nsmul_eq_mul] at h
  exact h

theorem abs_det_le (M : Matrix (Fin k) (Fin k) ℤ) (B : ℕ) (hM : ∀ i j, |M i j| ≤ B) :
    |M.det| ≤ (k.factorial : ℤ) * (B : ℤ) ^ k := by
  have h := Matrix.det_le (A := M) (abv := (AbsoluteValue.abs : AbsoluteValue ℤ ℤ))
    (x := (B : ℤ)) hM
  rw [Fintype.card_fin, nsmul_eq_mul] at h
  exact h

omit [Fintype ι] in
/-- Cramer's rule on the block: the values of a solution on the block are determined by its values off the
block. -/
theorem det_mul_block (c : W → ι → ℤ) (row : Fin k → ι) (P : Fin k → W) (hP : Function.Injective P)
    (x : W → ℤ) (t : Fin k → ℤ) (hx : ∀ i, ∑ v, x v * c v (row i) = t i) (j : Fin k) :
    (Matrix.of fun i j => c (P j) (row i)).det * x (P j)
      = (Matrix.of fun i j => c (P j) (row i)).cramer t j
        - ∑ q ∈ univ \ univ.image P,
            x q * (Matrix.of fun i j => c (P j) (row i)).cramer (fun i => c q (row i)) j := by
  set M : Matrix (Fin k) (Fin k) ℤ := Matrix.of fun i j => c (P j) (row i) with hM
  have hmul : M.mulVec (fun j => x (P j))
      = t - ∑ q ∈ univ \ univ.image P, x q • (fun i => c q (row i)) := by
    funext i
    have h1 := hx i
    rw [sum_block hP] at h1
    simp only [Pi.sub_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct]
    rw [← h1, add_sub_cancel_right]
    exact sum_congr rfl fun j _ => mul_comm _ _
  have hcr : M.cramer (M.mulVec (fun j => x (P j))) = M.det • (fun j => x (P j)) := by
    rw [Matrix.cramer_eq_adjugate_mulVec, Matrix.mulVec_mulVec, Matrix.adjugate_mul,
      Matrix.smul_mulVec, Matrix.one_mulVec]
  have h2 := congrFun hcr j
  rw [hmul, map_sub, map_sum] at h2
  simp only [map_smul, Pi.sub_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h2
  exact h2.symm

end Cramer

section Reduce

variable {k : ℕ}

omit [Fintype ι] in
/-- Reduction modulo the block determinant. A solution of `∑ v, x v • c v = g • y` becomes a solution with all
entries bounded by `(|g| + |W|) k! B^k`, keeping the coordinates in `K`, which lie off the block and are at
most `|det M|`. -/
theorem exists_small_solution (c : W → ι → ℤ) (B : ℕ) (hc : ∀ v s, |c v s| ≤ B)
    (row : Fin k → ι) (P : Fin k → W) (hP : Function.Injective P)
    (hrows : ∀ lam : W → ℤ, (∀ i, ∑ v, lam v * c v (row i) = 0) → IsDep c lam)
    (hM : (Matrix.of fun i j => c (P j) (row i)).det ≠ 0)
    (K : Finset W) (hK : K ⊆ univ \ univ.image P) (x₀ : W → ℤ)
    (hK' : ∀ q ∈ K, |x₀ q| ≤ |(Matrix.of fun i j => c (P j) (row i)).det|)
    (y : ι → ℤ) (hy : ∀ s, |y s| ≤ B) (g : ℤ) (hx₀ : ∀ s, ∑ v, x₀ v * c v s = g * y s) :
    ∃ x : W → ℤ, (∀ s, ∑ v, x v * c v s = g * y s) ∧ (∀ q ∈ K, x q = x₀ q) ∧
      ∀ v, |x v| ≤ (|g| + Fintype.card W) * ((k.factorial : ℤ) * (B : ℤ) ^ k) := by
  set M : Matrix (Fin k) (Fin k) ℤ := Matrix.of fun i j => c (P j) (row i) with hMdef
  set D := M.det with hD
  set Q := univ \ univ.image P with hQ
  have hκ : ∀ q : W, ∃ κ : W → ℤ, q ∈ Q → IsDep c κ ∧ κ q = D ∧
      ∀ v ∈ Q, v ≠ q → κ v = 0 := by
    intro q
    by_cases hq : q ∈ Q
    · obtain ⟨κ, h1, h2, h3, -⟩ := exists_cramer_dep c row P hP hrows hq
      exact ⟨κ, fun _ => ⟨h1, h2, h3⟩⟩
    · exact ⟨0, fun h => absurd h hq⟩
  choose κ hκ using hκ
  let S := Q \ K
  let x : W → ℤ := fun v => x₀ v - ∑ q ∈ S, (x₀ q / D) * κ q v
  have hS : ∀ q ∈ S, q ∈ Q := fun q hq => (mem_sdiff.mp hq).1
  have hsol : ∀ s, ∑ v, x v * c v s = g * y s := by
    intro s
    rw [← hx₀ s]
    have h1 : ∀ v, x v * c v s = x₀ v * c v s - ∑ q ∈ S, (x₀ q / D) * (κ q v * c v s) := by
      intro v
      simp only [x]
      rw [sub_mul, sum_mul]
      congr 1
      exact sum_congr rfl fun q _ => by ring
    simp_rw [h1]
    rw [sum_sub_distrib, sum_comm]
    have h0 : ∑ q ∈ S, ∑ v, (x₀ q / D) * (κ q v * c v s) = 0 :=
      sum_eq_zero fun q hq => by
        rw [← mul_sum, (hκ q (hS q hq)).1 s, mul_zero]
    rw [h0, sub_zero]
  have hxQ : ∀ v ∈ S, x v = x₀ v % D := by
    intro v hv
    simp only [x]
    rw [sum_eq_single v]
    · rw [(hκ v (hS v hv)).2.1]
      have := Int.emod_add_mul_ediv (x₀ v) D
      linarith [mul_comm D (x₀ v / D)]
    · intro q hq hqv
      rw [(hκ q (hS q hq)).2.2 v (hS v hv) hqv.symm, mul_zero]
    · intro h
      exact absurd hv h
  have hxK : ∀ q ∈ K, x q = x₀ q := by
    intro q hq
    simp only [x]
    rw [sum_eq_zero, sub_zero]
    intro q' hq'
    have hne : q ≠ q' := fun h => (mem_sdiff.mp hq').2 (h ▸ hq)
    rw [(hκ q' (hS q' hq')).2.2 q (hK hq) hne, mul_zero]
  have hDabs : 1 ≤ |D| := Int.one_le_abs hM
  have hent : ∀ i j, |M i j| ≤ (B : ℤ) := fun i j => hc _ _
  set KK : ℤ := (k.factorial : ℤ) * (B : ℤ) ^ k with hKK
  have hKK0 : 0 ≤ KK := by positivity
  have hDle : |D| ≤ KK := abs_det_le M B hent
  have hxQle : ∀ v ∈ Q, |x v| ≤ |D| := by
    intro v hv
    by_cases hvK : v ∈ K
    · rw [hxK v hvK]
      exact hK' v hvK
    · rw [hxQ v (mem_sdiff.mpr ⟨hv, hvK⟩), abs_of_nonneg (Int.emod_nonneg _ hM)]
      exact (Int.emod_lt_abs _ hM).le
  have hQcard : (Q.card : ℤ) ≤ Fintype.card W := by
    exact_mod_cast card_le_univ Q
  refine ⟨x, hsol, hxK, fun v => ?_⟩
  by_cases hv : v ∈ Q
  · have hr : (1 : ℤ) ≤ Fintype.card W := by
      have : 0 < Fintype.card W := Fintype.card_pos_iff.mpr ⟨v⟩
      exact_mod_cast this
    calc |x v| ≤ |D| := hxQle v hv
      _ ≤ KK := hDle
      _ = 1 * KK := (one_mul _).symm
      _ ≤ (|g| + Fintype.card W) * KK :=
          mul_le_mul_of_nonneg_right (by linarith [abs_nonneg g]) hKK0
  · have hvim : v ∈ univ.image P := by
      by_contra h
      exact hv (mem_sdiff.mpr ⟨mem_univ _, h⟩)
    obtain ⟨j, -, rfl⟩ := mem_image.mp hvim
    have hcr := det_mul_block c row P hP x (fun i => g * y (row i)) (fun i => hsol _) j
    rw [← hMdef, ← hD] at hcr
    have ht : M.cramer (fun i => g * y (row i)) j = g * M.cramer (fun i => y (row i)) j := by
      have : (fun i => g * y (row i)) = g • (fun i => y (row i)) := by
        funext i; simp
      rw [this, map_smul]
      simp
    have h1 : |M.cramer (fun i => y (row i)) j| ≤ KK := abs_cramer_le M B hent _ (fun i => hy _) j
    have h2 : ∀ q ∈ Q, |x q * M.cramer (fun i => c q (row i)) j| ≤ |D| * KK := by
      intro q hq
      rw [abs_mul]
      exact mul_le_mul (hxQle q hq) (abs_cramer_le M B hent _ (fun i => hc _ _) j) (abs_nonneg _)
        (abs_nonneg _)
    have h3 : |∑ q ∈ Q, x q * M.cramer (fun i => c q (row i)) j| ≤ Q.card * (|D| * KK) := by
      refine (abs_sum_le_sum_abs _ _).trans ?_
      refine (sum_le_sum h2).trans ?_
      rw [sum_const, nsmul_eq_mul]
    have h4 : |D| * |x (P j)| ≤ |g| * KK + Q.card * (|D| * KK) := by
      rw [← abs_mul, hcr, ht]
      refine (abs_sub _ _).trans (add_le_add ?_ h3)
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
    have h5 : |D| * |x (P j)| ≤ |D| * ((|g| + Fintype.card W) * KK) := by
      refine h4.trans ?_
      have h6 : |g| * KK ≤ |D| * (|g| * KK) := by
        nlinarith [mul_nonneg (abs_nonneg g) hKK0]
      have h7 : (Q.card : ℤ) * (|D| * KK) ≤ (Fintype.card W : ℤ) * (|D| * KK) :=
        mul_le_mul_of_nonneg_right hQcard (mul_nonneg (abs_nonneg _) hKK0)
      nlinarith
    exact le_of_mul_le_mul_left h5 (by linarith)

end Reduce

section Coordinates

omit [DecidableEq W] [Fintype ι] in
/-- The `u`-coordinates of the dependencies have a nonnegative generator. -/
theorem exists_coord_gen (c : W → ι → ℤ) (u : W) :
    ∃ g : ℤ, 0 ≤ g ∧ (∃ lam, IsDep c lam ∧ lam u = g) ∧ ∀ lam, IsDep c lam → g ∣ lam u := by
  let S : AddSubgroup ℤ :=
    { carrier := {l | ∃ lam : W → ℤ, IsDep c lam ∧ lam u = l}
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
  have : IsAddCyclic S := AddSubgroup.isAddCyclic _
  obtain ⟨g, hg⟩ := IsAddCyclic.exists_generator (α := S)
  have hdvd : ∀ lam, IsDep c lam → (g : ℤ) ∣ lam u := by
    intro lam hl
    obtain ⟨n, hn⟩ := AddSubgroup.mem_zmultiples_iff.mp (hg ⟨lam u, lam, hl, rfl⟩)
    have hn' : n • (g : ℤ) = lam u := congrArg Subtype.val hn
    exact ⟨n, by rw [← hn', smul_eq_mul, mul_comm]⟩
  obtain ⟨lam₀, hl₀, hlu⟩ := g.2
  rcases le_total 0 (g : ℤ) with h0 | h0
  · exact ⟨g, h0, ⟨lam₀, hl₀, hlu⟩, hdvd⟩
  · refine ⟨-g, by omega, ⟨-lam₀, fun s => ?_, by simp [hlu]⟩, fun lam hl => (neg_dvd).mpr (hdvd lam hl)⟩
    have := hl₀ s
    simp only [Pi.neg_apply, neg_mul, sum_neg_distrib]
    omega

/-- A dependency with `λ_u = g`, where `g ≠ 0` divides the `u`-coordinate of every dependency, and with
`ℓ₁` norm at most `r² r!`. -/
theorem exists_small_dep (c : W → ι → ℤ) (hent : ∀ v s, |c v s| ≤ 1) (u : W) (g : ℤ) (hg : g ≠ 0)
    (hg₀ : ∃ lam, IsDep c lam ∧ lam u = g) (hdvd : ∀ lam, IsDep c lam → g ∣ lam u) :
    ∃ lam, IsDep c lam ∧ lam u = g ∧
      ∑ v, |lam v| ≤ ((Fintype.card W : ℤ) ^ 2 * ((Fintype.card W).factorial : ℤ)) := by
  classical
  obtain ⟨lam₀, hl₀, hlu⟩ := hg₀
  let cq : W → ι → ℚ := fun v s => (c v s : ℚ)
  have hAvoid : ∀ w ∈ ({u} : Set W), (fun s => (c w s : ℚ)) ∈
      Submodule.span ℚ ((fun v s => (c v s : ℚ)) '' ({u} : Set W)ᶜ) := by
    intro w hw
    obtain rfl : w = u := hw
    have hsum : ∀ s, (c w s : ℚ) = ∑ v ∈ univ.erase w, (-(lam₀ v : ℚ) / g) • cq v s := by
      intro s
      have h1 := hl₀ s
      rw [← add_sum_erase _ _ (mem_univ w), hlu] at h1
      have h2 : (g : ℚ) * c w s + ∑ v ∈ univ.erase w, (lam₀ v : ℚ) * c v s = 0 := by
        exact_mod_cast h1
      have hg' : (g : ℚ) ≠ 0 := by exact_mod_cast hg
      have h3 : ∑ v ∈ univ.erase w, (-(lam₀ v : ℚ) / g) • cq v s
          = -(1 / (g : ℚ)) * ∑ v ∈ univ.erase w, (lam₀ v : ℚ) * c v s := by
        rw [mul_sum]
        refine sum_congr rfl fun v _ => ?_
        simp only [smul_eq_mul, cq]
        ring
      rw [h3]
      field_simp
      linarith
    have hfun : (fun s => (c w s : ℚ)) = ∑ v ∈ univ.erase w, (-(lam₀ v : ℚ) / g) • cq v := by
      funext s
      rw [hsum s]
      simp [Finset.sum_apply]
    rw [hfun]
    refine Submodule.sum_mem _ fun v hv => Submodule.smul_mem _ _ (Submodule.subset_span ?_)
    exact ⟨v, fun h => (ne_of_mem_erase hv) h, rfl⟩
  obtain ⟨k, row, P, hP, hPA, hM, -, hrows⟩ := exists_block c {u} hAvoid
  set M : Matrix (Fin k) (Fin k) ℤ := Matrix.of fun i j => c (P j) (row i) with hMdef
  have huQ : u ∈ univ \ univ.image P := by
    refine mem_sdiff.mpr ⟨mem_univ _, fun h => ?_⟩
    obtain ⟨j, -, hj⟩ := mem_image.mp h
    exact hPA j hj
  obtain ⟨κ, hκ, hκu, -, -⟩ := exists_cramer_dep c row P hP hrows huQ
  have hgD : g ∣ M.det := hκu ▸ hdvd κ hκ
  have hgle : |g| ≤ |M.det| := by
    have := Int.le_of_dvd (abs_pos.mpr hM) ((abs_dvd_abs _ _).mpr hgD)
    exact this
  obtain ⟨x, hx, hxK, hxb⟩ := exists_small_solution c 1 (by simpa using hent) row P hP hrows hM {u}
    (by simpa using huQ) lam₀ (by simpa [hlu] using hgle) 0 (by simp) 0
    (fun s => by simpa using hl₀ s)
  refine ⟨x, fun s => by simpa using hx s, by simpa [hlu] using hxK u (mem_singleton_self u), ?_⟩
  have hk : k ≤ Fintype.card W := by
    simpa using Fintype.card_le_of_injective P hP
  have hfac : (k.factorial : ℤ) ≤ (Fintype.card W).factorial := by
    exact_mod_cast Nat.factorial_le hk
  have hv : ∀ v, |x v| ≤ (Fintype.card W : ℤ) * ((Fintype.card W).factorial : ℤ) := by
    intro v
    have := hxb v
    simp only [abs_zero, zero_add, Nat.cast_one, one_pow, mul_one] at this
    exact this.trans (mul_le_mul_of_nonneg_left hfac (by positivity))
  calc ∑ v, |x v| ≤ ∑ _v : W, (Fintype.card W : ℤ) * ((Fintype.card W).factorial : ℤ) :=
        sum_le_sum fun v _ => hv v
    _ = (Fintype.card W : ℤ) ^ 2 * ((Fintype.card W).factorial : ℤ) := by
        rw [sum_const, card_univ, nsmul_eq_mul]
        ring

/-- The count: if no small dependency has a coordinate in `[1, m]`, where `m ≥ |W|`, then `|W| ≤ 2 |ι|`. -/
theorem card_le_of_coords (c : W → ι → ℤ) (hent : ∀ v s, |c v s| ≤ 1) (m : ℕ)
    (hm : Fintype.card W ≤ m)
    (hcoord : ∀ (u : W) (lam : W → ℤ), IsDep c lam →
      ∑ v, |lam v| ≤ ((Fintype.card W : ℤ) ^ 2 * ((Fintype.card W).factorial : ℤ)) →
      1 ≤ lam u → lam u ≤ m → False) :
    Fintype.card W ≤ 2 * Fintype.card ι := by
  classical
  obtain ⟨k, row, P, hP, -, hM, hkι, hrows⟩ := exists_block c ∅ (by simp)
  set M : Matrix (Fin k) (Fin k) ℤ := Matrix.of fun i j => c (P j) (row i) with hMdef
  set Q := univ \ univ.image P with hQ
  rcases Nat.eq_zero_or_pos (Fintype.card W) with hW | hW
  · omega
  have hm1 : 1 ≤ m := by omega
  choose g hg0 hgmem hgdvd using exists_coord_gen c
  have hglarge : ∀ q ∈ Q, m + 1 ≤ (g q).natAbs := by
    intro q hq
    obtain ⟨κ, hκ, hκq, -, -⟩ := exists_cramer_dep c row P hP hrows hq
    have hne : g q ≠ 0 := by
      intro h0
      have := hgdvd q κ hκ
      rw [h0, zero_dvd_iff, hκq] at this
      exact hM this
    by_contra hlt
    push Not at hlt
    obtain ⟨lam, hl, hlq, hsmall⟩ := exists_small_dep c hent q (g q) hne (hgmem q) (hgdvd q)
    have h1 : 0 < g q := lt_of_le_of_ne (hg0 q) hne.symm
    refine hcoord q lam hl hsmall ?_ ?_
    · rw [hlq]; omega
    · rw [hlq]; omega
  let N : Matrix (Fin k) ↥Q ℤ := Matrix.of fun i q => c (q : W) (row i)
  have hbound := prod_le_natAbs_det M N hM (fun q : ↥Q => (g q).natAbs) (by
    intro z p hzp q
    let zz : W → ℤ := fun v => if h : v ∈ Q then z ⟨v, h⟩ else 0
    let lam : W → ℤ := blockVec P (fun j => -p j) zz
    have hlamq : ∀ q' : ↥Q, lam q' = z q' := fun q' => by
      simp only [lam, blockVec_off _ _ q'.2, zz, q'.2, ↓reduceDIte]
    have hlam : IsDep c lam := by
      refine hrows lam fun i => ?_
      rw [sum_block hP, ← sum_coe_sort Q]
      simp only [hlamq]
      have h1 := congrFun hzp i
      simp only [Matrix.mulVec, dotProduct] at h1
      have h2 : ∑ j, lam (P j) * c (P j) (row i) = -∑ j, M i j * p j := by
        rw [← sum_neg_distrib]
        refine sum_congr rfl fun j _ => ?_
        rw [show lam (P j) = -p j from blockVec_block hP _ _ j]
        change _ = -(c (P j) (row i) * p j)
        ring
      have h3 : ∑ q : ↥Q, z q * c (q : W) (row i) = ∑ q, N i q * z q :=
        sum_congr rfl fun q _ => mul_comm _ _
      rw [h2, h3, h1]
      ring
    have := hgdvd q lam hlam
    rw [hlamq q] at this
    exact Int.natAbs_dvd.mpr this)
  have hdet : M.det.natAbs ≤ k ^ k := by
    have h1 := abs_det_le M 1 (by simpa [hMdef] using fun i j => hent (P j) (row i))
    simp only [Nat.cast_one, one_pow, mul_one] at h1
    rw [Int.abs_eq_natAbs] at h1
    have h2 : M.det.natAbs ≤ k.factorial := by exact_mod_cast h1
    exact h2.trans (Nat.factorial_le_pow k)
  have hkr : k ≤ Fintype.card W := by
    simpa using Fintype.card_le_of_injective P hP
  have hprod : (m + 1) ^ Q.card ≤ ∏ q : ↥Q, (g q).natAbs := by
    calc (m + 1) ^ Q.card = ∏ _q : ↥Q, (m + 1) := by simp
      _ ≤ ∏ q : ↥Q, (g q).natAbs := prod_le_prod fun q _ => hglarge q q.2
  have hpow : (m + 1) ^ Q.card ≤ (m + 1) ^ k :=
    hprod.trans (hbound.trans (hdet.trans (Nat.pow_le_pow_left (by omega) k)))
  have hκ : Q.card ≤ k := (Nat.pow_le_pow_iff_right (by omega)).mp hpow
  have hcard : Fintype.card W = k + Q.card := by
    have h1 : (univ.image P).card = k := by
      rw [card_image_of_injective _ hP]; simp
    have h2 : Q.card + (univ.image P).card = (univ : Finset W).card :=
      card_sdiff_add_card_eq_card (subset_univ (univ.image P))
    rw [h1, card_univ] at h2
    omega
  omega

end Coordinates

section Counting

variable {A : Type*}

/-- Pairing a dependency with the vector `u` in the form `H`, in the exact case. -/
theorem smul_self_eq_zero [AddCommGroup A] (c : W → ι → ℤ) (H : ι → A) (lam : W → ℤ) (hl : IsDep c lam)
    (u : W) (ho : ∀ v, u ≠ v → pr c H u v = 0) : lam u • pr c H u u = 0 := by
  have h := sum_smul_pr_eq_zero c H lam hl u
  rw [← add_sum_erase _ _ (mem_univ u), sum_eq_zero, add_zero] at h
  · exact h
  · intro v hv
    rw [ho v (ne_of_mem_erase hv).symm, smul_zero]

/-- Pairing a dependency with the vector `u` in the form `H`, in the near case. -/
theorem norm_smul_self_le [SeminormedAddCommGroup A] (c : W → ι → ℤ) (H : ι → A) (lam : W → ℤ) (η : ℝ)
    (hη : 0 ≤ η) (hl : IsDep c lam) (u : W) (ho : ∀ v, u ≠ v → ‖pr c H u v‖ ≤ η) :
    ‖lam u • pr c H u u‖ ≤ (∑ v, |(lam v : ℝ)|) * η := by
  have h := sum_smul_pr_eq_zero c H lam hl u
  rw [← add_sum_erase _ _ (mem_univ u)] at h
  have h' : lam u • pr c H u u = -∑ v ∈ univ.erase u, lam v • pr c H u v := eq_neg_of_add_eq_zero_left h
  rw [h', norm_neg]
  calc ‖∑ v ∈ univ.erase u, lam v • pr c H u v‖
      ≤ ∑ v ∈ univ.erase u, ‖lam v • pr c H u v‖ := norm_sum_le _ _
    _ ≤ ∑ v ∈ univ.erase u, |(lam v : ℝ)| * η := by
        refine sum_le_sum fun v hv => ?_
        have h1 : ‖lam v • pr c H u v‖ ≤ |(lam v : ℝ)| * ‖pr c H u v‖ := by
          have := norm_zsmul_le (lam v) (pr c H u v)
          simpa [Int.norm_eq_abs] using this
        exact h1.trans (mul_le_mul_of_nonneg_left (ho v (ne_of_mem_erase hv).symm) (abs_nonneg _))
    _ ≤ ∑ v, |(lam v : ℝ)| * η :=
        sum_le_sum_of_subset_of_nonneg (erase_subset _ _) fun _ _ _ =>
          mul_nonneg (abs_nonneg _) hη
    _ = (∑ v, |(lam v : ℝ)|) * η := by rw [sum_mul]

/-- The exact count in any abelian group. Each `u` has its own form `H u`, with zero off-diagonal entries at
`u` and `G • D u ≠ 0`, where `G` is divisible by `1, …, m` and `m ≥ |W|`. Then `|W| ≤ 2 |ι|`. -/
theorem exact_card_le [AddCommGroup A] (c : W → ι → ℤ) (hent : ∀ v s, |c v s| ≤ 1) (H : W → ι → A)
    (D : W → A) (hd : ∀ u, pr c (H u) u u = D u) (ho : ∀ u v, u ≠ v → pr c (H u) u v = 0)
    (G : ℤ) (m : ℕ) (hm : Fintype.card W ≤ m) (hG : ∀ d : ℕ, 1 ≤ d → d ≤ m → (d : ℤ) ∣ G)
    (hne : ∀ u, G • D u ≠ 0) :
    Fintype.card W ≤ 2 * Fintype.card ι := by
  refine card_le_of_coords c hent m hm fun u lam hl _ h1 h2 => ?_
  have hkill := smul_self_eq_zero c (H u) lam hl u (ho u)
  rw [hd] at hkill
  lift lam u to ℕ using (by omega) with d hd'
  obtain ⟨l, hl'⟩ := hG d (by omega) (by omega)
  apply hne u
  rw [hl', mul_smul, smul_comm, hkill, smul_zero]

/-- The near count. Each `u` has its own form `H u`, with off-diagonal entries at `u` of norm at most `η`, and
`G (r² r!) η < ‖G • D u‖`, where `G` is divisible by `1, …, m` and `m ≥ r = |W|`. Then `|W| ≤ 2 |ι|`. -/
theorem near_card_le [SeminormedAddCommGroup A] (c : W → ι → ℤ) (hent : ∀ v s, |c v s| ≤ 1)
    (H : W → ι → A) (D : W → A) (η : ℝ) (hη : 0 ≤ η) (hd : ∀ u, pr c (H u) u u = D u)
    (ho : ∀ u v, u ≠ v → ‖pr c (H u) u v‖ ≤ η)
    (G : ℕ) (m : ℕ) (hm : Fintype.card W ≤ m) (hG : ∀ d : ℕ, 1 ≤ d → d ≤ m → d ∣ G)
    (hne : ∀ u, (G : ℝ) * (((Fintype.card W) ^ 2 * (Fintype.card W).factorial : ℕ) : ℝ) * η
      < ‖(G : ℤ) • D u‖) :
    Fintype.card W ≤ 2 * Fintype.card ι := by
  refine card_le_of_coords c hent m hm fun u lam hl hsmall h1 h2 => ?_
  have hnear := norm_smul_self_le c (H u) lam η hη hl u (ho u)
  rw [hd] at hnear
  have hl1 : ∑ v, |(lam v : ℝ)| ≤ (((Fintype.card W) ^ 2 * (Fintype.card W).factorial : ℕ) : ℝ) := by
    have : ((∑ v, |lam v| : ℤ) : ℝ)
        ≤ (((Fintype.card W : ℤ) ^ 2 * ((Fintype.card W).factorial : ℤ) : ℤ) : ℝ) := by
      exact_mod_cast hsmall
    push_cast at this ⊢
    exact this
  have hnear2 : ‖lam u • D u‖ ≤ (((Fintype.card W) ^ 2 * (Fintype.card W).factorial : ℕ) : ℝ) * η :=
    hnear.trans (mul_le_mul_of_nonneg_right hl1 hη)
  lift lam u to ℕ using (by omega) with d hd'
  have hd1 : 1 ≤ d := by omega
  obtain ⟨l, hl'⟩ := hG d hd1 (by omega)
  have hlG : (l : ℝ) ≤ G := by
    rw [hl']
    push_cast
    have hdr : (1 : ℝ) ≤ d := by exact_mod_cast hd1
    nlinarith [(Nat.cast_nonneg l : (0 : ℝ) ≤ l)]
  have h3 : ‖(G : ℤ) • D u‖ ≤ (l : ℝ) * ‖((d : ℕ) : ℤ) • D u‖ := by
    have h4 : (G : ℤ) • D u = (l : ℤ) • (((d : ℕ) : ℤ) • D u) := by
      rw [smul_smul, hl']
      push_cast
      rw [mul_comm]
    rw [h4]
    have := norm_zsmul_le (l : ℤ) (((d : ℕ) : ℤ) • D u)
    simpa [Int.norm_eq_abs] using this
  have h5 := hne u
  have h6 : (l : ℝ) * ‖((d : ℕ) : ℤ) • D u‖
      ≤ (G : ℝ) * ((((Fintype.card W) ^ 2 * (Fintype.card W).factorial : ℕ) : ℝ) * η) :=
    mul_le_mul hlG hnear2 (norm_nonneg _) (Nat.cast_nonneg _)
  rw [mul_assoc] at h5
  linarith

end Counting

end CutQuery
