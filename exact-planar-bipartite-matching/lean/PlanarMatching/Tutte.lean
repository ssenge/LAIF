import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Combinatorics.SimpleGraph.Tutte

/-!
# The linear algebra of elimination and mates

`notes/GENERAL.md`, Sections 3, 4, 5, over a field `K` and finite index types.
`mate_exists` and `minor_ne_zero_iff` are Lemma 4, `update_inverse` is Lemma 5, `one_step` is Lemma 1.
`rank_schur`, `schur_zero`, `principal_of_row_basis` and `rank_drop` are the steps they use.
`tutte_berge_weak` is the bound used in the proof of the Certificate Theorem.
-/

namespace PlanarMatching

open Matrix Module

variable {K : Type*} [Field K]
variable {l m n o : Type*} [Fintype l] [Fintype m] [Fintype n] [Fintype o]
variable [DecidableEq l] [DecidableEq m] [DecidableEq n] [DecidableEq o]

/-- Skew with zero diagonal. -/
structure IsAlternating (M : Matrix n n K) : Prop where
  skew : Mᵀ = -M
  diag : ∀ i, M i i = 0

omit [Fintype n] [DecidableEq n] in
theorem IsAlternating.apply {M : Matrix n n K} (hM : IsAlternating M) (a b : n) :
    M b a = -M a b := by
  simpa using congrFun (congrFun hM.skew a) b

omit [DecidableEq n] in
/-- An alternating form vanishes on the diagonal, in every characteristic. -/
theorem IsAlternating.quad {M : Matrix n n K} (hM : IsAlternating M) (x : n → K) :
    ∑ a, ∑ b, x a * M a b * x b = 0 := by
  rw [← Finset.sum_product']
  refine Finset.sum_involution (fun p _ => p.swap) ?_ ?_ ?_ ?_
  · rintro ⟨a, b⟩ _
    simp only [Prod.fst_swap, Prod.snd_swap, hM.apply a b]
    ring
  · rintro ⟨a, b⟩ _ hne h
    have hab : b = a := congrArg Prod.fst h
    subst hab
    simp [hM.diag] at hne
  · simp
  · simp

omit [Fintype n] [DecidableEq n] in
theorem IsAlternating.neg {M : Matrix n n K} (hM : IsAlternating M) : IsAlternating (-M) :=
  ⟨by rw [transpose_neg, hM.skew], fun i => by simp [hM.diag]⟩

omit [Fintype n] [DecidableEq n] in
theorem IsAlternating.sub {M N : Matrix n n K} (hM : IsAlternating M) (hN : IsAlternating N) :
    IsAlternating (M - N) :=
  ⟨by rw [transpose_sub, hM.skew, hN.skew, neg_sub_neg, neg_sub],
    fun i => by simp [hM.diag, hN.diag]⟩

omit [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n] in
theorem IsAlternating.submatrix {M : Matrix n n K} (hM : IsAlternating M) (f : m → n) :
    IsAlternating (M.submatrix f f) :=
  ⟨by ext i j; simpa using congrFun (congrFun hM.skew (f i)) (f j), fun i => hM.diag (f i)⟩

omit [Fintype m] [DecidableEq m] [DecidableEq n] in
theorem IsAlternating.conj {M : Matrix n n K} (hM : IsAlternating M) (C : Matrix m n K) :
    IsAlternating (C * M * Cᵀ) := by
  refine ⟨?_, fun i => ?_⟩
  · rw [transpose_mul, transpose_mul, transpose_transpose, hM.skew, Matrix.neg_mul, Matrix.mul_neg,
      Matrix.mul_assoc]
  · simp only [mul_apply, transpose_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
    exact hM.quad (C i)

/-- The inverse of an alternating matrix is alternating. -/
theorem IsAlternating.inv {A : Matrix n n K} (hA : IsAlternating A) (hu : IsUnit A.det) :
    IsAlternating A⁻¹ := by
  have hT : A⁻¹ᵀ = -A⁻¹ := by
    rw [transpose_nonsing_inv, hA.skew]
    exact inv_eq_right_inv (by simp [mul_nonsing_inv A hu])
  have h : A⁻¹ * A * A⁻¹ᵀ = -A⁻¹ := by
    rw [nonsing_inv_mul A hu, Matrix.one_mul, hT]
  refine ⟨hT, fun i => ?_⟩
  have := (hA.conj A⁻¹).diag i
  rw [h] at this
  simpa using this

/-- Lemma 4, first claim. -/
theorem mate_exists {A F : Matrix n n K} (h : A * F = 1) (s : n) : ∃ v, A s v ≠ 0 ∧ F v s ≠ 0 := by
  by_contra! hc
  have h₁ := congrFun (congrFun h s) s
  rw [mul_apply, one_apply_eq, Finset.sum_eq_zero] at h₁
  · exact zero_ne_one h₁
  · intro v _
    by_cases hv : A s v = 0
    · simp [hv]
    · simp [hc v hv]

/-- Jacobi's identity on complementary minors. -/
theorem jacobi_block {A₁₁ F₁₁ : Matrix m m K} {A₁₂ F₁₂ : Matrix m n K} {A₂₁ F₂₁ : Matrix n m K}
    {A₂₂ F₂₂ : Matrix n n K}
    (h : fromBlocks A₁₁ A₁₂ A₂₁ A₂₂ * fromBlocks F₁₁ F₁₂ F₂₁ F₂₂ = 1) :
    (fromBlocks A₁₁ A₁₂ A₂₁ A₂₂).det * F₁₁.det = A₂₂.det := by
  rw [fromBlocks_multiply, ← fromBlocks_one, fromBlocks_inj] at h
  obtain ⟨h₁, -, h₃, -⟩ := h
  have key : fromBlocks A₁₁ A₁₂ A₂₁ A₂₂ * fromBlocks F₁₁ 0 F₂₁ 1 = fromBlocks 1 A₁₂ 0 A₂₂ := by
    simp [fromBlocks_multiply, h₁, h₃]
  simpa [det_mul, det_fromBlocks_zero₁₂, det_fromBlocks_zero₂₁] using congrArg det key

/-- The principal submatrix on a finite set of indices. -/
abbrev principal (M : Matrix n n K) (W : Finset n) : Matrix W W K := M.submatrix (↑) (↑)

/-- A finite set and its complement are a block decomposition of the index type. -/
def splitEquiv (T : Finset n) : T ⊕ ↥Tᶜ ≃ n :=
  (Equiv.sumCongr (Equiv.refl _) (Equiv.subtypeEquivRight fun _ => Finset.mem_compl)).trans
    (Equiv.sumCompl (· ∈ T))

omit [Field K] [Fintype m] [DecidableEq m] [Fintype l] [DecidableEq l] [Fintype n]
  [DecidableEq n] in
/-- A reindexing into blocks. -/
theorem submatrix_sum_eq_fromBlocks {α : Type*} (M : Matrix α α K) (e : m ⊕ l → α) :
    M.submatrix e e = fromBlocks (M.submatrix (e ∘ Sum.inl) (e ∘ Sum.inl))
      (M.submatrix (e ∘ Sum.inl) (e ∘ Sum.inr)) (M.submatrix (e ∘ Sum.inr) (e ∘ Sum.inl))
      (M.submatrix (e ∘ Sum.inr) (e ∘ Sum.inr)) := by
  ext (i | i) (j | j) <;> rfl

/-- Jacobi's identity for principal minors: `det A_{Tᶜ,Tᶜ} = det A · det F_{T,T}`. -/
theorem jacobi_principal {A F : Matrix n n K} (h : A * F = 1) (T : Finset n) :
    A.det * (principal F T).det = (principal A Tᶜ).det := by
  have hk : A.submatrix (splitEquiv T) (splitEquiv T) *
      F.submatrix (splitEquiv T) (splitEquiv T) = 1 := by
    rw [submatrix_mul_equiv, h, submatrix_one_equiv]
  rw [submatrix_sum_eq_fromBlocks, submatrix_sum_eq_fromBlocks F] at hk
  have := jacobi_block hk
  rw [← submatrix_sum_eq_fromBlocks, det_submatrix_equiv_self] at this
  exact this

omit [Fintype n] in
/-- An alternating matrix on a pair has determinant the square of the entry. -/
theorem alternating_two_minor {F : Matrix n n K} (hF : IsAlternating F) {s v : n} (hsv : s ≠ v) :
    (principal F {s, v}).det = F s v ^ 2 := by
  let g : Fin 2 → ({s, v} : Finset n) := ![⟨s, by simp⟩, ⟨v, by simp⟩]
  have hg : Function.Bijective g := by
    refine ⟨?_, ?_⟩
    · intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all [g, Subtype.ext_iff]
    · rintro ⟨x, hx⟩
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
  rw [← det_submatrix_equiv_self (Equiv.ofBijective g hg), det_fin_two]
  have h₁ : F v s = -F s v := hF.apply s v
  simp [g, hF.diag, h₁, sq]

/-- Lemma 4, second claim. -/
theorem minor_ne_zero_iff {A : Matrix n n K} (hA : IsAlternating A) (hu : IsUnit A.det) {s v : n}
    (hsv : s ≠ v) : (principal A ({s, v} : Finset n)ᶜ).det ≠ 0 ↔ A⁻¹ v s ≠ 0 := by
  have hF := hA.inv hu
  rw [← jacobi_principal (mul_nonsing_inv A hu), alternating_two_minor hF hsv, hF.apply v s]
  simp [hu.ne_zero]

/-- Lemma 5, on blocks. -/
theorem update_inverse {A₁₁ F₁₁ : Matrix m m K} {A₁₂ F₁₂ : Matrix m n K} {A₂₁ F₂₁ : Matrix n m K}
    {A₂₂ F₂₂ : Matrix n n K}
    (h : fromBlocks A₁₁ A₁₂ A₂₁ A₂₂ * fromBlocks F₁₁ F₁₂ F₂₁ F₂₂ = 1) (hF : IsUnit F₁₁.det) :
    IsUnit A₂₂.det ∧ A₂₂⁻¹ = F₂₂ - F₂₁ * F₁₁⁻¹ * F₁₂ := by
  have h' := mul_eq_one_comm.mp h
  rw [fromBlocks_multiply, ← fromBlocks_one, fromBlocks_inj] at h'
  obtain ⟨-, h₂, -, h₄⟩ := h'
  have hA₁₂ : A₁₂ = -(F₁₁⁻¹ * F₁₂ * A₂₂) := by
    have h₅ : F₁₁⁻¹ * (F₁₁ * A₁₂ + F₁₂ * A₂₂) = 0 := by rw [h₂, Matrix.mul_zero]
    rw [Matrix.mul_add, nonsing_inv_mul_cancel_left _ _ hF, ← Matrix.mul_assoc] at h₅
    exact eq_neg_of_add_eq_zero_left h₅
  have key : (F₂₂ - F₂₁ * F₁₁⁻¹ * F₁₂) * A₂₂ = 1 := by
    rw [hA₁₂] at h₄
    rw [← h₄, Matrix.sub_mul, Matrix.mul_neg, sub_eq_neg_add]
    simp only [Matrix.mul_assoc]
  exact ⟨isUnit_det_of_left_inverse key, inv_eq_left_inv key⟩

/-- Lemma 5 on principal submatrices. -/
theorem update_inverse_principal {A F : Matrix n n K} (h : A * F = 1) (R : Finset n)
    (hR : IsUnit (principal F R).det) :
    IsUnit (principal A Rᶜ).det ∧ (principal A Rᶜ)⁻¹ = principal F Rᶜ -
      F.submatrix ((↑) : ↥Rᶜ → n) ((↑) : R → n) * (principal F R)⁻¹ *
        F.submatrix ((↑) : R → n) ((↑) : ↥Rᶜ → n) := by
  have hk : A.submatrix (splitEquiv R) (splitEquiv R) *
      F.submatrix (splitEquiv R) (splitEquiv R) = 1 := by
    rw [submatrix_mul_equiv, h, submatrix_one_equiv]
  rw [submatrix_sum_eq_fromBlocks, submatrix_sum_eq_fromBlocks F] at hk
  exact update_inverse hk hR

omit [Fintype l] [Fintype o] [DecidableEq l] [DecidableEq m] [DecidableEq n] [DecidableEq o] in
/-- The rank of a block diagonal matrix. -/
theorem rank_fromBlocks_zero (A : Matrix l m K) (D : Matrix o n K) :
    (fromBlocks A 0 0 D).rank = A.rank + D.rank := by
  have h : (fromBlocks A 0 0 D).mulVecLin =
      (LinearEquiv.sumArrowLequivProdArrow l o K K).symm.toLinearMap ∘ₗ
        (A.mulVecLin.prodMap D.mulVecLin) ∘ₗ
          (LinearEquiv.sumArrowLequivProdArrow m n K K).toLinearMap := by
    refine LinearMap.ext fun x => funext fun i => ?_
    rcases i with i | i <;> simp [fromBlocks_mulVec] <;> rfl
  rw [rank, h, LinearMap.range_comp, LinearMap.range_comp, LinearEquiv.range, Submodule.map_top,
    LinearMap.range_prodMap, LinearEquiv.finrank_map_eq, (Submodule.prodEquiv _ _).finrank_eq,
    finrank_prod]
  rfl

/-- The rank adds over a Schur complement. -/
theorem rank_schur {P : Matrix m m K} (Q : Matrix m n K) (R : Matrix l m K) (S : Matrix l n K)
    (hP : IsUnit P.det) : (fromBlocks P Q R S).rank = P.rank + (S - R * P⁻¹ * Q).rank := by
  let := invertibleOfIsUnitDet P hP
  rw [fromBlocks_eq_of_invertible₁₁, invOf_eq_nonsing_inv,
    rank_mul_eq_left_of_isUnit_det _ _ (by simp),
    rank_mul_eq_right_of_isUnit_det _ _ (by simp),
    rank_fromBlocks_zero]

omit [Fintype l] [DecidableEq l] in
/-- A matrix of rank zero is zero. -/
theorem eq_zero_of_rank_eq_zero {A : Matrix l n K} (h : A.rank = 0) : A = 0 := by
  rw [rank, Submodule.finrank_eq_zero, LinearMap.range_eq_bot] at h
  ext i j
  simpa using congrFun (LinearMap.congr_fun h (Pi.single j 1)) i

/-- If the rank does not grow past an invertible block, the Schur complement vanishes. -/
theorem schur_zero {P : Matrix m m K} {Q : Matrix m n K} {R : Matrix l m K} {S : Matrix l n K}
    (hP : IsUnit P.det) (h : (fromBlocks P Q R S).rank = P.rank) : S - R * P⁻¹ * Q = 0 := by
  rw [rank_schur Q R S hP] at h
  exact eq_zero_of_rank_eq_zero (by omega)

omit [Fintype l] [DecidableEq l] [Fintype n] [DecidableEq n] in
/-- Rows in the span of the rows `f k` factor through those rows. -/
theorem exists_eq_mul_of_row_mem_span {κ : Type*} [Fintype κ] {N : Matrix l n K} {f : κ → l}
    (h : ∀ i, N.row i ∈ Submodule.span K (Set.range fun k => N.row (f k))) :
    ∃ C : Matrix l κ K, N = C * N.submatrix f id := by
  choose c hc using fun i => (Submodule.mem_span_range_iff_exists_fun K).mp (h i)
  refine ⟨Matrix.of c, ?_⟩
  ext i j
  have h₁ := congrFun (hc i) j
  simpa [mul_apply, Finset.sum_apply, Matrix.row] using h₁.symm

omit [Fintype n] [DecidableEq n] in
/-- Skew and symmetric matrices satisfy `M i j = ε * M j i` for a constant `ε`. -/
theorem exists_scale_of_transpose {M : Matrix n n K} (hM : Mᵀ = -M ∨ Mᵀ = M) :
    ∃ ε : K, ∀ i j, M i j = ε * M j i := by
  rcases hM with h | h
  · exact ⟨-1, fun i j => by simpa using congrFun (congrFun h j) i⟩
  · exact ⟨1, fun i j => by simpa using congrFun (congrFun h j) i⟩

omit [DecidableEq n] in
/-- If the rows `f k` span the row space of a skew or symmetric matrix, the rank sits on `f`. -/
theorem rank_eq_rank_submatrix {κ : Type*} [Fintype κ] {M : Matrix n n K} (hM : Mᵀ = -M ∨ Mᵀ = M)
    {f : κ → n} (h : ∀ i, M.row i ∈ Submodule.span K (Set.range fun k => M.row (f k))) :
    M.rank = (M.submatrix f f).rank := by
  obtain ⟨ε, hε⟩ := exists_scale_of_transpose hM
  obtain ⟨C, hC⟩ := exists_eq_mul_of_row_mem_span h
  refine le_antisymm ?_ (rank_submatrix_le _ _ _)
  have h₂ : M.submatrix f id = ((ε • C) * M.submatrix f f)ᵀ := by
    ext k j
    have h₃ := congrFun (congrFun hC j) (f k)
    simp only [mul_apply, submatrix_apply, id] at h₃
    simp only [transpose_apply, mul_apply, Matrix.smul_apply, submatrix_apply, smul_eq_mul, id]
    rw [hε (f k) j, h₃, Finset.mul_sum]
    exact Finset.sum_congr rfl fun u _ => by ring
  calc M.rank = (C * M.submatrix f id).rank := congrArg rank hC
    _ ≤ (M.submatrix f id).rank := rank_mul_le_right _ _
    _ = ((ε • C) * M.submatrix f f)ᵀ.rank := by rw [← h₂]
    _ = ((ε • C) * M.submatrix f f).rank := rank_transpose _
    _ ≤ (M.submatrix f f).rank := rank_mul_le_right _ _

/-- A row basis of a skew or symmetric matrix carries a nonsingular principal submatrix. -/
theorem principal_of_row_basis {M : Matrix n n K} (hM : Mᵀ = -M ∨ Mᵀ = M) {W : Finset n}
    (hli : LinearIndependent K fun w : W => M.row w)
    (hsp : ∀ i, M.row i ∈ Submodule.span K (Set.range fun w : W => M.row w)) :
    (principal M W).det ≠ 0 := by
  have h₁ : (M.submatrix ((↑) : W → n) id).rank = Fintype.card W :=
    LinearIndependent.rank_matrix hli
  have h₂ : M.rank = (principal M W).rank := rank_eq_rank_submatrix hM hsp
  have h₃ : (M.submatrix ((↑) : W → n) id).rank ≤ M.rank := rank_submatrix_le _ _ _
  have h₄ : (principal M W).rank = Fintype.card W :=
    le_antisymm (rank_le_card_width _) (by omega)
  exact (isUnit_iff_isUnit_det _ |>.mp
    (mulVec_surjective_iff_isUnit.mp (mulVec_surjective_iff_rank_eq_card.mpr h₄))).ne_zero

omit [DecidableEq n] in
/-- Lemma 1, last step: dropping rows in the span of the kept rows keeps the rank. -/
theorem rank_drop {M : Matrix n n K} (hM : Mᵀ = -M ∨ Mᵀ = M) (keep : Finset n)
    (h : ∀ d, d ∉ keep → M.row d ∈ Submodule.span K (Set.range fun k : keep => M.row k)) :
    M.rank = (principal M keep).rank := by
  refine rank_eq_rank_submatrix hM fun i => ?_
  by_cases hi : i ∈ keep
  · exact Submodule.subset_span ⟨⟨i, hi⟩, rfl⟩
  · exact h i hi

omit [DecidableEq n] in
/-- Lemma 1: independent rows on `∂` number at most `|∂|`. -/
theorem retained_bound {I : Type*} {N : Matrix I n K} {J : Finset I}
    (h : LinearIndependent K fun i : J => N.row i) : J.card ≤ Fintype.card n := by
  simpa using h.fintype_card_le_finrank

/-- The Schur complement of the block on `a` in `M`, on the indices `b`. -/
noncomputable def schurOn {α β γ : Type*} [Fintype β] [DecidableEq β] (M : Matrix α α K)
    (a : β → α) (b : γ → α) : Matrix γ γ K :=
  M.submatrix b b - M.submatrix b a * (M.submatrix a a)⁻¹ * M.submatrix a b

/-- Schur complements of alternating matrices are alternating. -/
theorem IsAlternating.schurOn {α β γ : Type*} [Fintype β] [DecidableEq β] [Fintype α]
    {M : Matrix α α K} (hM : IsAlternating M) (a : β → α) (b : γ → α)
    (hP : IsUnit (M.submatrix a a).det) :
    IsAlternating (schurOn M a b) := by
  have h₁ : M.submatrix a b = -(M.submatrix b a)ᵀ := by
    ext i j
    simpa using hM.apply (b j) (a i)
  have h₂ : M.submatrix b a * (M.submatrix a a)⁻¹ * M.submatrix a b =
      -(M.submatrix b a * (M.submatrix a a)⁻¹ * (M.submatrix b a)ᵀ) := by
    rw [h₁, Matrix.mul_neg]
  rw [PlanarMatching.schurOn, h₂]
  exact (hM.submatrix b).sub (((hM.submatrix a).inv hP).conj _).neg

/-- The rank adds over the Schur complement of the block on one part of a splitting. -/
theorem rank_schurOn {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ] [DecidableEq β]
    [DecidableEq γ] (M : Matrix α α K) (e : β ⊕ γ ≃ α)
    (hP : IsUnit (M.submatrix (e ∘ Sum.inl) (e ∘ Sum.inl)).det) :
    M.rank = Fintype.card β + (schurOn M (e ∘ Sum.inl) (e ∘ Sum.inr)).rank := by
  rw [← rank_submatrix M e e, submatrix_sum_eq_fromBlocks, rank_schur _ _ _ hP, rank_of_isUnit _
    ((isUnit_iff_isUnit_det _).mpr hP)]
  rfl

section OneStep

variable {I D : Type*} [Fintype I] [Fintype D] [DecidableEq I] [DecidableEq D]

/-- The splitting of `I ⊕ ∂` into `P` and `(I ∖ P) ⊕ ∂`. -/
def pivotSplit (P : Finset I) : P ⊕ (↥Pᶜ ⊕ D) ≃ I ⊕ D :=
  (Equiv.sumAssoc P ↥Pᶜ D).symm.trans (Equiv.sumCongr (splitEquiv P) (Equiv.refl D))

/-- `M′`: the Schur complement of `M_{P,P}` on `(I ∖ P) ∪ ∂`. -/
noncomputable abbrev schur (M : Matrix (I ⊕ D) (I ⊕ D) K) (P : Finset I) :
    Matrix (↥Pᶜ ⊕ D) (↥Pᶜ ⊕ D) K :=
  schurOn M (fun x : P => Sum.inl x) (Sum.map (↑) id)

/-- `M′_{I∖P,∂}`. -/
noncomputable abbrev schurBlock (M : Matrix (I ⊕ D) (I ⊕ D) K) (P : Finset I) : Matrix ↥Pᶜ D K :=
  (schur M P).submatrix Sum.inl Sum.inr

/-- `M″`: the restriction of `M′` to `I″ ∪ ∂`. -/
noncomputable abbrev retained (M : Matrix (I ⊕ D) (I ⊕ D) K) (P : Finset I) (J : Finset ↥Pᶜ) :
    Matrix (J ⊕ D) (J ⊕ D) K :=
  (schur M P).submatrix (Sum.map (↑) id) (Sum.map (↑) id)

/-- Lemma 1 in full. Here `J` is `I″`. -/
theorem one_step {M : Matrix (I ⊕ D) (I ⊕ D) K} (hM : IsAlternating M) {P : Finset I}
    (hP : IsUnit (principal (M.submatrix Sum.inl Sum.inl) P).det)
    (hr : P.card = (M.submatrix Sum.inl Sum.inl : Matrix I I K).rank)
    {J : Finset ↥Pᶜ}
    (hli : LinearIndependent K fun i : J => (schurBlock M P).row i)
    (hsp : ∀ i, (schurBlock M P).row i ∈
      Submodule.span K (Set.range fun i : J => (schurBlock M P).row i)) :
    (schur M P).submatrix Sum.inl Sum.inl = 0 ∧ J.card ≤ Fintype.card D ∧
      M.rank = P.card + (retained M P J).rank := by
  have hA : IsAlternating (schur M P) := hM.schurOn _ _ hP
  -- the rank adds inside the block on `I`, so the Schur complement vanishes there
  have hz : (schur M P).submatrix Sum.inl Sum.inl = 0 := by
    have h₁ := rank_schurOn (M.submatrix Sum.inl Sum.inl : Matrix I I K) (splitEquiv P) hP
    have h₂ : (schur M P).submatrix Sum.inl Sum.inl =
        schurOn (M.submatrix Sum.inl Sum.inl : Matrix I I K) (splitEquiv P ∘ Sum.inl)
          (splitEquiv P ∘ Sum.inr) := rfl
    rw [Fintype.card_coe, ← hr] at h₁
    rw [h₂]
    exact eq_zero_of_rank_eq_zero (by omega)
  -- the rank adds over the pivots
  have h₃ : M.rank = P.card + (schur M P).rank := by
    have h₁ := rank_schurOn M (pivotSplit (D := D) P) hP
    have he : (pivotSplit (D := D) P) ∘ Sum.inr = Sum.map (↑) id := by
      funext x
      rcases x with x | d <;> rfl
    rw [he, Fintype.card_coe] at h₁
    exact h₁
  -- dropping the rows outside `J` keeps the rank of `M′`
  have h₄ : (schur M P).rank = (retained M P J).rank := by
    refine rank_eq_rank_submatrix (Or.inl hA.skew) fun i => ?_
    rcases i with i | d
    · obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp (hsp i)
      have : (schur M P).row (Sum.inl i) =
          ∑ u : J, c u • (schur M P).row (Sum.inl (u : ↥Pᶜ)) := by
        ext (j | j)
        · have h₅ : ∀ a, schur M P (Sum.inl a) (Sum.inl j) = 0 :=
            fun a => congrFun (congrFun hz a) j
          simp [Finset.sum_apply, Matrix.row, h₅]
        · simpa [Finset.sum_apply, Matrix.row] using (congrFun hc j).symm
      rw [this]
      exact Submodule.sum_mem _ fun u _ => Submodule.smul_mem _ _
        (Submodule.subset_span ⟨Sum.inl u, rfl⟩)
    · exact Submodule.subset_span ⟨Sum.inr d, rfl⟩
  exact ⟨hz, retained_bound hli, by omega⟩

end OneStep

section TutteBerge

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

/-- An odd component of `G - S` has a vertex that `M` leaves free or matches into `S`. -/
theorem odd_component_escapes [Finite V] {M : G.Subgraph} (hM : M.IsMatching) {S : Set V}
    (c : ((⊤ : G.Subgraph).deleteVerts S).coe.oddComponents) :
    ∃ v : ((⊤ : G.Subgraph).deleteVerts S).verts, v ∈ c.val.supp ∧
      ((v : V) ∉ M.verts ∨ ∃ w ∈ S, M.Adj v w) := by
  by_contra! h
  have hMmatch : (M.induce (Subtype.val '' c.val.supp)).IsMatching := by
    intro v hv
    obtain ⟨⟨v', hv'⟩, ⟨hv, rfl⟩⟩ := hv
    obtain ⟨hcov, hout⟩ := h ⟨v', hv'⟩ hv
    obtain ⟨w, hw⟩ := hM hcov
    use w
    have hwnu : w ∉ S := fun hw' => hout w hw' hw.1
    refine ⟨⟨⟨⟨v', hv'⟩, hv, rfl⟩, ?_, hw.1⟩, fun _ hy => hw.2 _ hy.2.2⟩
    apply ConnectedComponent.mem_coe_supp_of_adj ⟨⟨v', hv'⟩, ⟨hv, rfl⟩⟩ ⟨by trivial, hwnu⟩
    simp only [Subgraph.induce_verts, Subgraph.verts_top, Set.mem_sdiff, Set.mem_univ, true_and,
      Subgraph.induce_adj, hwnu, not_false_eq_true, and_self, Subgraph.top_adj, M.adj_sub hw.1,
      and_true] at hv' ⊢
    trivial
  apply Nat.not_even_iff_odd.2 c.prop
  have : Fintype ↑(Subgraph.induce M (Subtype.val '' ConnectedComponent.supp c.val)).verts :=
    Fintype.ofFinite _
  classical
  have := Fintype.ofFinite c.val.supp
  simpa [Finset.card_image_of_injective] using hMmatch.even_card

/-- A matching covers two vertices per edge. -/
theorem ncard_verts_of_isMatching [Finite V] {M : G.Subgraph} (hM : M.IsMatching) :
    M.verts.ncard = 2 * M.edgeSet.ncard := by
  classical
  have := Fintype.ofFinite M.verts
  have := Fintype.ofFinite V
  have h₁ : M.coe.edgeSet.ncard = M.edgeSet.ncard := by
    rw [← Subgraph.image_coe_edgeSet_coe,
      Set.ncard_image_of_injective _ (Sym2.map.injective Subtype.val_injective)]
  have h₃ : M.verts.ncard = 2 * M.coe.edgeFinset.card := by
    rw [← M.coe.sum_degrees_eq_twice_card_edges, ← Nat.card_coe_set_eq, Nat.card_eq_fintype_card,
      ← Finset.card_univ, Finset.card_eq_sum_ones]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Subgraph.coe_degree]
    exact (Subgraph.degree_eq_one_iff_existsUnique_adj.mpr (hM x.2)).symm
  rw [h₃, ← h₁, Set.ncard_eq_toFinset_card']
  rfl

/-- Tutte-Berge weak duality: `n - 2|M| ≥ odd(G - S) - |S|`, without subtraction. -/
theorem tutte_berge_weak [Fintype V] {M : G.Subgraph} (hM : M.IsMatching) (S : Set V) :
    ((⊤ : G.Subgraph).deleteVerts S).coe.oddComponents.ncard + 2 * M.edgeSet.ncard ≤
      Fintype.card V + S.ncard := by
  classical
  have hc := Set.ncard_add_ncard_compl M.verts
  rw [Nat.card_eq_fintype_card, ncard_verts_of_isMatching hM] at hc
  have key : ((⊤ : G.Subgraph).deleteVerts S).coe.oddComponents.ncard ≤
      M.vertsᶜ.ncard + S.ncard := by
    have hx : ∀ c : ((⊤ : G.Subgraph).deleteVerts S).coe.oddComponents,
        ∃ v : ((⊤ : G.Subgraph).deleteVerts S).verts, v ∈ c.val.supp ∧
          ∃ t : ↥(M.vertsᶜ) ⊕ ↥S,
            Sum.elim (fun u : ↥(M.vertsᶜ) => (u : V) = v) (fun w : ↥S => M.Adj v w) t := by
      intro c
      obtain ⟨v, hv, hc⟩ := odd_component_escapes hM c
      refine ⟨v, hv, ?_⟩
      rcases hc with hc | ⟨w, hw, hc⟩
      · exact ⟨Sum.inl ⟨v, hc⟩, rfl⟩
      · exact ⟨Sum.inr ⟨w, hw⟩, hc⟩
    choose v hv t ht using hx
    have hinj : Function.Injective t := by
      intro c d hcd
      have hvv : v c = v d := by
        have h₁ := ht c
        have h₂ := ht d
        rw [← hcd] at h₂
        rcases hx' : t c with u | w
        · simp only [hx', Sum.elim_inl] at h₁ h₂
          exact Subtype.val_injective (h₁.symm.trans h₂)
        · simp only [hx', Sum.elim_inr] at h₁ h₂
          exact Subtype.val_injective (hM.eq_of_adj_right h₁ h₂)
      exact Subtype.val_injective
        (ConnectedComponent.eq_of_common_vertex (hv c) (hvv ▸ hv d))
    have := Nat.card_le_card_of_injective t hinj
    rw [Nat.card_sum, Nat.card_coe_set_eq, Nat.card_coe_set_eq, Nat.card_coe_set_eq] at this
    exact this
  omega

end TutteBerge

end PlanarMatching
