import PlanarMatching.Tutte
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.FieldTheory.Finiteness
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp

/-!
# The kernel from the pivots

`notes/GENERAL.md`, Section 5, Lemma 7, over a field `K` and a finite index type `V`. Let `B` be a set with `A_{B,B}`
nonsingular and `rank A = |B|`, as Lemma 2 gives, and `N = V ∖ B`. For `z` on `N`, let `y_N = z` and
`y_B = -(A_{B,B})⁻¹ A_{B,N} z` (`kerVec`).

* `kerVec_mul`: `A y = 0`.
* `kerVec_unique`: every vector of the kernel of `A` is `y` of its part on `N`. With `kerVec_N`, the map `z ↦ y` is
  a linear bijection onto the kernel.
* `mem_support_iff`: some kernel vector is nonzero at `v` exactly when `z ↦ y_v` is a nonzero linear form.
* `support_iff_rank` (Lemma 8): for a skew matrix, some kernel vector is nonzero at `v` exactly when deleting row and
  column `v` keeps the rank. `lemma8`: under the rank conditions of Fact 2, `D′ = {v : y_v ≠ 0}` is the set of `v`
  with `ν(G - v) = ν(G)` for all `z` outside a fraction `|V| / |K|` of `K^N`.
* `card_zero_mul`: a nonzero linear form on a finite space vanishes on a fraction `1/|K|` of it, so for `z` drawn
  uniformly from `F_p^N`, `y_v = 0` with probability `1/p` for every `v` in the union of the supports of kernel
  vectors.
-/

namespace PlanarMatching

open Matrix Module

set_option linter.unusedSectionVars false

variable {K : Type*} [Field K] {V : Type*} [Fintype V] [DecidableEq V]

/-- `A_{B,N}`. -/
abbrev blockBN (A : Matrix V V K) (B : Finset V) : Matrix B ↥Bᶜ K := A.submatrix (↑) (↑)

/-- The vector `y` of `z`: `y_N = z` and `y_B = -(A_{B,B})⁻¹ A_{B,N} z`. -/
noncomputable def kerVec (A : Matrix V V K) (B : Finset V) (z : ↥Bᶜ → K) : V → K := fun v =>
  if h : v ∈ B then -((principal A B)⁻¹ *ᵥ (blockBN A B *ᵥ z)) ⟨v, h⟩ else z ⟨v, Finset.mem_compl.2 h⟩

/-- `z ↦ y` as a linear map. -/
noncomputable def kerMap (A : Matrix V V K) (B : Finset V) : (↥Bᶜ → K) →ₗ[K] (V → K) where
  toFun := kerVec A B
  map_add' z w := by
    ext v; by_cases hv : v ∈ B <;> simp [kerVec, hv, mulVec_add]; ring
  map_smul' c z := by
    ext v; by_cases hv : v ∈ B <;> simp [kerVec, hv, mulVec_smul]

theorem kerVec_N (A : Matrix V V K) (B : Finset V) (z : ↥Bᶜ → K) (c : ↥Bᶜ) : kerVec A B z c = z c := by
  have : (c : V) ∉ B := Finset.mem_compl.1 c.2
  simp [kerVec, this]

theorem kerVec_B (A : Matrix V V K) (B : Finset V) (z : ↥Bᶜ → K) (b : B) :
    kerVec A B z b = -((principal A B)⁻¹ *ᵥ (blockBN A B *ᵥ z)) b := by
  simp [kerVec, b.2]

/-- The sum over `V` splits into the sums over `B` and over `N`. -/
theorem sum_split (B : Finset V) (f : V → K) : ∑ j, f j = ∑ b : B, f b + ∑ c : ↥Bᶜ, f c := by
  rw [← Fintype.sum_equiv (splitEquiv B) (f ∘ splitEquiv B) f (fun _ => rfl), Fintype.sum_sum_type]
  rfl

variable {A : Matrix V V K} {B : Finset V}

/-- The rows of `B` of `A x`. -/
theorem rows_B (x : V → K) :
    (fun b : B => (A *ᵥ x) b) = principal A B *ᵥ (fun b : B => x b) + blockBN A B *ᵥ (fun c => x c) := by
  funext b
  rw [mulVec, dotProduct, sum_split B]
  rfl

/-- The rows of `N` of `A x`. -/
theorem rows_N (x : V → K) :
    (fun c : ↥Bᶜ => (A *ᵥ x) c) = A.submatrix ((↑) : ↥Bᶜ → V) ((↑) : B → V) *ᵥ (fun b : B => x b) +
      A.submatrix ((↑) : ↥Bᶜ → V) ((↑) : ↥Bᶜ → V) *ᵥ (fun c => x c) := by
  funext c
  rw [mulVec, dotProduct, sum_split B]
  rfl

theorem kerVec_B' (z : ↥Bᶜ → K) :
    (fun b : B => kerVec A B z b) = -((principal A B)⁻¹ *ᵥ (blockBN A B *ᵥ z)) :=
  funext fun b => kerVec_B A B z b

theorem kerVec_N' (z : ↥Bᶜ → K) : (fun c : ↥Bᶜ => kerVec A B z c) = z :=
  funext fun c => kerVec_N A B z c

/-- **Lemma 7, first claim.** `A y = 0`. -/
theorem kerVec_mul (hB : IsUnit (principal A B).det) (hr : A.rank = B.card) (z : ↥Bᶜ → K) :
    A *ᵥ kerVec A B z = 0 := by
  -- the Schur complement on `N` has rank zero
  have hS := rank_schurOn A (splitEquiv B) hB
  rw [Fintype.card_coe, hr] at hS
  have h0 : schurOn A (splitEquiv B ∘ Sum.inl) (splitEquiv B ∘ Sum.inr) = 0 :=
    eq_zero_of_rank_eq_zero (by omega)
  have key : A.submatrix ((↑) : ↥Bᶜ → V) ((↑) : ↥Bᶜ → V) -
      A.submatrix ((↑) : ↥Bᶜ → V) ((↑) : B → V) * (principal A B)⁻¹ * blockBN A B = 0 := h0
  have hBrows := rows_B (A := A) (B := B) (kerVec A B z)
  have hNrows := rows_N (A := A) (B := B) (kerVec A B z)
  rw [kerVec_B', kerVec_N', mulVec_neg, mulVec_mulVec, mul_nonsing_inv _ hB, one_mulVec, neg_add_cancel] at hBrows
  rw [kerVec_B', kerVec_N', mulVec_neg, mulVec_mulVec, mulVec_mulVec, neg_add_eq_sub, ← sub_mulVec, key,
    zero_mulVec] at hNrows
  funext i
  by_cases hi : i ∈ B
  · exact congrFun hBrows ⟨i, hi⟩
  · exact congrFun hNrows ⟨i, Finset.mem_compl.2 hi⟩

/-- **Lemma 7, second claim.** Every vector of the kernel is `y` of its part on `N`. -/
theorem kerVec_unique (hB : IsUnit (principal A B).det) {x : V → K} (hx : A *ᵥ x = 0) :
    x = kerVec A B (fun c => x c) := by
  have hrow := rows_B (A := A) (B := B) x
  rw [hx] at hrow
  have hxB : (fun b : B => x b) = -((principal A B)⁻¹ *ᵥ (blockBN A B *ᵥ fun c => x c)) := by
    have h1 : principal A B *ᵥ (fun b : B => x b) = -(blockBN A B *ᵥ fun c => x c) := by
      rw [eq_neg_iff_add_eq_zero, ← hrow]; rfl
    rw [← mulVec_neg, ← h1, mulVec_mulVec, nonsing_inv_mul _ hB, one_mulVec]
  funext v
  by_cases hv : v ∈ B
  · rw [kerVec_B A B _ ⟨v, hv⟩]; exact congrFun hxB ⟨v, hv⟩
  · rw [kerVec_N A B _ ⟨v, Finset.mem_compl.2 hv⟩]

/-- **Lemma 7, support.** Some kernel vector is nonzero at `v` exactly when `y_v` is not identically zero in `z`. -/
theorem mem_support_iff (hB : IsUnit (principal A B).det) (hr : A.rank = B.card) (v : V) :
    (∃ x, A *ᵥ x = 0 ∧ x v ≠ 0) ↔ ∃ z, kerVec A B z v ≠ 0 := by
  constructor
  · rintro ⟨x, hx, hv⟩
    exact ⟨fun c => x c, by rw [← kerVec_unique hB hx]; exact hv⟩
  · rintro ⟨z, hz⟩
    exact ⟨kerVec A B z, kerVec_mul hB hr z, hz⟩

/-- A nonzero linear form on a finite space vanishes on exactly a fraction `1 / |K|` of it. -/
theorem card_zero_mul [Fintype K] [DecidableEq K] {M : Type*} [AddCommGroup M] [Module K M] [Fintype M]
    (f : M →ₗ[K] K) (hf : f ≠ 0) :
    (Finset.univ.filter fun x => f x = 0).card * Fintype.card K = Fintype.card M := by
  classical
  have hfin : Module.Finite K M := Module.Finite.of_finite
  obtain ⟨x, hx⟩ : ∃ x, f x ≠ 0 := by
    by_contra h; push_neg at h; exact hf (LinearMap.ext h)
  have hr : LinearMap.range f = ⊤ := by
    refine eq_top_iff.2 fun c _ => ⟨(c / f x) • x, ?_⟩
    rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hx]
  have hdim := f.finrank_range_add_finrank_ker
  rw [hr, finrank_top, Module.finrank_self] at hdim
  have hk : (Finset.univ.filter fun x => f x = 0).card = Fintype.card (LinearMap.ker f) := by
    rw [← Fintype.card_subtype]
    exact Fintype.card_congr (Equiv.subtypeEquivRight fun y => (LinearMap.mem_ker).symm)
  rw [hk, Module.card_eq_pow_finrank (K := K) (V := LinearMap.ker f),
    Module.card_eq_pow_finrank (K := K) (V := M), ← hdim, pow_add, pow_one, mul_comm]

/-- **Lemma 7, third claim.** For `v` in the support of a kernel vector and `z` uniform on `K^N`, `y_v = 0` for
exactly a fraction `1 / |K|` of the `z`. -/
theorem card_kerVec_zero [Fintype K] [DecidableEq K] (hB : IsUnit (principal A B).det) (hr : A.rank = B.card)
    {v : V} (hv : ∃ x, A *ᵥ x = 0 ∧ x v ≠ 0) :
    (Finset.univ.filter fun z : ↥Bᶜ → K => kerVec A B z v = 0).card * Fintype.card K =
      Fintype.card (↥Bᶜ → K) := by
  obtain ⟨z, hz⟩ := (mem_support_iff hB hr v).1 hv
  have hf : (LinearMap.proj v).comp (kerMap A B) ≠ 0 := fun h => hz (by
    have := LinearMap.congr_fun h z; simpa [kerMap] using this)
  exact card_zero_mul _ hf

/-- **Lemma 8, the rank step.** For a skew matrix, some kernel vector is nonzero at `v` exactly when deleting row
and column `v` keeps the rank. -/
theorem support_iff_rank {A : Matrix V V K} (hA : Aᵀ = -A) (v : V) :
    (∃ x, A *ᵥ x = 0 ∧ x v ≠ 0) ↔ (principal A ({v}ᶜ : Finset V)).rank = A.rank := by
  have hskew : ∀ i j, A j i = -A i j := fun i j => by
    have := congrFun (congrFun hA i) j; simpa using this
  constructor
  · rintro ⟨x, hx, hxv⟩
    refine (rank_drop (Or.inl hA) ({v}ᶜ : Finset V) fun d hd => ?_).symm
    have hd' : d = v := by simpa using hd
    subst hd'
    -- `xᵀ A = 0`, so row `d` is a combination of the other rows
    have hrow : A.row d = ∑ k : ↥({d}ᶜ : Finset V), (-(x k / x d)) • A.row k := by
      ext j
      have h0 : ∑ i, x i * A i j = 0 := by
        have := congrFun hx j
        simp only [mulVec, dotProduct, Pi.zero_apply] at this
        rw [← neg_eq_zero, ← this, ← Finset.sum_neg_distrib]
        exact Finset.sum_congr rfl fun i _ => by rw [hskew j i]; ring
      rw [sum_split ({d}ᶜ : Finset V)] at h0
      have hs : ∑ b : ↥({d}ᶜ : Finset V), x b * A b j =
          -∑ c : ↥({d}ᶜ : Finset V)ᶜ, x c * A c j := by linear_combination h0
      have h1 : ∑ c : ↥({d}ᶜ : Finset V)ᶜ, x c * A c j = x d * A d j := by
        have : (Finset.univ : Finset ↥({d}ᶜ : Finset V)ᶜ) = {⟨d, by simp⟩} := by
          ext c; simp only [Finset.mem_univ, Finset.mem_singleton, true_iff]
          exact Subtype.ext (by simpa using c.2)
        rw [this, Finset.sum_singleton]
      simp only [row, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      rw [show ∑ k : ↥({d}ᶜ : Finset V), -(x k / x d) * A k j =
          -(∑ k : ↥({d}ᶜ : Finset V), x k * A k j) * (x d)⁻¹ by
        rw [neg_mul, Finset.sum_mul, ← Finset.sum_neg_distrib]
        exact Finset.sum_congr rfl fun k _ => by ring]
      rw [hs, h1]
      field_simp
    rw [hrow]
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  · intro hr
    set S : Finset V := {v}ᶜ
    -- the rows off `v` span the row space
    have hle : Submodule.span K (Set.range fun k : S => A.row k) ≤ Submodule.span K (Set.range A.row) :=
      Submodule.span_mono (Set.range_subset_iff.2 fun k => ⟨k, rfl⟩)
    have hsub : (A.submatrix ((↑) : S → V) id).rank = A.rank := by
      refine le_antisymm (rank_submatrix_le _ _ _) ?_
      rw [← hr]
      exact rank_submatrix_le (A.submatrix ((↑) : S → V) id) id ((↑) : S → V)
    have heq : Submodule.span K (Set.range fun k : S => A.row k) = Submodule.span K (Set.range A.row) := by
      refine Submodule.eq_of_le_of_finrank_eq hle ?_
      rw [← rank_eq_finrank_span_row, ← hsub, rank_eq_finrank_span_row]
      rfl
    have hv : A.row v ∈ Submodule.span K (Set.range fun k : S => A.row k) := by
      rw [heq]; exact Submodule.subset_span ⟨v, rfl⟩
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun K).1 hv
    have hvS : v ∉ S := by simp [S]
    refine ⟨fun i => (if i = v then 1 else 0) - ∑ k : S, c k * (if i = (k : V) then 1 else 0), ?_, ?_⟩
    · funext i
      have hci := congrFun hc i
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, row] at hci
      simp only [mulVec, dotProduct, Pi.zero_apply, mul_sub, Finset.sum_sub_distrib, Finset.mul_sum]
      rw [Finset.sum_comm]
      simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
      rw [hskew v i, ← hci, ← Finset.sum_neg_distrib, ← Finset.sum_sub_distrib]
      exact Finset.sum_eq_zero fun k _ => by rw [hskew (k : V) i]; ring
    · show (if v = v then (1 : K) else 0) - ∑ k : S, c k * (if v = (k : V) then 1 else 0) ≠ 0
      rw [Finset.sum_eq_zero fun (k : S) _ => by
        have hk : v ≠ (k : V) := fun h => hvS (by rw [h]; exact k.2)
        simp [hk]]
      simp

/-- **Lemma 8.** Let `rank A = 2ν` and `rank A_{-v,-v} = 2ν_v` for every `v`, with `ν_v` the maximum matching
number of `G - v`, as Fact 2 gives with high probability. Then `D′ = {v : y_v ≠ 0}` is the set of `v` with
`ν_v = ν` for all `z` outside a set of at most a fraction `|V| / |K|` of `K^N`. -/
theorem lemma8 [Fintype K] [DecidableEq K] (hA : Aᵀ = -A) (hB : IsUnit (principal A B).det) (hr : A.rank = B.card)
    (nu : ℕ) (nuDel : V → ℕ) (h1 : A.rank = 2 * nu)
    (h2 : ∀ v, (principal A ({v}ᶜ : Finset V)).rank = 2 * nuDel v) :
    (Finset.univ.filter fun z : ↥Bᶜ → K =>
        Finset.univ.filter (fun v => kerVec A B z v ≠ 0) ≠ Finset.univ.filter (fun v => nuDel v = nu)).card *
      Fintype.card K ≤ Fintype.card V * Fintype.card (↥Bᶜ → K) := by
  classical
  have hZ : ∀ v, nuDel v = nu ↔ ∃ x, A *ᵥ x = 0 ∧ x v ≠ 0 := by
    intro v; rw [support_iff_rank hA v, h2, h1]; omega
  set Z := Finset.univ.filter (fun v => nuDel v = nu)
  have hsub : (Finset.univ.filter fun z : ↥Bᶜ → K =>
      Finset.univ.filter (fun v => kerVec A B z v ≠ 0) ≠ Z) ⊆
      Z.biUnion (fun v => Finset.univ.filter fun z : ↥Bᶜ → K => kerVec A B z v = 0) := by
    intro z hz
    rw [Finset.mem_filter] at hz
    rw [Finset.mem_biUnion]
    by_contra hne
    push_neg at hne
    apply hz.2
    ext v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Z]
    constructor
    · intro hv; exact (hZ v).2 ⟨kerVec A B z, kerVec_mul hB hr z, hv⟩
    · intro hv
      have := hne v (by simp [Z, hv])
      simpa using this
  calc _ ≤ (Z.biUnion fun v => Finset.univ.filter fun z : ↥Bᶜ → K => kerVec A B z v = 0).card *
          Fintype.card K := Nat.mul_le_mul_right _ (Finset.card_le_card hsub)
    _ ≤ (∑ v ∈ Z, (Finset.univ.filter fun z : ↥Bᶜ → K => kerVec A B z v = 0).card) * Fintype.card K :=
          Nat.mul_le_mul_right _ Finset.card_biUnion_le
    _ = ∑ v ∈ Z, Fintype.card (↥Bᶜ → K) := by
          rw [Finset.sum_mul]
          exact Finset.sum_congr rfl fun v hv =>
            card_kerVec_zero hB hr ((hZ v).1 (by simpa [Z] using hv))
    _ ≤ Fintype.card V * Fintype.card (↥Bᶜ → K) := by
          rw [Finset.sum_const, smul_eq_mul]
          exact Nat.mul_le_mul_right _ (Finset.card_le_univ Z)

end PlanarMatching
