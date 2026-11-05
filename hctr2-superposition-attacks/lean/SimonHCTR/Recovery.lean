import SimonHCTR.Shift

/-!
# Key recovery from an element of the hidden subgroup

Over a field `K` of characteristic two, the additive part of the POLYVAL hash of
`l` blocks with key `w` is `lamPoly w N = Σ_i N i * w^(l - i)` (indices from `0`,
so the last block gets `w^1`).

* One block: from `(a, δ)` with `a = δ * w` and `δ ≠ 0` the key is `w = a / δ`.
* Two blocks and two keys `w1 ≠ w2` (CHCTR): `lamPoly w1 δ = lamPoly w2 δ` iff
  `δ 1 = δ 0 * (w1 + w2)`, and then `lamPoly w1 δ = δ 0 * w1 * w2`. From an element
  `(a, d1, d2)` with `d1 ≠ 0` one reads off `s = w1 + w2 = d2 / d1` and
  `p = w1 * w2 = a / d1`, and `{w1, w2}` is the root set of `X^2 + s X + p`.
* The quotient map `(M, N) ↦ (M + lam1 N, lam1 N + lam2 N)` has kernel the subgroup
  of Lemma 2, and for two blocks with `w1 ≠ w2` it is onto `K × K`.
-/

namespace SimonHCTR

variable {K : Type*} [Field K]

/-- The additive part of the polynomial hash with key `w` on `l` blocks:
`N ↦ Σ_i N i * w^(l - i)`. -/
def lamPoly (l : ℕ) (w : K) : (Fin l → K) →+ K where
  toFun N := ∑ i : Fin l, N i * w ^ (l - (i : ℕ))
  map_zero' := by simp
  map_add' N N' := by simp [add_mul, Finset.sum_add_distrib]

theorem lamPoly_apply (l : ℕ) (w : K) (N : Fin l → K) :
    lamPoly l w N = ∑ i : Fin l, N i * w ^ (l - (i : ℕ)) := rfl

theorem lamPoly_one (w : K) (δ : Fin 1 → K) : lamPoly 1 w δ = δ 0 * w := by
  simp [lamPoly_apply]

theorem lamPoly_two (w : K) (δ : Fin 2 → K) :
    lamPoly 2 w δ = δ 0 * w ^ 2 + δ 1 * w := by
  simp [lamPoly_apply, Fin.sum_univ_two]

/-- One block (HCTR2): from `(a, δ)` in the hidden subgroup, `a = lam δ`, with `δ ≠ 0`
the hash key is `w = a / δ`. -/
theorem recover_one {w a : K} {δ : Fin 1 → K} (ha : a = lamPoly 1 w δ) (hδ : δ 0 ≠ 0) :
    w = a / δ 0 := by
  rw [ha, lamPoly_one, mul_div_cancel_left₀ _ hδ]

/-- One block in the form `a = δ * w`. -/
theorem recover_one' {w a δ : K} (ha : a = δ * w) (hδ : δ ≠ 0) : w = a / δ := by
  rw [ha, mul_div_cancel_left₀ _ hδ]

variable [CharP K 2]

theorem add_ne_zero_of_ne {w1 w2 : K} (hw : w1 ≠ w2) : w1 + w2 ≠ 0 := by
  rwa [Ne, CharTwo.add_eq_zero]

/-- In characteristic two, `lamPoly w1 δ + lamPoly w2 δ = (w1 + w2) (δ 0 (w1 + w2) + δ 1)`
for two blocks. -/
theorem lamPoly_two_add (w1 w2 : K) (δ : Fin 2 → K) :
    lamPoly 2 w1 δ + lamPoly 2 w2 δ = (w1 + w2) * (δ 0 * (w1 + w2) + δ 1) := by
  rw [lamPoly_two, lamPoly_two]
  linear_combination (-(δ 0 * w1 * w2)) * (CharTwo.two_eq_zero (R := K))

/-- Two blocks, `w1 ≠ w2`: the CHCTR condition `lam1 δ = lam2 δ` is
`δ 1 = δ 0 * (w1 + w2)`. -/
theorem lamPoly_two_eq_iff {w1 w2 : K} (hw : w1 ≠ w2) (δ : Fin 2 → K) :
    lamPoly 2 w1 δ = lamPoly 2 w2 δ ↔ δ 1 = δ 0 * (w1 + w2) := by
  rw [← CharTwo.add_eq_zero, lamPoly_two_add, mul_eq_zero, or_iff_right
    (add_ne_zero_of_ne hw), CharTwo.add_eq_zero, eq_comm]

/-- Two blocks: if `δ 1 = δ 0 * (w1 + w2)` then `lamPoly w1 δ = δ 0 * w1 * w2`. -/
theorem lamPoly_two_of {w1 w2 : K} (δ : Fin 2 → K) (h : δ 1 = δ 0 * (w1 + w2)) :
    lamPoly 2 w1 δ = δ 0 * w1 * w2 := by
  rw [lamPoly_two, h]
  linear_combination (δ 0 * w1 ^ 2) * (CharTwo.two_eq_zero (R := K))

/-- The roots of `X^2 + (w1 + w2) X + w1 w2` are exactly `w1` and `w2`. -/
theorem quadratic_roots (w1 w2 X : K) :
    X ^ 2 + (w1 + w2) * X + w1 * w2 = 0 ↔ X = w1 ∨ X = w2 := by
  have : X ^ 2 + (w1 + w2) * X + w1 * w2 = (X + w1) * (X + w2) := by ring
  rw [this, mul_eq_zero, CharTwo.add_eq_zero, CharTwo.add_eq_zero]

/-- CHCTR key recovery: for `δ` with `lam1 δ = lam2 δ`, `w1 ≠ w2` and `δ 0 ≠ 0`, the
element `(a, d1, d2) = (lam1 δ, δ 0, δ 1)` of the hidden subgroup gives
`d2 / d1 = w1 + w2` and `a / d1 = w1 * w2`. -/
theorem recover_two {w1 w2 : K} (hw : w1 ≠ w2) (δ : Fin 2 → K)
    (h : lamPoly 2 w1 δ = lamPoly 2 w2 δ) (hd : δ 0 ≠ 0) :
    δ 1 / δ 0 = w1 + w2 ∧ lamPoly 2 w1 δ / δ 0 = w1 * w2 := by
  have h1 := (lamPoly_two_eq_iff hw δ).1 h
  refine ⟨?_, ?_⟩
  · rw [h1, mul_div_cancel_left₀ _ hd]
  · rw [lamPoly_two_of δ h1, mul_assoc, mul_div_cancel_left₀ _ hd]

/-- CHCTR key recovery, combined: with `s = d2 / d1` and `p = a / d1` computed from the
element `(a, d1, d2) = (lam1 δ, δ 0, δ 1)`, the roots of `X^2 + s X + p` are exactly
the two hash keys. -/
theorem recover_two_roots {w1 w2 : K} (hw : w1 ≠ w2) (δ : Fin 2 → K)
    (h : lamPoly 2 w1 δ = lamPoly 2 w2 δ) (hd : δ 0 ≠ 0) (X : K) :
    X ^ 2 + (δ 1 / δ 0) * X + lamPoly 2 w1 δ / δ 0 = 0 ↔ X = w1 ∨ X = w2 := by
  obtain ⟨hs, hp⟩ := recover_two hw δ h hd
  rw [hs, hp, quadratic_roots]

/-! ## The quotient map -/

/-- The quotient map `(M, N) ↦ (M + lam1 N, lam1 N + lam2 N)`. -/
def quotMap {R : Type*} [CommRing R] {l : ℕ} (lam1 lam2 : (Fin l → R) →+ R) :
    R × (Fin l → R) →+ R × R where
  toFun x := (x.1 + lam1 x.2, lam1 x.2 + lam2 x.2)
  map_zero' := by simp
  map_add' x y := by
    simp only [Prod.fst_add, Prod.snd_add, map_add, Prod.mk_add_mk, Prod.mk.injEq]
    constructor <;> abel

/-- The kernel of the quotient map is the CHCTR subgroup
`{(lam1 δ, δ) : lam1 δ = lam2 δ}`. -/
theorem quotMap_eq_zero_iff {R : Type*} [CommRing R] [CharP R 2] {l : ℕ}
    (lam1 lam2 : (Fin l → R) →+ R) (x : R × (Fin l → R)) :
    quotMap lam1 lam2 x = 0 ↔ ∃ δ, lam1 δ = lam2 δ ∧ x = (lam1 δ, δ) := by
  constructor
  · intro h
    simp only [quotMap, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Prod.mk_eq_zero,
      CharTwo.add_eq_zero] at h
    exact ⟨x.2, h.2, Prod.ext h.1 rfl⟩
  · rintro ⟨δ, hδ, rfl⟩
    simp [quotMap, hδ, CharTwo.add_self_eq_zero]

/-- For two blocks and `w1 ≠ w2` the quotient map for the polynomial hashes is onto. -/
theorem quotMap_surjective {w1 w2 : K} (hw : w1 ≠ w2) :
    Function.Surjective (quotMap (lamPoly 2 w1) (lamPoly 2 w2)) := by
  rintro ⟨y, z⟩
  set N : Fin 2 → K := ![0, z / (w1 + w2)]
  have hz : lamPoly 2 w1 N + lamPoly 2 w2 N = z := by
    rw [lamPoly_two_add]
    simp [N, mul_div_cancel₀ _ (add_ne_zero_of_ne hw)]
  refine ⟨(y + lamPoly 2 w1 N, N), ?_⟩
  simp only [quotMap, AddMonoidHom.coe_mk, ZeroHom.coe_mk, hz, add_add_cancel_right]

end SimonHCTR
