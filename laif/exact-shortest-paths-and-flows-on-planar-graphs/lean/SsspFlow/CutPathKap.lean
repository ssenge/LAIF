import SsspFlow.CutPathAlg

/-!
# The indices of the corners of the cut path from local counts

Every node knows, for each dart at it, whether it is the first dart of the source or of the target, and
after one exchange it knows the count of the dart and of its reverse from the parent chain of the dual
network. With the length `m`, these give the indices of the corners `p_τ^0` and `p_τ^1` of the cut
path at the corners of the dart.

* `encC`, `decC`: counts in `ℕ∞` as natural numbers, for messages.
* `kapOf`: the indices of the corners of a dart from its count, the count of its reverse and the flags.
* `kapOf_spec`: the indices are those of the corners `C.k 0 τ` and `C.k 1 τ` of the cut path.
-/

set_option autoImplicit false

namespace SsspFlow.Congest

/-- A count as a natural number: `0` for `⊤`, `k + 1` for `k`. -/
def encC (c : ℕ∞) : ℕ := if c = ⊤ then 0 else c.toNat + 1

/-- The count of a natural number. -/
def decC (k : ℕ) : ℕ∞ := if k = 0 then ⊤ else ((k - 1 : ℕ) : ℕ∞)

theorem decC_encC (c : ℕ∞) : decC (encC c) = c := by
  unfold encC decC
  by_cases h : c = ⊤
  · simp [h]
  · simp only [h, ite_false, Nat.add_one_ne_zero, Nat.add_sub_cancel]
    exact ENat.coe_toNat h

/-- The indices of the corners `(d, b)` of a dart `d`, from the length `m`, the count `c` of `d`, the
count `cR` of its reverse, and the flags whether `d` is the first dart `cs` of the source, whether it is
the first dart `ct` of the target, and whether its reverse is `cs`. -/
def kapOf (m : ℕ) (c cR : ℕ∞) (fs ft fsR : Bool) (b : Bool) : (ℕ → Bool) × (ℕ → Bool) :=
  (fun τ => if b then decide (m ≤ τ) && ft else decide (τ < m) && decide (c = ((m - 1 - τ : ℕ) : ℕ∞)),
    fun τ => if b then decide (τ = 0) && fs else
      decide (τ ≠ 0) && (if τ - 1 < m then decide (cR = ((m - 1 - (τ - 1) : ℕ) : ℕ∞)) else fsR))

variable {V : Type} [Fintype V] [DecidableEq V] {N : Net V}

/-- **The indices of the corners.** If the count of a dart picks out its index on the cut path and the
darts past the end are `cs`, then `kapOf` gives the indices of the corners `C.k 0 τ` and `C.k 1 τ` at
the corners of each dart. -/
theorem kapOf_spec (C : N.toRot.dual.CutPath) (cnt : N.G.Dart → ℕ∞)
    (hidx : ∀ x τ, τ < C.m → (C.e τ = x ↔ cnt x = ((C.m - 1 - τ : ℕ) : ℕ∞)))
    (hpast : ∀ τ, C.m ≤ τ → C.e τ = C.cs) (d : N.G.Dart) {fs ft fsR : Bool}
    (hfs : fs = true ↔ d = C.cs) (hft : ft = true ↔ d = C.ct) (hfsR : fsR = true ↔ d.symm = C.cs)
    (b : Bool) (τ : ℕ) :
    ((kapOf C.m (cnt d) (cnt d.symm) fs ft fsR b).1 τ = true ↔ (d, b) = C.k 0 τ) ∧
      ((kapOf C.m (cnt d) (cnt d.symm) fs ft fsR b).2 τ = true ↔ (d, b) = C.k 1 τ) := by
  refine ⟨?_, ?_⟩
  · simp only [kapOf, RotSystem.CutPath.k_zero, RotSystem.CutPath.k0]
    cases b
    · by_cases hτ : τ < C.m
      · simp only [hτ, ite_true, Bool.false_eq_true, ite_false, decide_true, Bool.true_and,
          decide_eq_true_eq, Prod.mk.injEq, and_true]
        exact ⟨fun h => ((hidx d τ hτ).2 h).symm, fun h => (hidx d τ hτ).1 h.symm⟩
      · simp [hτ]
    · by_cases hτ : τ < C.m
      · simp [hτ]
      · simp only [hτ, ite_false, ite_true, Bool.and_eq_true, decide_eq_true_eq, Prod.mk.injEq, and_true]
        exact ⟨fun h => hft.1 h.2, fun h => ⟨by omega, hft.2 h⟩⟩
  · simp only [kapOf, RotSystem.CutPath.k_one, RotSystem.CutPath.k1]
    cases b
    · by_cases h0 : τ = 0
      · simp [h0]
      · simp only [h0, ite_false, Bool.false_eq_true, decide_true, ne_eq, not_false_eq_true,
          Bool.true_and, Prod.mk.injEq, and_true]
        have hr : (d = N.toRot.dual.rev (C.e (τ - 1))) ↔ d.symm = C.e (τ - 1) := by
          show d = (C.e (τ - 1)).symm ↔ _
          constructor
          · rintro rfl; exact SimpleGraph.Dart.symm_symm _
          · intro h; rw [← h, SimpleGraph.Dart.symm_symm]
        rw [hr]
        by_cases hl : τ - 1 < C.m
        · simp only [hl, ite_true, decide_eq_true_eq]
          rw [← hidx d.symm (τ - 1) hl, eq_comm]
        · simp only [hl, ite_false]
          rw [hpast _ (by omega), hfsR]
    · by_cases h0 : τ = 0 <;> simp [h0, hfs]

end SsspFlow.Congest
