import Mathlib

/-!
# Reduction of a quadratic to a hidden shift

For `f(y) = (y + s)² - D` and offsets `a_1, …, a_m`, put `f₀(x)_i = g(f(x + a_i))` and
`f₁(x)_i = g(f(-x - a_i))` for any function `g` (in the application the quadratic character). Then
`f₁(x) = f₀(x - 2s)`: the reflection symmetry `y ↦ -2s - y` of `f` becomes a hidden shift by `2s`, and
`f₁` is computable from the same oracle as `f₀`.

If the vectors `f₀(x)` are pairwise distinct, `f₀` is injective. A union bound over pairs then shows that
`m` random offsets give an injective `f₀` unless a set of offset tuples of size at most `q² c^m` is hit,
where `c` bounds the number of offsets `a` with `g(f(x + a)) = g(f(y + a))` for `x ≠ y`. For the quadratic
character, `q = p` prime and `D ≠ 0`, the Weil bound gives `c ≤ p/2 + 3√p/2 + 1`; it enters here as a hypothesis.
-/

open Finset

namespace LegendreRecon

/-- The quadratic with hidden centre `-s` and discriminant parameter `D`. -/
def quad {R : Type*} [CommRing R] (s D y : R) : R := (y + s) ^ 2 - D

/-- The reflection symmetry of the quadratic. -/
theorem quad_reflect {R : Type*} [CommRing R] (s D y : R) : quad s D (-2 * s - y) = quad s D y := by
  unfold quad; ring

/-- The two functions of the hidden shift. -/
def f0 {R β ι : Type*} [CommRing R] (g : R → β) (s D : R) (a : ι → R) (x : R) : ι → β :=
  fun i => g (quad s D (x + a i))

def f1 {R β ι : Type*} [CommRing R] (g : R → β) (s D : R) (a : ι → R) (x : R) : ι → β :=
  fun i => g (quad s D (-x - a i))

/-- `f₁(x) = f₀(x - 2s)`. -/
theorem f1_eq_shift {R β ι : Type*} [CommRing R] (g : R → β) (s D : R) (a : ι → R) (x : R) :
    f1 g s D a x = f0 g s D a (x - 2 * s) := by
  funext i
  unfold f1 f0 quad
  congr 1
  ring

/-- Union bound: the offset tuples `A ∈ F^m` for which `x ↦ (g(x + A_i))_i` is not injective number at
most `q² c^m`, if every pair `x ≠ y` agrees on at most `c` offsets. -/
theorem card_not_injective_le {F β : Type*} [AddCommGroup F] [Fintype F] [DecidableEq F] [DecidableEq β]
    (g : F → β) (m c : ℕ)
    (hc : ∀ x y : F, x ≠ y → (univ.filter fun a => g (x + a) = g (y + a)).card ≤ c) :
    (univ.filter fun A : Fin m → F => ¬ Function.Injective fun x => fun i => g (x + A i)).card ≤
      Fintype.card F ^ 2 * c ^ m := by
  set S : F × F → Finset F := fun xy => univ.filter fun a => g (xy.1 + a) = g (xy.2 + a)
  have hsub : (univ.filter fun A : Fin m → F => ¬ Function.Injective fun x => fun i => g (x + A i)) ⊆
      (univ.offDiag : Finset (F × F)).biUnion fun xy => Fintype.piFinset fun _ : Fin m => S xy := by
    intro A hA
    simp only [mem_filter, mem_univ, true_and, Function.Injective, not_forall] at hA
    obtain ⟨x, y, hxy, hne⟩ := hA
    simp only [mem_biUnion, mem_offDiag, mem_univ, true_and, Fintype.mem_piFinset]
    refine ⟨(x, y), hne, fun i => ?_⟩
    simp only [S, mem_filter, mem_univ, true_and]
    exact congrFun hxy i
  calc _ ≤ _ := card_le_card hsub
    _ ≤ ∑ xy ∈ (univ.offDiag : Finset (F × F)), (Fintype.piFinset fun _ : Fin m => S xy).card :=
        card_biUnion_le
    _ ≤ ∑ _xy ∈ (univ.offDiag : Finset (F × F)), c ^ m := by
        refine sum_le_sum fun xy hxy => ?_
        rw [Fintype.card_piFinset, prod_const, card_univ, Fintype.card_fin]
        exact Nat.pow_le_pow_left (hc xy.1 xy.2 (mem_offDiag.mp hxy).2.2) m
    _ ≤ Fintype.card F ^ 2 * c ^ m := by
        rw [sum_const, smul_eq_mul, offDiag_card, card_univ]
        exact Nat.mul_le_mul_right _ (by rw [sq]; exact Nat.sub_le _ _)

end LegendreRecon
