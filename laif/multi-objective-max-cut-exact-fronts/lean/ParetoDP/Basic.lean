import Mathlib

/-!
# Correctness of Pareto-pruned dynamic programming

Values live in a partially ordered additive monoid `V` (for example `Fin m → ℝ` with the
pointwise order, maximization in every coordinate). The non-dominated part of a finite set
`A` is the set of its maximal elements. A dynamic program keeps, for every state, a finite set
of values. A step takes the union, over the incoming transitions, of the source set shifted by
the transition value. The pruned program applies `nondom` after every step.

Main result: `pruned_eq_nondom_exact`. The pruned sets equal the non-dominated parts of the
exact sets at every step.
-/

namespace ParetoDP

open Finset

variable {V : Type*} [AddCommMonoid V] [PartialOrder V] [IsOrderedAddMonoid V] [DecidableEq V]

/-- The non-dominated (maximal) elements of a finite set. -/
noncomputable def nondom (A : Finset V) : Finset V := by
  classical exact A.filter (fun x => ∀ y ∈ A, x ≤ y → y = x)

lemma mem_nondom {A : Finset V} {x : V} :
    x ∈ nondom A ↔ x ∈ A ∧ ∀ y ∈ A, x ≤ y → y = x := by
  classical simp [nondom]

lemma nondom_subset (A : Finset V) : nondom A ⊆ A := fun _ h => (mem_nondom.1 h).1

/-- Every element of a finite set lies below a non-dominated element. -/
lemma exists_nondom_ge {A : Finset V} {a : V} (ha : a ∈ A) : ∃ x ∈ nondom A, a ≤ x := by
  classical
  obtain ⟨x, hax, hx⟩ := A.exists_le_maximal ha
  exact ⟨x, mem_nondom.2 ⟨hx.prop, fun y hy hxy => (hx.eq_of_le hy hxy).symm⟩, hax⟩

/-- If `X ⊆ Y` and every element of `Y` lies below an element of `X`, then both sets have the
same non-dominated part. -/
lemma nondom_eq_of_cover {X Y : Finset V} (hXY : X ⊆ Y)
    (hcov : ∀ y ∈ Y, ∃ x ∈ X, y ≤ x) : nondom X = nondom Y := by
  ext z
  constructor
  · intro hz
    obtain ⟨hzX, hmax⟩ := mem_nondom.1 hz
    refine mem_nondom.2 ⟨hXY hzX, fun y hy hzy => ?_⟩
    obtain ⟨x, hx, hyx⟩ := hcov y hy
    have hxz : x = z := hmax x hx (hzy.trans hyx)
    subst hxz
    exact le_antisymm hyx hzy
  · intro hz
    obtain ⟨hzY, hmax⟩ := mem_nondom.1 hz
    obtain ⟨x, hx, hzx⟩ := hcov z hzY
    have hxz : x = z := hmax x (hXY hx) hzx
    subst hxz
    exact mem_nondom.2 ⟨hx, fun y hy hzy => hmax y (hXY hy) hzy⟩

/-- One step of the program: union over transitions `(source state, shift)`. -/
def step {S : Type*} (E : S → Finset V) (T : Finset (S × V)) : Finset V :=
  T.biUnion (fun p => (E p.1).image (· + p.2))

/-- Pruning the sources before a step does not change the non-dominated part of the result. -/
lemma nondom_step_nondom {S : Type*} (E : S → Finset V) (T : Finset (S × V)) :
    nondom (step (fun s => nondom (E s)) T) = nondom (step E T) := by
  apply nondom_eq_of_cover
  · intro v hv
    simp only [step, mem_biUnion, mem_image] at hv ⊢
    obtain ⟨p, hp, x, hx, rfl⟩ := hv
    exact ⟨p, hp, x, nondom_subset _ hx, rfl⟩
  · intro v hv
    simp only [step, mem_biUnion, mem_image] at hv
    obtain ⟨p, hp, a, ha, rfl⟩ := hv
    obtain ⟨x, hx, hax⟩ := exists_nondom_ge ha
    refine ⟨x + p.2, ?_, add_le_add hax le_rfl⟩
    simp only [step, mem_biUnion, mem_image]
    exact ⟨p, hp, x, hx, rfl⟩

/-- The exact program: all reachable values. -/
def exact {S : Type*} (init : S → Finset V) (T : ℕ → S → Finset (S × V)) : ℕ → S → Finset V
  | 0 => init
  | i + 1 => fun s => step (exact init T i) (T i s)

/-- The pruned program: `nondom` after every step. -/
noncomputable def pruned {S : Type*} (init : S → Finset V) (T : ℕ → S → Finset (S × V)) :
    ℕ → S → Finset V
  | 0 => fun s => nondom (init s)
  | i + 1 => fun s => nondom (step (pruned init T i) (T i s))

/-- **Correctness.** At every step and state, the pruned program holds exactly the
non-dominated values of the exact program. -/
theorem pruned_eq_nondom_exact {S : Type*} (init : S → Finset V)
    (T : ℕ → S → Finset (S × V)) (i : ℕ) (s : S) :
    pruned init T i s = nondom (exact init T i s) := by
  induction i generalizing s with
  | zero => rfl
  | succ i ih =>
    have h : pruned init T i = fun s => nondom (exact init T i s) := funext ih
    simp only [pruned, exact, h]
    exact nondom_step_nondom _ _

/-- The final answer: the union over end states, pruned once more, is the non-dominated part
of all values reachable in `n` steps. -/
theorem final_eq {S : Type*} (init : S → Finset V) (T : ℕ → S → Finset (S × V)) (n : ℕ)
    (F : Finset S) :
    nondom (F.biUnion (pruned init T n)) = nondom (F.biUnion (exact init T n)) := by
  apply nondom_eq_of_cover
  · intro v hv
    simp only [mem_biUnion, pruned_eq_nondom_exact] at hv ⊢
    obtain ⟨s, hs, hv⟩ := hv
    exact ⟨s, hs, nondom_subset _ hv⟩
  · intro v hv
    simp only [mem_biUnion] at hv
    obtain ⟨s, hs, hv⟩ := hv
    obtain ⟨x, hx, hvx⟩ := exists_nondom_ge hv
    exact ⟨x, mem_biUnion.2 ⟨s, hs, by rw [pruned_eq_nondom_exact]; exact hx⟩, hvx⟩

end ParetoDP
