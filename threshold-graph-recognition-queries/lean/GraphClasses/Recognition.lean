import GraphClasses.Learn

/-!
# Recognition: learn a hypothesis, then check it

`check` is the logic of the Check paragraph. The hypothesis is arbitrary, which is the point: correctness of a "yes"
does not depend on what the learner did.
-/

open Finset

namespace GraphClasses

variable {α : Type*}

/-- **Check.** Reject if the hypothesis `H` is not in the class. Then search `all` for a disagreement with the input,
and accept iff there is none. -/
def check (s : Search α) (Cl : (α → Bool) → Prop) [DecidablePred Cl] (all : Finset α) (H input : α → Bool) : Bool :=
  decide (Cl H) && (s all fun e => H e != input e).isNone

/-- A class that only depends on the entries in `all`. -/
def DependsOn (Cl : (α → Bool) → Prop) (all : Finset α) : Prop :=
  ∀ f g : α → Bool, (∀ e ∈ all, f e = g e) → (Cl f ↔ Cl g)

/-- **Recognition, soundness.** If the hypothesis is in the class and the correct search finds no disagreement, the
input is in the class. Nothing is assumed about the hypothesis. -/
theorem check_sound {s : Search α} (hs : SearchSpec s) {Cl : (α → Bool) → Prop} [DecidablePred Cl] {all : Finset α}
    (hdep : DependsOn Cl all) {H input : α → Bool} (h : check s Cl all H input = true) : Cl input := by
  simp only [check, Bool.and_eq_true, decide_eq_true_eq, Option.isNone_iff_eq_none] at h
  refine (hdep H input fun e he => ?_).1 h.1
  have := (hs all fun e => H e != input e).2 h.2 e he
  simpa using this

/-- **Recognition, completeness.** If the input is in the class and the learner succeeded, the answer is yes. -/
theorem check_complete {s : Search α} (hs : SearchSpec s) {Cl : (α → Bool) → Prop} [DecidablePred Cl]
    {all : Finset α} (hdep : DependsOn Cl all) {H input : α → Bool} (hin : Cl input) (hH : ∀ e ∈ all, H e = input e) :
    check s Cl all H input = true := by
  simp only [check, Bool.and_eq_true, decide_eq_true_eq, Option.isNone_iff_eq_none]
  refine ⟨(hdep H input hH).2 hin, ?_⟩
  cases he : s all (fun e => H e != input e) with
  | none => rfl
  | some a =>
    obtain ⟨h1, h2⟩ := (hs all fun e => H e != input e).1 a he
    simp [hH a h1] at h2

/-! ## Theorem 2, the logic: recognizing nested matrices -/

variable {R C : Type*} [Fintype R] [Fintype C] [DecidableEq R] [DecidableEq C]

/-- The matrix class, on matrices written as functions on pairs. -/
def NestedPairs (f : R × C → Bool) : Prop := Nested fun r c => f (r, c)

instance : DecidablePred (NestedPairs (R := R) (C := C)) := fun f => by
  unfold NestedPairs Nested
  infer_instance

/-- The hypothesis read off a table: an entry is `1` iff the table records it as `1`. -/
def tableFn (T : Table R C) (e : R × C) : Bool := decide ((e.1, e.2, true) ∈ T)

theorem tableFn_graphOn (M : R → C → Bool) {A : Finset R} {B : Finset C} {r : R} {c : C} (hr : r ∈ A) (hc : c ∈ B) :
    tableFn (graphOn M A B) (r, c) = M r c := by
  simp only [tableFn, mem_graphOn, hr, hc, true_and]
  cases M r c <;> simp

/-- The recognizer of nested matrices: Learn the whole matrix, then Check. -/
def recognizeNested (s : Search (R × C)) (t : Search (C × R)) (pick : Finset R → Finset C → Option (R × C))
    (M : R → C → Bool) : Bool :=
  check s NestedPairs univ
    (tableFn (learn s t pick M (Fintype.card R + Fintype.card C) univ univ)) (fun e => M e.1 e.2)

/-- **Theorem 2, the logic.** With correct searches, the recognizer accepts exactly the nested matrices. -/
theorem recognizeNested_iff {s : Search (R × C)} {t : Search (C × R)} (hs : SearchSpec s) (ht : SearchSpec t)
    {pick : Finset R → Finset C → Option (R × C)} (hp : PickSpec pick) (M : R → C → Bool) :
    recognizeNested s t pick M = true ↔ Nested M := by
  have hdep : DependsOn (NestedPairs (R := R) (C := C)) univ := by
    intro f g h
    have : f = g := funext fun e => h e (mem_univ e)
    rw [this]
  constructor
  · intro h
    exact check_sound hs hdep h
  · intro hM
    refine check_complete hs hdep hM fun e _ => ?_
    have hN : NestedOn M univ univ := (nested_iff_nestedOn_univ M).1 hM
    rw [learn_correct hs ht hp M _ univ univ hN (by simp)]
    exact tableFn_graphOn M (mem_univ _) (mem_univ _)

end GraphClasses
