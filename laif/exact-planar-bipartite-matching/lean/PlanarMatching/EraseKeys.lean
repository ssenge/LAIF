import PlanarMatching.PathDecomp
import Mathlib.Data.Nat.Find

/-!
# The erasure from the reports of the separator

`notes/MATCHING.md`, Section 3, "Doing the erasure". Positions in the walk stand for the keys, which follow the walk.
Every member of `H` reports its visits, that is the positions where it occurs (`reports`). From the length of the
walk and these reports alone, `fromRep` computes the positions that the erasure keeps: at a reported position it jumps
to the last report of the same vertex, which is kept, and every other position is kept as it is.

* `fromRep_spec`: reading the walk at these positions gives `eraseAt H`.
* `loopErase_fromRep`: when only members of `H` repeat, it gives the loop erasure.
* `Decomp.pathOf_fromRep`: in a bag with children, the path of a request is read off the walk at the positions
  computed from the reports of the separator.
-/

namespace PlanarMatching

variable {α : Type*} [DecidableEq α]

/-- The jump lands after the last visit. -/
theorem after_eq_drop {x : α} : ∀ {m : List α} {j : ℕ}, m[j]? = some x → (∀ r, j < r → m[r]? ≠ some x) →
    after x m = m.drop (j + 1)
  | [], _, h, _ => by simp at h
  | a :: m, 0, h, hr => by
    have ha : a = x := by simpa using h
    have hx : x ∉ m := fun hm => by
      obtain ⟨r, hr', e⟩ := List.getElem_of_mem hm
      exact hr (r + 1) (by omega) (by rw [List.getElem?_cons_succ, List.getElem?_eq_getElem hr', e])
    simp [after, hx, ha]
  | a :: m, j + 1, h, hr => by
    have h' : m[j]? = some x := by simpa using h
    have hx : x ∈ m := List.mem_of_getElem? h'
    rw [after, ite_eq_left hx, after_eq_drop h' (fun r hjr => by simpa using hr (r + 1) (by omega))]
    simp

theorem after_drop {l : List α} {p q : ℕ} {x : α} (hpq : p ≤ q) (hq : l[q]? = some x)
    (hlast : ∀ r, q < r → l[r]? ≠ some x) : after x (l.drop (p + 1)) = l.drop (q + 1) := by
  rcases Nat.eq_or_lt_of_le hpq with rfl | hlt
  · apply after_of_not_mem
    intro hm
    obtain ⟨j, hj, e⟩ := List.getElem_of_mem hm
    apply hlast (p + 1 + j) (by omega)
    rw [← List.getElem?_drop, List.getElem?_eq_getElem hj, e]
  · rw [after_eq_drop (j := q - p - 1), List.drop_drop]
    · congr 1; omega
    · rw [List.getElem?_drop, show p + 1 + (q - p - 1) = q by omega, hq]
    · intro r hr
      rw [List.getElem?_drop]
      exact hlast _ (by omega)

/-- The reports of the members of `H`: the vertex at each of their visits. -/
def reports (H : Finset α) (l : List α) (p : ℕ) : Option α :=
  match l[p]? with
  | some x => if x ∈ H then some x else none
  | none => none

theorem reports_eq_some {H : Finset α} {l : List α} {p : ℕ} {x : α} :
    reports H l p = some x ↔ l[p]? = some x ∧ x ∈ H := by
  unfold reports
  cases h : l[p]? with
  | none => simp
  | some y =>
    by_cases hy : y ∈ H
    · simp only [hy, ite_true, Option.some.injEq]
      exact ⟨fun e => ⟨e, e ▸ hy⟩, fun e => e.1⟩
    · simp only [hy, ite_false]
      simp
      rintro rfl
      exact hy

/-- The kept positions from `p` on, computed from the length `n` of the walk and the reports `rep` alone. -/
def fromRep (n : ℕ) (rep : ℕ → Option α) (p : ℕ) : List ℕ :=
  if _hp : p < n then
    match rep p with
    | some x => max p (Nat.findGreatest (fun r => rep r = some x) n) ::
        fromRep n rep (max p (Nat.findGreatest (fun r => rep r = some x) n) + 1)
    | none => p :: fromRep n rep (p + 1)
  else []
termination_by n - p
decreasing_by
  all_goals omega

/-- Reading the walk at the computed positions gives the erasure that jumps at members of `H`. -/
theorem fromRep_spec (H : Finset α) (l : List α) (p : ℕ) :
    eraseAt H (l.drop p) = (fromRep l.length (reports H l) p).filterMap (fun q => l[q]?) := by
  rw [fromRep]
  split_ifs with hp
  · rw [List.drop_eq_getElem_cons hp, eraseAt]
    by_cases hx : l[p] ∈ H
    · have hrep : reports H l p = some l[p] := reports_eq_some.mpr ⟨List.getElem?_eq_getElem hp, hx⟩
      simp only [hrep, hx, ite_true]
      obtain ⟨q, hq⟩ : ∃ q, q = max p (Nat.findGreatest (fun r => reports H l r = some l[p]) l.length) := ⟨_, rfl⟩
      rw [← hq]
      have hle := Nat.le_findGreatest (P := fun r => reports H l r = some l[p]) hp.le hrep
      have hq' : q = Nat.findGreatest (fun r => reports H l r = some l[p]) l.length := by
        rw [hq]; exact max_eq_right hle
      have hpq : p ≤ q := hq ▸ le_max_left _ _
      have hPq : reports H l q = some l[p] := by
        rw [hq']; exact Nat.findGreatest_spec (P := fun r => reports H l r = some l[p]) hp.le hrep
      have hlq : l[q]? = some l[p] := (reports_eq_some.mp hPq).1
      have hlast : ∀ r, q < r → l[r]? ≠ some l[p] := fun r hr e => by
        have hrl : r < l.length := by
          by_contra hc
          rw [List.getElem?_eq_none (by omega)] at e
          cases e
        rw [hq'] at hr
        exact Nat.findGreatest_is_greatest hr hrl.le (reports_eq_some.mpr ⟨e, hx⟩)
      rw [List.filterMap_cons, hlq, after_drop hpq hlq hlast, fromRep_spec H l (q + 1)]
    · have hrep : reports H l p = none := by
        unfold reports; rw [List.getElem?_eq_getElem hp]; simp [hx]
      simp only [hrep, hx, ite_false]
      rw [List.filterMap_cons, List.getElem?_eq_getElem hp, fromRep_spec H l (p + 1)]
  · rw [List.drop_eq_nil_of_le (by omega)]
    simp [eraseAt]
termination_by l.length - p
decreasing_by
  all_goals omega

/-- When only members of `H` repeat, the loop erasure is read off the walk at the positions computed from the
reports of `H`. -/
theorem loopErase_fromRep (H : Finset α) (l : List α) (h : ∀ a, 1 < l.count a → a ∈ H) :
    loopErase l = (fromRep l.length (reports H l) 0).filterMap (fun q => l[q]?) := by
  rw [← eraseAt_eq_loopErase H l h, ← fromRep_spec, List.drop_zero]

variable {V B : Type*} [DecidableEq V] (D : Decomp V B) {E : V → V → Prop} {leafPath : B → V → V → List V}

/-- In a bag with children, the path of a request is read off its walk at the positions computed from the length of
the walk and the reports of the separator `H` alone. -/
theorem Decomp.pathOf_fromRep
    (hleaf : ∀ Y u v, (¬ ∃ c, D.child c Y) → D.verts Y u → D.Reach Y u v →
      SPath E (Interval (D.Reach Y) u v) u v (leafPath Y u v))
    {Y : B} {u v : V} (r : D.Reach Y u v) (hint : ∃ c, D.child c Y) {H : Finset V} (hH : ∀ x, D.sep Y x → x ∈ H) :
    D.pathOf leafPath Y u v = (fromRep (D.walkOf leafPath Y u v).length (reports H (D.walkOf leafPath Y u v)) 0).filterMap
      (fun q => (D.walkOf leafPath Y u v)[q]?) := by
  have hl := fun i (hi : i < D.hops Y u v) => D.lbl_spec (D.hops_spec r hint).1 hi
  rw [D.pathOf_eq hint (fun i hi => (hl i hi).1)]
  exact loopErase_fromRep H _ fun a ha => hH a (D.repeat_sep hleaf r hint ha)

end PlanarMatching
