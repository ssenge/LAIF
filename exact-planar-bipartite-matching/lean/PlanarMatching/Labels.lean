import PlanarMatching.Decomp
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.List.Chain

/-!
# Walks, labels and the hub graph

The walk form of Fact 1 and the Exact Labels Lemma of the notes. A walk in a bag is a list of vertices whose
consecutive pairs are arcs of the bag, `List.IsChain`. `Decomp.walk_stays`: a walk of a bag whose vertices between
the ends are off the separator lies in one child. With arc lengths `ℓ`, `Decomp.exact_labels` says that the distance
in a bag `X` from a hub `a` to a vertex `v` is the least sum of a distance in the hub graph of `X` from `a` to a hub
`b` and a distance from `b` to `v` in a child holding both. `Decomp.distQ_eq`: between hubs, the hub graph has the
distances of `X`.
-/

namespace PlanarMatching

open Relation

variable {V B : Type*} (D : Decomp V B)

/-! ### Fact 1 for walks -/

/-- The vertices of a walk with an arc lie in the bag. -/
theorem Decomp.isChain_verts {c : B} {u x : V} {w : List V} (h : List.IsChain (D.arc c) (u :: x :: w)) :
    ∀ y ∈ u :: x :: w, D.verts c y := by
  induction w generalizing u x with
  | nil =>
    intro y hy
    have a := h.rel
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl
    · exact (D.arc_mem a).1
    · exact (D.arc_mem a).2
  | cons z w ih =>
    intro y hy
    rw [List.isChain_cons_cons] at h
    rcases List.mem_cons.1 hy with rfl | hy
    · exact (D.arc_mem h.1).1
    · exact ih h.2 y hy

/-- Fact 1 for walks: a walk of `b` whose vertices between the ends are off the separator lies in one child of `b`.
The ends may lie on the separator. -/
theorem Decomp.walk_stays {b : B} {w : List V} (hw : List.IsChain (D.arc b) w) (hb : ∃ c, D.child c b)
    (hin : ∀ x ∈ w.tail.dropLast, ¬ D.sep b x) : ∃ c, D.child c b ∧ List.IsChain (D.arc c) w := by
  obtain ⟨c₀, hc₀⟩ := hb
  rcases w with _ | ⟨u, _ | ⟨x, w⟩⟩
  · exact ⟨c₀, hc₀, List.IsChain.nil⟩
  · exact ⟨c₀, hc₀, List.IsChain.singleton u⟩
  · simp only [List.tail_cons] at hin
    induction w generalizing u x with
    | nil =>
      obtain ⟨c, hc, ha⟩ := D.arc_child hw.rel ⟨c₀, hc₀⟩
      exact ⟨c, hc, List.isChain_pair.2 ha⟩
    | cons z w ih =>
      rw [List.isChain_cons_cons] at hw
      rw [List.dropLast_cons_cons] at hin
      have hx : ¬ D.sep b x := hin x (by simp)
      obtain ⟨c, hc, hwc⟩ := ih _ _ hw.2 fun y hy => hin y (List.mem_cons_of_mem _ hy)
      obtain ⟨c', hc', ha⟩ := D.arc_child hw.1 ⟨c₀, hc₀⟩
      have e := D.uniq hc hc' (D.arc_mem hwc.rel).1 (D.arc_mem ha).2 hx
      subst e
      exact ⟨c, hc, List.IsChain.cons_cons ha hwc⟩

/-! ### Lengths of walks -/

/-- The sum of `f` over the consecutive pairs of a list. -/
def pairSum {M : Type*} [AddMonoid M] (f : V → V → M) : List V → M
  | [] => 0
  | [_] => 0
  | u :: v :: w => f u v + pairSum f (v :: w)

@[simp] theorem pairSum_nil {M : Type*} [AddMonoid M] (f : V → V → M) : pairSum f [] = 0 := rfl

@[simp] theorem pairSum_singleton {M : Type*} [AddMonoid M] (f : V → V → M) (u : V) : pairSum f [u] = 0 := rfl

@[simp] theorem pairSum_cons_cons {M : Type*} [AddMonoid M] (f : V → V → M) (u v : V) (w : List V) :
    pairSum f (u :: v :: w) = f u v + pairSum f (v :: w) := rfl

/-- The sum over a concatenation of two lists that share the junction vertex. -/
theorem pairSum_append {M : Type*} [AddMonoid M] (f : V → V → M) :
    ∀ {w₁ w₂ : List V} {u : V}, w₁.getLast? = some u → w₂.head? = some u →
      pairSum f (w₁ ++ w₂.tail) = pairSum f w₁ + pairSum f w₂
  | [], _, _, h₁, _ => by simp at h₁
  | [x], w₂, u, h₁, h₂ => by
    obtain ⟨w₂', rfl⟩ := List.head?_eq_some_iff.1 h₂
    simp only [List.getLast?_singleton, Option.some.injEq] at h₁
    subst h₁
    simp
  | x :: y :: w₁, w₂, u, h₁, h₂ => by
    rw [List.getLast?_cons_cons] at h₁
    have ih := pairSum_append f (w₁ := y :: w₁) h₁ h₂
    show pairSum f (x :: y :: (w₁ ++ w₂.tail)) = pairSum f (x :: y :: w₁) + pairSum f w₂
    rw [pairSum_cons_cons, pairSum_cons_cons, ← List.cons_append, ih, add_assoc]

/-- The sum over a list with one more vertex at the end. -/
theorem pairSum_concat {M : Type*} [AddMonoid M] (f : V → V → M) {w : List V} {u x : V}
    (h : w.getLast? = some u) : pairSum f (w ++ [x]) = pairSum f w + f u x := by
  simpa using pairSum_append f (w₂ := [u, x]) h rfl

/-! ### Distances in a bag -/

/-- `D.IsWalk b u v w`: `w` is a walk in the bag `b` from `u` to `v`. -/
def Decomp.IsWalk (b : B) (u v : V) (w : List V) : Prop :=
  List.IsChain (D.arc b) w ∧ w.head? = some u ∧ w.getLast? = some v

/-- The distance in a bag for the arc lengths `ℓ`: the least length of a walk, `⊤` when there is none. -/
noncomputable def Decomp.dist (ℓ : V → V → ℕ) (b : B) (u v : V) : ℕ∞ :=
  ⨅ (w : List V) (_ : D.IsWalk b u v w), ((pairSum ℓ w : ℕ) : ℕ∞)

theorem Decomp.dist_le {ℓ : V → V → ℕ} {b : B} {u v : V} {w : List V} (h : D.IsWalk b u v w) :
    D.dist ℓ b u v ≤ pairSum ℓ w :=
  iInf₂_le w h

theorem Decomp.le_dist {ℓ : V → V → ℕ} {b : B} {u v : V} {x : ℕ∞}
    (h : ∀ w, D.IsWalk b u v w → x ≤ pairSum ℓ w) : x ≤ D.dist ℓ b u v :=
  le_iInf₂ h

theorem Decomp.dist_self (ℓ : V → V → ℕ) (b : B) (v : V) : D.dist ℓ b v v = 0 :=
  le_antisymm ((D.dist_le (ℓ := ℓ) (b := b) (w := [v]) ⟨List.IsChain.singleton v, rfl, rfl⟩).trans (by simp))
    zero_le

theorem Decomp.isWalk_of_child {c b : B} (hc : D.child c b) {u v : V} {w : List V} (h : D.IsWalk c u v w) :
    D.IsWalk b u v w :=
  ⟨h.1.imp fun _ _ a => D.child_arc hc a, h.2.1, h.2.2⟩

/-- A walk of a child is a walk of the bag, so the bag has the smaller distances. -/
theorem Decomp.dist_child_le (ℓ : V → V → ℕ) {c b : B} (hc : D.child c b) (u v : V) :
    D.dist ℓ b u v ≤ D.dist ℓ c u v :=
  D.le_dist fun _ hw => D.dist_le (D.isWalk_of_child hc hw)

/-- Two walks that share the junction vertex concatenate. -/
theorem Decomp.isWalk_append {b : B} {u x v : V} {w₁ w₂ : List V} (h₁ : D.IsWalk b u x w₁)
    (h₂ : D.IsWalk b x v w₂) : D.IsWalk b u v (w₁ ++ w₂.tail) := by
  obtain ⟨c₁, e₁, l₁⟩ := h₁
  obtain ⟨c₂, e₂, l₂⟩ := h₂
  obtain ⟨w₂', rfl⟩ := List.head?_eq_some_iff.1 e₂
  obtain ⟨w₁', rfl⟩ := List.getLast?_eq_some_iff.1 l₁
  rw [List.tail_cons]
  refine ⟨?_, ?_, ?_⟩
  · rw [List.append_assoc, List.singleton_append, List.isChain_append]
    rw [List.isChain_append] at c₁
    exact ⟨c₁.1, c₂, fun y hy z hz => c₁.2.2 y hy z hz⟩
  · rw [List.head?_append_of_ne_nil _ (by simp)]
    exact e₁
  · rw [List.append_assoc, List.singleton_append, List.getLast?_append, l₂, Option.some_or]

theorem Decomp.isWalk_concat {c : B} {h u x : V} {p : List V} (hp : D.IsWalk c h u p) (a : D.arc c u x) :
    D.IsWalk c h x (p ++ [x]) :=
  D.isWalk_append hp ⟨List.isChain_pair.2 a, rfl, rfl⟩

/-- The triangle inequality. -/
theorem Decomp.dist_triangle (ℓ : V → V → ℕ) {b : B} (u x v : V) :
    D.dist ℓ b u v ≤ D.dist ℓ b u x + D.dist ℓ b x v :=
  ENat.le_iInf₂_add_iInf₂ fun w₁ h₁ w₂ h₂ =>
    (D.dist_le (D.isWalk_append h₁ h₂)).trans
      (le_of_eq (by rw [pairSum_append ℓ h₁.2.2 h₂.2.1, Nat.cast_add]))

/-! ### Hubs and the hub graph -/

/-- A hub of the bag `X`: a vertex of `X` on the separator of `X` or of an ancestor of `X`. -/
def Decomp.hub (X : B) (a : V) : Prop :=
  D.verts X a ∧ ∃ A, ReflTransGen D.child X A ∧ D.sep A a

theorem Decomp.hub_of_sep {X : B} {a : V} (hs : D.sep X a) (hv : D.verts X a) : D.hub X a :=
  ⟨hv, X, ReflTransGen.refl, hs⟩

/-- The distance between two vertices inside one child of `X`, the least over the children holding both. -/
noncomputable def Decomp.distChild (ℓ : V → V → ℕ) (X : B) (b c : V) : ℕ∞ :=
  ⨅ (Y : B) (_ : D.child Y X) (_ : D.verts Y b) (_ : D.verts Y c), D.dist ℓ Y b c

theorem Decomp.distChild_le {ℓ : V → V → ℕ} {X Y : B} (hY : D.child Y X) {b c : V} (hb : D.verts Y b)
    (hc : D.verts Y c) : D.distChild ℓ X b c ≤ D.dist ℓ Y b c :=
  iInf_le_of_le Y (iInf_le_of_le hY (iInf_le_of_le hb (iInf_le _ hc)))

theorem Decomp.dist_le_distChild (ℓ : V → V → ℕ) (X : B) (b c : V) :
    D.dist ℓ X b c ≤ D.distChild ℓ X b c :=
  le_iInf fun _ => le_iInf fun hY => le_iInf fun _ => le_iInf fun _ => D.dist_child_le ℓ hY b c

/-- `D.IsQWalk X a b q`: `q` is a walk of the hub graph of `X` from `a` to `b`, a list of hubs of `X`. Its length
is `pairSum (D.distChild ℓ X) q`, the sum of `distChild` over its consecutive pairs. -/
def Decomp.IsQWalk (X : B) (a b : V) (q : List V) : Prop :=
  (∀ x ∈ q, D.hub X x) ∧ q.head? = some a ∧ q.getLast? = some b

/-- The distance in the hub graph of `X`: the least length of a walk of the hub graph, `⊤` when there is none. -/
noncomputable def Decomp.distQ (ℓ : V → V → ℕ) (X : B) (a b : V) : ℕ∞ :=
  ⨅ (q : List V) (_ : D.IsQWalk X a b q), pairSum (D.distChild ℓ X) q

theorem Decomp.distQ_le {ℓ : V → V → ℕ} {X : B} {a b : V} {q : List V} (h : D.IsQWalk X a b q) :
    D.distQ ℓ X a b ≤ pairSum (D.distChild ℓ X) q :=
  iInf₂_le q h

theorem Decomp.distQ_self (ℓ : V → V → ℕ) {X : B} {a : V} (ha : D.hub X a) : D.distQ ℓ X a a = 0 := by
  have hmem : ∀ x ∈ [a], D.hub X x := fun x hx => by
    obtain rfl := List.mem_singleton.1 hx
    exact ha
  exact le_antisymm ((D.distQ_le (ℓ := ℓ) (q := [a]) ⟨hmem, rfl, rfl⟩).trans (by simp)) zero_le

/-- A hub in front of a walk of the hub graph. -/
theorem Decomp.distQ_cons_le {ℓ : V → V → ℕ} {X : B} {h u b : V} (hh : D.hub X h) :
    D.distQ ℓ X h b ≤ D.distChild ℓ X h u + D.distQ ℓ X u b := by
  have key : ∀ q, D.IsQWalk X u b q →
      D.distQ ℓ X h b ≤ D.distChild ℓ X h u + pairSum (D.distChild ℓ X) q := by
    intro q hq
    obtain ⟨hq, e₁, e₂⟩ := hq
    obtain ⟨q', rfl⟩ := List.head?_eq_some_iff.1 e₁
    have hmem : ∀ x ∈ h :: u :: q', D.hub X x := by
      intro x hx
      rcases List.mem_cons.1 hx with rfl | hx
      · exact hh
      · exact hq x hx
    exact D.distQ_le (q := h :: u :: q') ⟨hmem, rfl, e₂⟩
  calc D.distQ ℓ X h b
      ≤ ⨅ (q) (_ : D.IsQWalk X u b q), D.distChild ℓ X h u + pairSum (D.distChild ℓ X) q := le_iInf₂ key
    _ = D.distChild ℓ X h u + D.distQ ℓ X u b := by unfold Decomp.distQ; rw [ENat.add_iInf₂]

/-- A hub at the end of a walk of the hub graph. -/
theorem Decomp.distQ_concat_le {ℓ : V → V → ℕ} {X : B} {a b' b : V} (hb : D.hub X b) :
    D.distQ ℓ X a b ≤ D.distQ ℓ X a b' + D.distChild ℓ X b' b := by
  have key : ∀ q, D.IsQWalk X a b' q →
      D.distQ ℓ X a b ≤ pairSum (D.distChild ℓ X) q + D.distChild ℓ X b' b := by
    intro q hq
    obtain ⟨hq, e₁, e₂⟩ := hq
    obtain ⟨q', rfl⟩ := List.head?_eq_some_iff.1 e₁
    have hmem : ∀ x ∈ a :: q' ++ [b], D.hub X x := by
      intro x hx
      rcases List.mem_append.1 hx with hx | hx
      · exact hq x hx
      · obtain rfl := List.mem_singleton.1 hx
        exact hb
    have h := D.distQ_le (ℓ := ℓ) (q := a :: q' ++ [b]) ⟨hmem, rfl, List.getLast?_concat⟩
    rwa [pairSum_concat _ e₂] at h
  calc D.distQ ℓ X a b
      ≤ ⨅ (q) (_ : D.IsQWalk X a b' q), pairSum (D.distChild ℓ X) q + D.distChild ℓ X b' b := le_iInf₂ key
    _ = D.distQ ℓ X a b' + D.distChild ℓ X b' b := by unfold Decomp.distQ; rw [ENat.iInf₂_add]

/-! ### The Exact Labels Lemma -/

/-- A walk of the hub graph from `a` to `b`, followed by the distance from `b`, bounds the distance from `a`. -/
theorem Decomp.dist_le_qwalk_add (ℓ : V → V → ℕ) {X : B} (v : V) :
    ∀ (q : List V) {a b : V}, D.IsQWalk X a b (a :: q) →
      D.dist ℓ X a v ≤ pairSum (D.distChild ℓ X) (a :: q) + D.dist ℓ X b v
  | [], a, b, h => by
    obtain ⟨_, _, e⟩ := h
    simp only [List.getLast?_singleton, Option.some.injEq] at e
    subst e
    simp
  | y :: q, a, b, h => by
    obtain ⟨hq, _, e⟩ := h
    rw [List.getLast?_cons_cons] at e
    have ih := Decomp.dist_le_qwalk_add ℓ v q (a := y) ⟨fun z hz => hq z (List.mem_cons_of_mem _ hz), rfl, e⟩
    calc D.dist ℓ X a v ≤ D.dist ℓ X a y + D.dist ℓ X y v := D.dist_triangle ℓ a y v
      _ ≤ D.distChild ℓ X a y + (pairSum (D.distChild ℓ X) (y :: q) + D.dist ℓ X b v) :=
        add_le_add (D.dist_le_distChild ℓ X a y) ih
      _ = _ := by rw [pairSum_cons_cons, add_assoc]

/-- The easy half of the Exact Labels Lemma: a walk of the hub graph to a hub `b` and a walk of a child from `b`
concatenate to a walk of `X`. -/
theorem Decomp.dist_le_distQ_add (ℓ : V → V → ℕ) {X Y : B} (hY : D.child Y X) (a b v : V) :
    D.dist ℓ X a v ≤ D.distQ ℓ X a b + D.dist ℓ Y b v := by
  calc D.dist ℓ X a v ≤ D.distQ ℓ X a b + D.dist ℓ X b v := ?_
    _ ≤ D.distQ ℓ X a b + D.dist ℓ Y b v := add_le_add le_rfl (D.dist_child_le ℓ hY b v)
  unfold Decomp.distQ
  rw [ENat.iInf₂_add]
  refine le_iInf₂ fun q hq => ?_
  obtain ⟨q', rfl⟩ := List.head?_eq_some_iff.1 hq.2.1
  exact D.dist_le_qwalk_add ℓ v q' hq

/-- The cutting of a walk at its hub visits. A walk `u :: w` of `X` to `v`, after a walk `p` of a child `c` from a
hub `h` to `u`, costs at least a walk of the hub graph from `h` to a hub `b` plus a walk of a child from `b` to
`v`. -/
theorem Decomp.cut (ℓ : V → V → ℕ) {X : B} : ∀ (w : List V) {h u v : V} {c : B} {p : List V},
    D.hub X h → D.child c X → D.IsWalk c h u p → D.verts c h → D.verts c u →
    List.IsChain (D.arc X) (u :: w) → (u :: w).getLast? = some v →
    ∃ Y b, D.child Y X ∧ D.verts Y v ∧ D.hub X b ∧ D.verts Y b ∧
      D.distQ ℓ X h b + D.dist ℓ Y b v ≤ ((pairSum ℓ p : ℕ) : ℕ∞) + ((pairSum ℓ (u :: w) : ℕ) : ℕ∞)
  | [], h, u, v, c, p, hh, hc, hp, hch, hcu, _, e => by
    simp only [List.getLast?_singleton, Option.some.injEq] at e
    subst e
    refine ⟨c, h, hc, hcu, hh, hch, ?_⟩
    rw [D.distQ_self ℓ hh, zero_add]
    exact (D.dist_le hp).trans le_self_add
  | x :: w, h, u, v, c, p, hh, hc, hp, hch, hcu, hw, e => by
    rw [List.isChain_cons_cons] at hw
    rw [List.getLast?_cons_cons] at e
    obtain ⟨c', hc', ha⟩ := D.arc_child hw.1 ⟨c, hc⟩
    by_cases hu : D.hub X u
    · obtain ⟨Y, b, hY, hYv, hb, hYb, ih⟩ := Decomp.cut ℓ w (p := [u, x]) hu hc'
        ⟨List.isChain_pair.2 ha, rfl, rfl⟩ (D.arc_mem ha).1 (D.arc_mem ha).2 hw.2 e
      refine ⟨Y, b, hY, hYv, hb, hYb, ?_⟩
      calc D.distQ ℓ X h b + D.dist ℓ Y b v
          ≤ (D.distChild ℓ X h u + D.distQ ℓ X u b) + D.dist ℓ Y b v :=
            add_le_add (D.distQ_cons_le hh) le_rfl
        _ = D.distChild ℓ X h u + (D.distQ ℓ X u b + D.dist ℓ Y b v) := add_assoc _ _ _
        _ ≤ ((pairSum ℓ p : ℕ) : ℕ∞) + (((pairSum ℓ [u, x] : ℕ) : ℕ∞) + ((pairSum ℓ (x :: w) : ℕ) : ℕ∞)) :=
            add_le_add ((D.distChild_le hc hch hcu).trans (D.dist_le hp)) ih
        _ = ((pairSum ℓ p : ℕ) : ℕ∞) + ((pairSum ℓ (u :: x :: w) : ℕ) : ℕ∞) := by
            simp only [pairSum_cons_cons, pairSum_singleton, Nat.cast_add, add_zero]
    · have hus : ¬ D.sep X u := fun hs => hu (D.hub_of_sep hs (D.arc_mem hw.1).1)
      have e' := D.uniq hc hc' hcu (D.arc_mem ha).1 hus
      subst e'
      obtain ⟨Y, b, hY, hYv, hb, hYb, ih⟩ := Decomp.cut ℓ w hh hc (D.isWalk_concat hp ha) hch
        (D.arc_mem ha).2 hw.2 e
      refine ⟨Y, b, hY, hYv, hb, hYb, ih.trans (le_of_eq ?_)⟩
      rw [pairSum_concat ℓ hp.2.2, pairSum_cons_cons, Nat.cast_add, Nat.cast_add, add_assoc]

/-- The Exact Labels Lemma. In a bag `X` whose children cover it, the distance from a hub `a` to a vertex `v` is the
least sum of a distance in the hub graph from `a` to a hub `b` and a distance from `b` to `v` in a child holding `b`
and `v`. -/
theorem Decomp.exact_labels (ℓ : V → V → ℕ) {X : B}
    (hcov : ∀ v, D.verts X v → ∃ Y, D.child Y X ∧ D.verts Y v) {a v : V} (ha : D.hub X a) :
    D.dist ℓ X a v = ⨅ (Y) (_ : D.child Y X) (_ : D.verts Y v) (b) (_ : D.hub X b) (_ : D.verts Y b),
      D.distQ ℓ X a b + D.dist ℓ Y b v := by
  apply le_antisymm
  · exact le_iInf fun Y => le_iInf fun hY => le_iInf fun _ => le_iInf fun b => le_iInf fun _ =>
      le_iInf fun _ => D.dist_le_distQ_add ℓ hY a b v
  · refine D.le_dist fun w hw => ?_
    obtain ⟨c, hc, hca⟩ := hcov a ha.1
    obtain ⟨w', rfl⟩ := List.head?_eq_some_iff.1 hw.2.1
    obtain ⟨Y, b, hY, hYv, hb, hYb, h⟩ := D.cut ℓ w' (p := [a]) ha hc ⟨List.IsChain.singleton a, rfl, rfl⟩
      hca hca hw.1 hw.2.2
    refine iInf_le_of_le Y (iInf_le_of_le hY (iInf_le_of_le hYv (iInf_le_of_le b (iInf_le_of_le hb
      (iInf_le_of_le hYb ?_)))))
    simpa using h

/-- Between hubs, the hub graph has the distances of `X`. -/
theorem Decomp.distQ_eq (ℓ : V → V → ℕ) {X : B}
    (hcov : ∀ v, D.verts X v → ∃ Y, D.child Y X ∧ D.verts Y v) {a b : V} (ha : D.hub X a) (hb : D.hub X b) :
    D.distQ ℓ X a b = D.dist ℓ X a b := by
  rw [D.exact_labels ℓ hcov ha]
  apply le_antisymm
  · exact le_iInf fun Y => le_iInf fun hY => le_iInf fun hYb => le_iInf fun b' => le_iInf fun _ =>
      le_iInf fun hYb' =>
        (D.distQ_concat_le (b' := b') hb).trans (add_le_add le_rfl (D.distChild_le hY hYb' hYb))
  · obtain ⟨Y, hY, hYb⟩ := hcov b hb.1
    refine iInf_le_of_le Y (iInf_le_of_le hY (iInf_le_of_le hYb (iInf_le_of_le b (iInf_le_of_le hb
      (iInf_le_of_le hYb ?_)))))
    rw [D.dist_self, add_zero]

end PlanarMatching
