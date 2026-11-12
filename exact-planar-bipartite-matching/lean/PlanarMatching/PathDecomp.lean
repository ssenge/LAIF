import PlanarMatching.PathAssembly
import PlanarMatching.Decomp

/-!
# The paths of requests on the tree of bags

`notes/MATCHING.md`, Section 3, on a `Decomp`. The digraph `J` of a request `(u, v)` in `Y` has the nodes `u`, `v` and
the separator of `Y`, and an arc labelled `c` from `a` to `d` when `a` is on the child `c` and `a ⇝_c d`. A request in
a bag with children takes a path of `J` with least hops (it exists by `Decomp.jpath`), asks each child for the path of
its segment, and erases the loops of the joined walk; a leaf answers with a given leaf path.

* `Decomp.pathOf_spec`: every request `(u, v)` with `u` on `Y` and `u ⇝_Y v` gets a simple directed `u`-`v` path
  inside its interval, when every leaf path is one.
* `Decomp.repeat_sep` (Lemma C) and `Decomp.visits` (Lemma B): a vertex that repeats in the walk of a request lies on
  the separator, and a vertex of the separator has at most two visits in it.
-/

namespace PlanarMatching

open Relation

set_option linter.unusedSectionVars false

variable {V B : Type*}

/-- A sequence of steps for a reflexive transitive closure. -/
theorem exists_seq {R : V → V → Prop} {u v : V} (h : ReflTransGen R u v) :
    ∃ (k : ℕ) (y : ℕ → V), y 0 = u ∧ y k = v ∧ ∀ i < k, R (y i) (y (i + 1)) := by
  induction h with
  | refl => exact ⟨0, fun _ => u, rfl, rfl, fun i hi => absurd hi (Nat.not_lt_zero _)⟩
  | @tail b c _ hbc ih =>
    obtain ⟨k, y, h0, hk, hs⟩ := ih
    refine ⟨k + 1, fun i => if i ≤ k then y i else c, by simp [h0], by simp, fun i hi => ?_⟩
    by_cases h : i < k
    · simp only [show i ≤ k by omega, show i + 1 ≤ k by omega, ite_true]
      exact hs i h
    · obtain rfl : i = k := by omega
      simp only [le_refl, ite_true, show ¬ (i + 1 ≤ i) by omega, ite_false]
      rw [hk]
      exact hbc

theorem walk_congr {u : V} {π π' : ℕ → List V} : ∀ {i : ℕ}, (∀ j < i, π j = π' j) → walk u π i = walk u π' i
  | 0, _ => rfl
  | i + 1, h => by rw [walk, walk, walk_congr (fun j hj => h j (by omega)), h i (by omega)]

theorem SPath.mono {E : V → V → Prop} {S S' : Set V} {u v : V} {p : List V} (h : SPath E S u v p)
    (hS : ∀ x ∈ p, x ∈ S → x ∈ S') : SPath E S' u v p :=
  ⟨h.chain, h.nodup, h.head, h.last, fun x hx => hS x hx (h.sub x hx)⟩

variable (D : Decomp V B)

/-- The arcs of `J` in `Y`, labelled by the child that realizes them. -/
def Decomp.JR (Y c : B) (a d : V) : Prop := D.child c Y ∧ D.verts c a ∧ D.Reach c a d

/-- The nodes of `J` for the request `(u, v)` in `Y`. -/
def Decomp.JN (Y : B) (u v : V) : Set V := {a | a = u ∨ a = v ∨ D.sep Y a}

theorem Decomp.exists_jpath {Y : B} {u v : V} (r : D.Reach Y u v) (hint : ∃ c, D.child c Y) :
    ∃ k y, JPath (D.JN Y u v) (D.JR Y) u v k y := by
  obtain ⟨k, y, h0, hk, hs⟩ := exists_seq (D.jpath r hint)
  refine ⟨k, y, ⟨h0, hk, fun i hi => ?_, fun i hi => ?_⟩⟩
  · cases i with
    | zero => exact Or.inl h0
    | succ j =>
      rcases (hs j (by omega)).2.1 with h | h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
  · obtain ⟨-, -, c, hc, hv, hr⟩ := hs i hi
    exact ⟨c, hc, hv, hr⟩

open Classical in
/-- The least number of hops of a path of `J`. -/
noncomputable def Decomp.hops (Y : B) (u v : V) : ℕ :=
  if h : ∃ k y, JPath (D.JN Y u v) (D.JR Y) u v k y then Nat.find h else 0

open Classical in
/-- A path of `J` with least hops. -/
noncomputable def Decomp.seq (Y : B) (u v : V) : ℕ → V :=
  if h : ∃ k y, JPath (D.JN Y u v) (D.JR Y) u v k y then Classical.choose (Nat.find_spec h) else fun _ => u

open Classical in
/-- The child that realizes the arc `i` of the path. -/
noncomputable def Decomp.lblOf (Y : B) (u v : V) (i : ℕ) : B :=
  if h : ∃ c, D.JR Y c (D.seq Y u v i) (D.seq Y u v (i + 1)) then Classical.choose h else Y

open Classical in
theorem Decomp.hops_spec {Y : B} {u v : V} (r : D.Reach Y u v) (hint : ∃ c, D.child c Y) :
    JPath (D.JN Y u v) (D.JR Y) u v (D.hops Y u v) (D.seq Y u v) ∧
      ∀ k' y', JPath (D.JN Y u v) (D.JR Y) u v k' y' → D.hops Y u v ≤ k' := by
  have hex := D.exists_jpath r hint
  refine ⟨?_, fun k' y' h => ?_⟩
  · simp only [Decomp.hops, Decomp.seq, dite_eq_left hex]
    exact Classical.choose_spec (Nat.find_spec hex)
  · simp only [Decomp.hops, dite_eq_left hex]
    exact Nat.find_min' hex ⟨y', h⟩

open Classical in
theorem Decomp.lbl_spec {Y : B} {u v : V} {k : ℕ} (hP : JPath (D.JN Y u v) (D.JR Y) u v k (D.seq Y u v))
    {i : ℕ} (hi : i < k) : D.JR Y (D.lblOf Y u v i) (D.seq Y u v i) (D.seq Y u v (i + 1)) := by
  have h := hP.arc i hi
  simp only [Decomp.lblOf, dite_eq_left h]
  exact Classical.choose_spec h

variable [DecidableEq V]

open Classical in
/-- The path of a request: a leaf answers with `leafPath`; a bag with children joins the paths of the segments of a
least-hop path of `J` and erases the loops. -/
noncomputable def Decomp.pathOf (leafPath : B → V → V → List V) : B → V → V → List V :=
  D.wf.fix (C := fun _ => V → V → List V) fun Y rec u v =>
    if ∃ c, D.child c Y then
      loopErase (walk u (fun i => if h : D.child (D.lblOf Y u v i) Y then
        rec _ h (D.seq Y u v i) (D.seq Y u v (i + 1)) else []) (D.hops Y u v))
    else leafPath Y u v

/-- The joined walk of a request in a bag with children. -/
noncomputable def Decomp.walkOf (leafPath : B → V → V → List V) (Y : B) (u v : V) : List V :=
  walk u (fun i => D.pathOf leafPath (D.lblOf Y u v i) (D.seq Y u v i) (D.seq Y u v (i + 1))) (D.hops Y u v)

open Classical in
theorem Decomp.pathOf_unfold (leafPath : B → V → V → List V) (Y : B) (u v : V) :
    D.pathOf leafPath Y u v = if ∃ c, D.child c Y then
      loopErase (walk u (fun i => if _h : D.child (D.lblOf Y u v i) Y then
        D.pathOf leafPath (D.lblOf Y u v i) (D.seq Y u v i) (D.seq Y u v (i + 1)) else []) (D.hops Y u v))
    else leafPath Y u v := by
  unfold Decomp.pathOf
  rw [WellFounded.fix_eq]

theorem Decomp.pathOf_eq {leafPath : B → V → V → List V} {Y : B} {u v : V} (hint : ∃ c, D.child c Y)
    (hc : ∀ i < D.hops Y u v, D.child (D.lblOf Y u v i) Y) :
    D.pathOf leafPath Y u v = loopErase (D.walkOf leafPath Y u v) := by
  rw [D.pathOf_unfold, ite_eq_left hint, Decomp.walkOf]
  congr 1
  exact walk_congr fun i hi => by rw [dite_eq_left (hc i hi)]

variable {E : V → V → Prop} {leafPath : B → V → V → List V}

/-- Every request gets a simple directed path inside its interval, when every leaf path is one. -/
theorem Decomp.pathOf_spec
    (hleaf : ∀ Y u v, (¬ ∃ c, D.child c Y) → D.verts Y u → D.Reach Y u v →
      SPath E (Interval (D.Reach Y) u v) u v (leafPath Y u v)) :
    ∀ Y u v, D.verts Y u → D.Reach Y u v →
      SPath E (Interval (D.Reach Y) u v) u v (D.pathOf leafPath Y u v) := by
  intro Y
  induction Y using D.wf.induction with
  | _ Y ih =>
  intro u v hu r
  by_cases hint : ∃ c, D.child c Y
  · have hP := (D.hops_spec r hint).1
    have hl := fun i (hi : i < D.hops Y u v) => D.lbl_spec hP hi
    rw [D.pathOf_eq hint (fun i hi => (hl i hi).1), Decomp.walkOf]
    exact realize (R := D.Reach) (lbl := D.lblOf Y u v) (fun i hi a d h => D.reach_mono (hl i hi).1 h)
      (fun a => (ReflTransGen.refl : D.Reach Y a a)) (fun a b d h1 h2 => ReflTransGen.trans h1 h2)
      hP.start hP.stop (fun i hi => ih _ (hl i hi).1 _ _ (hl i hi).2.1 (hl i hi).2.2)
  · rw [D.pathOf_unfold, ite_eq_right hint]
    exact hleaf Y u v hint hu r

/-- The segment paths lie in the intervals of `J`. -/
theorem Decomp.segment_spec
    (hleaf : ∀ Y u v, (¬ ∃ c, D.child c Y) → D.verts Y u → D.Reach Y u v →
      SPath E (Interval (D.Reach Y) u v) u v (leafPath Y u v))
    {Y : B} {u v : V} (r : D.Reach Y u v) (hint : ∃ c, D.child c Y) :
    ∀ i < D.hops Y u v, SPath E (Interval (D.JR Y (D.lblOf Y u v i)) (D.seq Y u v i) (D.seq Y u v (i + 1)))
      (D.seq Y u v i) (D.seq Y u v (i + 1))
      (D.pathOf leafPath (D.lblOf Y u v i) (D.seq Y u v i) (D.seq Y u v (i + 1))) := by
  intro i hi
  obtain ⟨hc, hv, hr⟩ := D.lbl_spec (D.hops_spec r hint).1 hi
  refine (D.pathOf_spec hleaf _ _ _ hv hr).mono fun x _ hx => ⟨⟨hc, hv, hx.1⟩, ⟨hc, D.reach_mem hv hx.1, hx.2⟩⟩

/-- **Lemma C** on the tree of bags: a vertex that repeats in the walk of a request lies on the separator. -/
theorem Decomp.repeat_sep
    (hleaf : ∀ Y u v, (¬ ∃ c, D.child c Y) → D.verts Y u → D.Reach Y u v →
      SPath E (Interval (D.Reach Y) u v) u v (leafPath Y u v))
    {Y : B} {u v : V} (r : D.Reach Y u v) (hint : ∃ c, D.child c Y) {x : V}
    (h : 1 < (D.walkOf leafPath Y u v).count x) : D.sep Y x := by
  obtain ⟨hP, hmin⟩ := D.hops_spec r hint
  exact walk_repeat (R := D.JR Y) (inBag := fun c a => D.child c Y ∧ D.verts c a) (sep := {x | D.sep Y x})
    (fun _ _ _ _ h1 h2 => ⟨h1.1, h1.2.1, ReflTransGen.trans h1.2.2 h2.2.2⟩) (fun _ _ _ h => ⟨h.1, h.2.1⟩)
    (fun _ hx _ _ h1 h2 => D.uniq h1.1 h2.1 h1.2 h2.2 hx) (noShortcut_of_least hP hmin) hP.start
    (D.segment_spec hleaf r hint) x h

/-- **Lemma B** on the tree of bags: a vertex of the separator has at most two visits in the walk of a request. -/
theorem Decomp.visits
    (hleaf : ∀ Y u v, (¬ ∃ c, D.child c Y) → D.verts Y u → D.Reach Y u v →
      SPath E (Interval (D.Reach Y) u v) u v (leafPath Y u v))
    {Y : B} {u v : V} (r : D.Reach Y u v) (hint : ∃ c, D.child c Y) {x : V} (hx : D.sep Y x) :
    (D.walkOf leafPath Y u v).count x ≤ 2 := by
  obtain ⟨hP, hmin⟩ := D.hops_spec r hint
  exact lemmaB hP hmin (D.segment_spec hleaf r hint) (Or.inr (Or.inr hx))

end PlanarMatching
