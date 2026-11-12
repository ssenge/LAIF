import Mathlib.Logic.Relation
import Mathlib.Order.WellFounded

/-!
# What the decomposition gives

`notes/MATCHING.md`, Facts 1 and 2, the J path, the outer recursion, and the Multi-Source Lemma, from the listed
properties alone. `Decomp` asks for (B2), (B3) and (B4) of the note: an arc of a bag lies in a child, a vertex off
the separator lies in one child only, and a bag with no child has `sep = V`. Planarity plays no part here.
-/

namespace PlanarMatching

open Relation

/-- A tree of bags on a digraph, by the properties the note lists. -/
structure Decomp (V B : Type*) where
  verts : B → V → Prop
  arc : B → V → V → Prop
  sep : B → V → Prop
  /-- `child c b`: the bag `c` is a child of the bag `b`. -/
  child : B → B → Prop
  wf : WellFounded child
  arc_mem : ∀ {b u v}, arc b u v → verts b u ∧ verts b v
  child_verts : ∀ {c b v}, child c b → verts c v → verts b v
  child_arc : ∀ {c b u v}, child c b → arc c u v → arc b u v
  arc_child : ∀ {b u v}, arc b u v → (∃ c, child c b) → ∃ c, child c b ∧ arc c u v
  /-- A vertex of a bag off the separator lies on a child, unless the bag is a leaf. -/
  off_child : ∀ {b v}, verts b v → ¬ sep b v → ∃ c, child c b ∧ verts c v
  /-- (B3): a vertex off the separator lies on at most one child. -/
  uniq : ∀ {b c c' v}, child c b → child c' b → verts c v → verts c' v → ¬ sep b v → c = c'
  /-- (B4): a leaf has `sep = V`. -/
  leaf : ∀ {b v}, (¬ ∃ c, child c b) → verts b v → sep b v

variable {V B : Type*} (D : Decomp V B)

/-- Reachability inside a bag. -/
def Decomp.Reach (b : B) : V → V → Prop := ReflTransGen (D.arc b)

theorem Decomp.reach_mono {c b : B} (h : D.child c b) {u v : V} (r : D.Reach c u v) : D.Reach b u v := by
  induction r with
  | refl => exact ReflTransGen.refl
  | tail _ a ih => exact ih.tail (D.child_arc h a)

theorem Decomp.reach_mem {b : B} {u v : V} (hu : D.verts b u) (r : D.Reach b u v) : D.verts b v := by
  induction r with
  | refl => exact hu
  | tail _ h _ => exact (D.arc_mem h).2

/-- Fact 1: a path that avoids the separator stays in the one child of its start. -/
theorem Decomp.stays {b c : B} {u v : V} (hc : D.child c b) (hu : D.verts c u)
    (r : D.Reach b u v) (hav : ∀ x, D.Reach b u x → D.Reach b x v → ¬ D.sep b x) :
    D.Reach c u v := by
  have key : ∀ x, D.Reach b u x → D.Reach b x v → D.Reach c u x ∧ D.verts c x := by
    intro x hx
    induction hx with
    | refl => intro _; exact ⟨ReflTransGen.refl, hu⟩
    | tail hxy harc ih =>
      rename_i x' y
      intro hyv
      have hxv : D.Reach b x' v := ReflTransGen.head harc hyv
      obtain ⟨h1, h2⟩ := ih hxv
      obtain ⟨c', hc', ha⟩ := D.arc_child harc ⟨c, hc⟩
      have e := D.uniq hc hc' h2 (D.arc_mem ha).1 (hav x' hxy hxv)
      subst e
      exact ⟨h1.tail ha, (D.arc_mem ha).2⟩
  exact (key v r ReflTransGen.refl).1

/-- `D.OnChain Y x b`: going down from `b` to `Y`, `x` never lies on a separator of a proper ancestor of `Y`. This is
`x ∈ Y°` of the note, relative to `b`. -/
inductive Decomp.OnChain : B → V → B → Prop
  | here {b x} : D.verts b x → Decomp.OnChain b x b
  | down {Y b c x} : D.child c b → D.verts b x → ¬ D.sep b x → Decomp.OnChain Y x c → Decomp.OnChain Y x b

theorem Decomp.OnChain.mem_top {Y b : B} {x : V} (h : D.OnChain Y x b) : D.verts b x := by
  cases h <;> assumption

theorem Decomp.OnChain.mem {Y b : B} {x : V} (h : D.OnChain Y x b) : D.verts Y x := by
  induction h with
  | here h => exact h
  | down _ _ _ _ ih => exact ih

/-- A bag `Y` below `b` carries no more reachability than `b`. -/
theorem Decomp.OnChain.reach {Y b : B} {x : V} (h : D.OnChain Y x b) {u v : V} (r : D.Reach Y u v) :
    D.Reach b u v := by
  induction h with
  | here _ => exact r
  | down hc _ _ _ ih => exact D.reach_mono hc ih

/-- Facts 1 and 2, and the core of the Multi-Source Lemma. A path in `b` meets the separator of a bag `Y` that is on the
chains of both ends. -/
theorem Decomp.descent (b : B) : ∀ {u v : V}, D.verts b u → D.Reach b u v →
    ∃ Y h, D.OnChain Y u b ∧ D.OnChain Y v b ∧ D.sep Y h ∧ D.Reach Y u h ∧ D.Reach Y h v := by
  refine D.wf.induction (C := fun b => ∀ {u v : V}, D.verts b u → D.Reach b u v →
    ∃ Y h, D.OnChain Y u b ∧ D.OnChain Y v b ∧ D.sep Y h ∧ D.Reach Y u h ∧ D.Reach Y h v) b ?_
  intro b ih u v hu r
  by_cases hit : ∃ x, D.Reach b u x ∧ D.Reach b x v ∧ D.sep b x
  · obtain ⟨x, h1, h2, h3⟩ := hit
    exact ⟨b, x, .here hu, .here (D.reach_mem hu r), h3, h1, h2⟩
  · have hav : ∀ x, D.Reach b u x → D.Reach b x v → ¬ D.sep b x := fun x h1 h2 h3 => hit ⟨x, h1, h2, h3⟩
    have hus := hav u ReflTransGen.refl r
    obtain ⟨c, hc, huc⟩ := D.off_child hu hus
    have rc := D.stays hc huc r hav
    obtain ⟨Y, h, a1, a2, a3, a4, a5⟩ := ih c hc huc rc
    have hvs := hav v r ReflTransGen.refl
    exact ⟨Y, h, .down hc hu hus a1, .down hc (D.reach_mem hu r) hvs a2, a3, a4, a5⟩

/-- The Multi-Source Lemma, soundness and completeness: `v` is reached from a member of `S` in `b` exactly when some bag
`Y` on the chain of `v` has a hub reached from a source on the chain, within `Y`, and that hub reaches `v` within `Y`. -/
theorem Decomp.multiSource (b : B) (S : V → Prop) (hS : ∀ a, S a → D.verts b a) (v : V) :
    (∃ a, S a ∧ D.Reach b a v) ↔
      (∃ Y h a, D.OnChain Y v b ∧ S a ∧ D.OnChain Y a b ∧ D.sep Y h ∧ D.Reach Y a h ∧ D.Reach Y h v) := by
  constructor
  · rintro ⟨a, ha, r⟩
    obtain ⟨Y, h, a1, a2, a3, a4, a5⟩ := D.descent b (hS a ha) r
    exact ⟨Y, h, a, a2, ha, a1, a3, a4, a5⟩
  · rintro ⟨Y, h, a, h1, ha, _, _, a4, a5⟩
    exact ⟨a, ha, h1.reach D (a4.trans a5)⟩

/-- An arc of the digraph `J` of a request `(u,v)` in `Y`. -/
def Decomp.JArc (Y : B) (u v a b : V) : Prop :=
  (a = u ∨ D.sep Y a) ∧ (b = v ∨ D.sep Y b) ∧ ∃ c, D.child c Y ∧ D.verts c a ∧ D.Reach c a b

/-- Fact 1, the cutting: `u ⇝_Y v` gives a path of `J`, whose arcs each lie in one child of `Y` and whose nodes between
the ends are on the separator. -/
theorem Decomp.jpath {Y : B} {u v : V} (r : D.Reach Y u v) (hint : ∃ c, D.child c Y) :
    ReflTransGen (D.JArc Y u v) u v := by
  have key : ∀ w, D.Reach Y u w → ∃ x, ReflTransGen (D.JArc Y u v) u x ∧ (x = u ∨ D.sep Y x) ∧
      (w = x ∨ ∃ c, D.child c Y ∧ D.verts c x ∧ D.Reach c x w ∧ D.verts c w) := by
    intro w hw
    induction hw with
    | refl => exact ⟨u, ReflTransGen.refl, Or.inl rfl, Or.inl rfl⟩
    | tail hw' harc ih =>
      rename_i w' w''
      obtain ⟨x, hx, hxs, hst⟩ := ih
      obtain ⟨c', hc', ha⟩ := D.arc_child harc hint
      by_cases hsw : D.sep Y w'
      · have hx' : ReflTransGen (D.JArc Y u v) u w' := by
          rcases hst with rfl | ⟨c, hc, hxc, hr, _⟩
          · exact hx
          · exact hx.tail ⟨hxs, Or.inr hsw, c, hc, hxc, hr⟩
        exact ⟨w', hx', Or.inr hsw, Or.inr ⟨c', hc', (D.arc_mem ha).1, ReflTransGen.single ha, (D.arc_mem ha).2⟩⟩
      · rcases hst with rfl | ⟨c, hc, hxc, hr, hwc⟩
        · exact ⟨w', hx, hxs, Or.inr ⟨c', hc', (D.arc_mem ha).1, ReflTransGen.single ha, (D.arc_mem ha).2⟩⟩
        · have e := D.uniq hc hc' hwc (D.arc_mem ha).1 hsw
          subst e
          exact ⟨x, hx, hxs, Or.inr ⟨c, hc, hxc, hr.tail ha, (D.arc_mem ha).2⟩⟩
  obtain ⟨x, hx, hxs, hst⟩ := key v r
  rcases hst with rfl | ⟨c, hc, hxc, hr, _⟩
  · exact hx
  · exact hx.tail ⟨hxs, Or.inl rfl, c, hc, hxc, hr⟩

theorem Decomp.no_cycle (c : B) : ¬ TransGen D.child c c := by
  refine D.wf.induction (C := fun c => ¬ TransGen D.child c c) c ?_
  intro c ih h
  obtain ⟨d, h1, h2⟩ := TransGen.tail'_iff.mp h
  exact ih d h2 (TransGen.head' h2 h1)

theorem Decomp.OnChain.toTop {Y b : B} {x : V} (h : D.OnChain Y x b) : ReflTransGen D.child Y b := by
  induction h with
  | here _ => exact ReflTransGen.refl
  | down hc _ _ _ ih => exact ih.tail hc

/-- `X°` on one chain: two bags whose `X°` hold a common vertex are comparable. So bags of one depth have disjoint `X°`. -/
theorem Decomp.chain_comparable {x : V} {b X X' : B} (h : D.OnChain X x b) (h' : D.OnChain X' x b) :
    D.OnChain X x X' ∨ D.OnChain X' x X := by
  induction h generalizing X' with
  | here _ => exact Or.inr h'
  | down hc hb hs hrest ih =>
    cases h' with
    | here _ => exact Or.inl (.down hc hb hs hrest)
    | down hc' _ _ h2 =>
      have e := D.uniq hc hc' (Decomp.OnChain.mem_top D hrest) (Decomp.OnChain.mem_top D h2) hs
      subst e
      exact ih h2

/-- `G[X°] ⊆ X`: an arc of `b` between two vertices on the chain of `X` lies in `X`. -/
theorem Decomp.arc_in_chain {X b : B} {u v : V} (hu : D.OnChain X u b) (hv : D.OnChain X v b) (a : D.arc b u v) :
    D.arc X u v := by
  induction hu generalizing v with
  | here _ => exact a
  | down hc hb hs hrest ih =>
    obtain ⟨c', hc', ha⟩ := D.arc_child a ⟨_, hc⟩
    have e := D.uniq hc hc' (Decomp.OnChain.mem_top D hrest) (D.arc_mem ha).1 hs
    subst e
    cases hv with
    | here _ =>
      exact absurd (TransGen.head' hc (Decomp.OnChain.toTop D hrest)) (D.no_cycle _)
    | down hc2 _ hs2 hrest2 =>
      have e2 := D.uniq hc hc2 (D.arc_mem ha).2 (Decomp.OnChain.mem_top D hrest2) hs2
      subst e2
      exact ih hrest2 ha

/-- Vertices of two different children, off the separator, have no arc between them. -/
theorem Decomp.no_cross {X c c' : B} {u v : V} (hc : D.child c X) (hc' : D.child c' X)
    (hu : D.verts c u) (hv : D.verts c' v) (hus : ¬ D.sep X u) (hvs : ¬ D.sep X v) (a : D.arc X u v) : c = c' := by
  obtain ⟨d, hd, ha⟩ := D.arc_child a ⟨_, hc⟩
  have e1 := D.uniq hc hd hu (D.arc_mem ha).1 hus
  have e2 := D.uniq hc' hd hv (D.arc_mem ha).2 hvs
  rw [e1, e2]

end PlanarMatching
