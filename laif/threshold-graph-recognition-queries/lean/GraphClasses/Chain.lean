import GraphClasses.Threshold

/-!
# Chain graphs

A chain graph is a bipartite graph whose neighbourhoods on one side are nested, plus possibly isolated vertices. An
isolated vertex has an empty neighbourhood, so it fits on either side and needs no separate clause.
-/

open Finset

namespace GraphClasses

variable {V : Type*}

/-- The neighbourhoods of `u` and `v` are comparable. -/
def Comparable (G : SimpleGraph V) (u v : V) : Prop :=
  (∀ t, G.Adj u t → G.Adj v t) ∨ (∀ t, G.Adj v t → G.Adj u t)

/-- **Chain graph.** The sides are given by `side`, every edge goes across, and the neighbourhoods on side `false` are
nested. -/
def IsChain (G : SimpleGraph V) : Prop :=
  ∃ side : V → Bool, (∀ u v, G.Adj u v → side u ≠ side v) ∧
    ∀ u v, side u = false → side v = false → Comparable G u v

/-- The neighbourhoods on the other side are nested as well. -/
theorem comparable_other {G : SimpleGraph V} {side : V → Bool} (hb : ∀ u v, G.Adj u v → side u ≠ side v)
    (hc : ∀ u v, side u = false → side v = false → Comparable G u v) {u v : V} (hu : side u = true)
    (hv : side v = true) : Comparable G u v := by
  by_contra hno
  simp only [Comparable, not_or] at hno
  push Not at hno
  obtain ⟨⟨s, hus, hvs⟩, t, hvt, hut⟩ := hno
  have hs : side s = false := by
    have := hb u s hus
    rw [hu] at this
    simpa using this.symm
  have ht : side t = false := by
    have := hb v t hvt
    rw [hv] at this
    simpa using this.symm
  rcases hc s t hs ht with g | g
  · exact hut (g u hus.symm).symm
  · exact hvs (g v hvt.symm).symm

/-- A chain graph has comparable neighbourhoods on both sides. -/
theorem comparable_same {G : SimpleGraph V} {side : V → Bool} (hb : ∀ u v, G.Adj u v → side u ≠ side v)
    (hc : ∀ u v, side u = false → side v = false → Comparable G u v) {u v : V} (huv : side u = side v) :
    Comparable G u v := by
  cases hu : side u
  · exact hc u v hu (by rw [← huv, hu])
  · exact comparable_other hb hc hu (by rw [← huv, hu])

/-- A chain graph has no induced `2K₂`. This is what the hard family breaks. -/
theorem IsChain.no_two_K2 {G : SimpleGraph V} (h : IsChain G) {a b c d : V} (hab : G.Adj a b) (hcd : G.Adj c d)
    (hac : ¬ G.Adj a c) (had : ¬ G.Adj a d) (hbc : ¬ G.Adj b c) (hbd : ¬ G.Adj b d) : False := by
  obtain ⟨side, hb, hc⟩ := h
  have h1 := hb a b hab
  have h2 := hb c d hcd
  by_cases hs : side a = side c
  · rcases comparable_same hb hc hs with g | g
    · exact hbc (g b hab).symm
    · exact had (g d hcd)
  · have hs' : side a = side d := by
      cases ha : side a <;> cases hc' : side c <;> cases hd : side d <;> simp_all
    rcases comparable_same hb hc hs' with g | g
    · exact hbd (g b hab).symm
    · exact hac (g c hcd.symm)

variable [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The neighbourhood of a set, the columns having a `1` in the rows `X`. -/
def nbrs (X : Finset V) : Finset V := holdingSet (adjM G) X univ true

theorem mem_nbrs {X : Finset V} {v : V} : v ∈ nbrs G X ↔ ∃ u ∈ X, G.Adj u v := by
  simp [nbrs, holdingSet]

/-- **The three-step discovery.** Given an edge `(x, y)`: read `X := N(y)`; with Holding compute `Y := N(X)`; with
Holding compute `X := N(Y)`. The result is `(X, Y)`. -/
def discover (s : Search (V × V)) (y : V) : Finset V × Finset V :=
  let X := univ.filter fun v => G.Adj y v
  let Y := holding s (adjM G) X univ true (Fintype.card V + 1) ∅
  (holding s (adjM G) Y univ true (Fintype.card V + 1) ∅, Y)

/-- The vertices on a given side that are not isolated. -/
def sideVerts (side : V → Bool) (b : Bool) : Finset V :=
  univ.filter fun v => side v = b ∧ ∃ t, G.Adj v t

variable {G}

theorem mem_sideVerts {side : V → Bool} {b : Bool} {v : V} :
    v ∈ sideVerts G side b ↔ side v = b ∧ ∃ t, G.Adj v t := by
  simp [sideVerts]

open Classical in
/-- A vertex whose neighbourhood contains that of every vertex on its side. -/
private theorem exists_top {side : V → Bool} (hb : ∀ u v, G.Adj u v → side u ≠ side v)
    (hc : ∀ u v, side u = false → side v = false → Comparable G u v) (b : Bool) {a₀ : V} (ha₀ : side a₀ = b) :
    ∃ a, side a = b ∧ ∀ u, side u = b → ∀ t, G.Adj u t → G.Adj a t := by
  let T := univ.filter fun v => side v = b
  have hT : T.Nonempty := ⟨a₀, mem_filter.2 ⟨mem_univ _, ha₀⟩⟩
  obtain ⟨a, ha, hmax⟩ := exists_max_image T (fun v => (univ.filter fun t => G.Adj v t).card) hT
  have hab := (mem_filter.1 ha).2
  refine ⟨a, hab, fun u hu t hut => ?_⟩
  rcases comparable_same hb hc (hab.trans hu.symm) with g | g
  · -- `N(a) ⊆ N(u)` and `|N(u)| ≤ |N(a)|`, so they are equal.
    have hsub : (univ.filter fun t => G.Adj a t) ⊆ univ.filter fun t => G.Adj u t := by
      intro z hz
      simp only [mem_filter, mem_univ, true_and] at hz ⊢
      exact g z hz
    have heq := eq_of_subset_of_card_le hsub (hmax u (mem_filter.2 ⟨mem_univ _, hu⟩))
    have : t ∈ univ.filter fun t => G.Adj u t := by simpa using hut
    rw [← heq] at this
    simpa using this
  · exact g t hut

/-- **Chain graph sides.** In a chain graph with an edge `xy`, the three-step discovery reaches exactly all
non-isolated vertices: `Y` those on the side of `y`, and `X` those on the side of `x`. Correct searches assumed. -/
theorem discover_correct {s : Search (V × V)} (hs : SearchSpec s) {side : V → Bool}
    (hb : ∀ u v, G.Adj u v → side u ≠ side v)
    (hc : ∀ u v, side u = false → side v = false → Comparable G u v) {x y : V} (hxy : G.Adj x y) :
    (discover G s y).1 = sideVerts G side (side x) ∧ (discover G s y).2 = sideVerts G side (side y) := by
  have hcard : ∀ X : Finset V, holding s (adjM G) X univ true (Fintype.card V + 1) ∅ = nbrs G X := fun X =>
    holding_correct hs (adjM G) X univ true
  obtain ⟨a, ha, htop⟩ := exists_top hb hc (side x) (a₀ := x) rfl
  have hY : holding s (adjM G) (univ.filter fun v => G.Adj y v) univ true (Fintype.card V + 1) ∅ =
      sideVerts G side (side y) := by
    rw [hcard]
    ext v
    simp only [mem_nbrs, mem_filter, mem_univ, true_and, sideVerts]
    constructor
    · rintro ⟨u, hyu, huv⟩
      have h1 := hb y u hyu
      have h2 := hb u v huv
      refine ⟨?_, u, huv.symm⟩
      cases hsy : side y <;> cases hsu : side u <;> cases hsv : side v <;> simp_all
    · rintro ⟨hv, t, hvt⟩
      -- The top vertex `a` of the side of `x` sees every non-isolated vertex on the side of `y`.
      have hts : side t = side x := by
        have h1 := hb v t hvt
        have h2 := hb x y hxy
        cases hsx : side x <;> cases hsy : side y <;> cases hsv : side v <;> cases hst : side t <;> simp_all
      exact ⟨a, (htop x rfl y hxy).symm, htop t hts v hvt.symm⟩
  refine ⟨?_, hY⟩
  have hdisc : (discover G s y).1 = holding s (adjM G)
      (holding s (adjM G) (univ.filter fun v => G.Adj y v) univ true (Fintype.card V + 1) ∅) univ true
      (Fintype.card V + 1) ∅ := rfl
  rw [hdisc, hY, hcard]
  ext v
  simp only [mem_nbrs, mem_filter, mem_univ, true_and, sideVerts]
  constructor
  · rintro ⟨u, ⟨hu, _⟩, huv⟩
    have h1 := hb u v huv
    have h2 := hb x y hxy
    refine ⟨?_, u, huv.symm⟩
    cases hsx : side x <;> cases hsy : side y <;> cases hsu : side u <;> cases hsv : side v <;> simp_all
  · rintro ⟨hv, t, hvt⟩
    have h1 := hb v t hvt
    have h2 := hb x y hxy
    refine ⟨t, ⟨?_, v, hvt.symm⟩, hvt.symm⟩
    cases hsx : side x <;> cases hsy : side y <;> cases hsv : side v <;> cases hst : side t <;> simp_all

/-- The recognizer of Theorem 4. Search for an edge; if none exists, accept. Otherwise discover `(X, Y)`, reject if
they meet, Learn `X × Y`, reject if the hypothesis is not a chain graph, and search all pairs for a disagreement. -/
noncomputable def recognizeChain (s : Search (V × V)) (pick : Finset V → Finset V → Option (V × V))
    (G : SimpleGraph V) [DecidableRel G.Adj] : Bool :=
  match s (allPairs V) (pairFn G) with
  | none => true
  | some e =>
    let d := discover G s e.2
    if Disjoint d.1 d.2 then
      let H := tableGraph (learn s s pick (adjM G) (d.1.card + d.2.card) d.1 d.2)
      (open Classical in decide (IsChain H)) && (s (allPairs V) fun e => pairFn H e != pairFn G e).isNone
    else false

/-- The empty graph is a chain graph. -/
private theorem isChain_of_no_edges {G : SimpleGraph V} (h : ∀ u v, ¬ G.Adj u v) : IsChain G :=
  ⟨fun _ => false, fun u v huv => absurd huv (h u v), fun u _ _ _ => Or.inl fun t ht => absurd ht (h u t)⟩

/-- **Theorem 4, the logic.** With a correct search, the recognizer accepts exactly the chain graphs. -/
theorem recognizeChain_iff {s : Search (V × V)} (hs : SearchSpec s) {pick : Finset V → Finset V → Option (V × V)}
    (hp : PickSpec pick) (G : SimpleGraph V) [DecidableRel G.Adj] :
    recognizeChain s pick G = true ↔ IsChain G := by
  have hedge := hs (allPairs V) (pairFn G)
  unfold recognizeChain
  cases he : s (allPairs V) (pairFn G) with
  | none =>
    simp only [true_iff]
    refine isChain_of_no_edges fun u v huv => ?_
    have := hedge.2 he (u, v) (by simpa [allPairs] using huv.ne)
    simp [pairFn, huv] at this
  | some e =>
    obtain ⟨_, hef⟩ := hedge.1 e he
    have hxy : G.Adj e.1 e.2 := by simpa [pairFn] using hef
    simp only
    constructor
    · intro h
      split_ifs at h with hd
      simp only [Bool.and_eq_true, decide_eq_true_eq, Option.isNone_iff_eq_none] at h
      obtain ⟨h1, h2⟩ := h
      set H := tableGraph (learn s s pick (adjM G) ((discover G s e.2).1.card + (discover G s e.2).2.card)
        (discover G s e.2).1 (discover G s e.2).2)
      have hag : ∀ e ∈ allPairs V, pairFn H e = pairFn G e := by
        intro e he
        have := (hs (allPairs V) fun e => pairFn H e != pairFn G e).2 h2 e he
        simpa using this
      have : H = G := by
        ext u v
        by_cases huv : u = v
        · subst huv
          simp
        · have := hag (u, v) (by simp [allPairs, huv])
          simpa [pairFn] using this
      exact this ▸ h1
    · rintro ⟨side, hb, hc⟩
      obtain ⟨hX, hY⟩ := discover_correct hs hb hc hxy
      have hne : side e.1 ≠ side e.2 := hb _ _ hxy
      have hdis : Disjoint (discover G s e.2).1 (discover G s e.2).2 := by
        rw [hX, hY]
        refine disjoint_left.2 fun v h1 h2 => ?_
        exact hne ((mem_sideVerts.1 h1).1.symm.trans (mem_sideVerts.1 h2).1)
      rw [if_pos hdis]
      have hN : NestedOn (adjM G) (discover G s e.2).1 (discover G s e.2).2 := by
        intro r hr r' hr'
        rw [hX] at hr hr'
        have hsame : side r = side r' := (mem_sideVerts.1 hr).1.trans (mem_sideVerts.1 hr').1.symm
        rcases comparable_same hb hc hsame with g | g
        · exact Or.inl fun c _ h => adjM_eq_true.2 (g c (adjM_eq_true.1 h))
        · exact Or.inr fun c _ h => adjM_eq_true.2 (g c (adjM_eq_true.1 h))
      rw [learn_correct hs hs hp _ _ _ _ hN le_rfl]
      have hHG : tableGraph (graphOn (adjM G) (discover G s e.2).1 (discover G s e.2).2) = G := by
        ext u v
        rw [tableGraph, SimpleGraph.fromRel_adj]
        simp only [mem_graphOn, adjM_eq_true]
        constructor
        · rintro ⟨_, ⟨_, _, h⟩ | ⟨_, _, h⟩⟩
          · exact h
          · exact h.symm
        · intro huv
          refine ⟨huv.ne, ?_⟩
          rw [hX, hY]
          have hsuv := hb u v huv
          have hmemS : ∀ a b : V, G.Adj a b → ∀ w, side a = side w → a ∈ sideVerts G side (side w) :=
            fun a b hab w h => mem_sideVerts.2 ⟨h, b, hab⟩
          by_cases hu : side u = side e.1
          · have hv : side v = side e.2 := by
              cases h1 : side u <;> cases h2 : side v <;> cases h3 : side e.1 <;> cases h4 : side e.2 <;> simp_all
            exact Or.inl ⟨hmemS u v huv _ hu, hmemS v u huv.symm _ hv, huv⟩
          · have hv : side v = side e.1 := by
              cases h1 : side u <;> cases h2 : side v <;> cases h3 : side e.1 <;> cases h4 : side e.2 <;> simp_all
            have hu' : side u = side e.2 := by
              cases h1 : side u <;> cases h3 : side e.1 <;> cases h4 : side e.2 <;> simp_all
            exact Or.inr ⟨hmemS v u huv.symm _ hv, hmemS u v huv _ hu', huv.symm⟩
      simp only [Bool.and_eq_true, decide_eq_true_eq, Option.isNone_iff_eq_none, hHG]
      refine ⟨⟨side, hb, hc⟩, ?_⟩
      cases he' : s (allPairs V) (fun e => pairFn G e != pairFn G e) with
      | none => rfl
      | some a =>
        obtain ⟨_, h2⟩ := (hs (allPairs V) fun e => pairFn G e != pairFn G e).1 a he'
        simp at h2

end GraphClasses
