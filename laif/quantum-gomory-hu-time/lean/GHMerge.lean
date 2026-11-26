import Mathlib

/-!
# Merging a terminal-free node of a weighted tree into its heaviest neighbour

Let `T` be a tree on a type `N` with edge weights `w : Sym2 N → ℕ`, let `y` be a node and let `z` be a
neighbour of `y` such that the edge `yz` is a heaviest edge at `y`. The merged tree lives on the nodes
other than `y`: node `y` is identified with `z` by `proj`, the edge `yz` disappears, and every other edge
`ab` of `T` becomes the edge between `proj a` and `proj b`, with the same weight.

* `thr G w k`: the edges of `G` of weight at least `k`.
* `path_thr`: in an acyclic graph, all edges of the path from `u` to `v` weigh at least `k` exactly
  when `u` reaches `v` through edges of weight at least `k`. So the minimum weight on a tree path is the
  largest such `k`.
* `merge_isTree`: the merged graph is a tree.
* `mergeW_eq`: every edge of the merged tree has the weight of its edge in `T`.
* `path_min_iff`: for nodes `u, v ≠ y`, every `k`, the path from `u` to `v` in `T` and the path from
  `proj u` to `proj v` in the merged tree, all edges of the first weigh at least `k` exactly when all
  edges of the second do. Hence the two paths have the same minimum weight.
* `side_iff`: for an edge `ab ≠ yz` of `T`, two nodes are on the same side of `ab` in `T` exactly when
  their images are on the same side of the merged edge. So every remaining edge splits the nodes as
  before, with `y` on the side of `z`.
* `hyps_hold`, `heaviest_needed`: on the path `0 - 1 - 2` with weights `3` and `5`, merging `1` into
  `2` satisfies all hypotheses; merging `1` into `0` along the lighter edge breaks the conclusion of
  `thr_reach_iff` for the nodes `0` and `2` at `k = 5`.
-/

namespace GHMerge

open SimpleGraph

variable {N : Type*} [DecidableEq N]

/-- The edges of `G` of weight at least `k`. -/
def thr (G : SimpleGraph N) (w : Sym2 N → ℕ) (k : ℕ) : SimpleGraph N where
  Adj a b := G.Adj a b ∧ k ≤ w s(a, b)
  symm := ⟨fun a b h => ⟨h.1.symm, by rw [Sym2.eq_swap]; exact h.2⟩⟩
  loopless := ⟨fun _ h => h.1.ne rfl⟩

omit [DecidableEq N] in
@[simp] theorem thr_adj {G : SimpleGraph N} {w : Sym2 N → ℕ} {k : ℕ} {a b : N} :
    (thr G w k).Adj a b ↔ G.Adj a b ∧ k ≤ w s(a, b) := Iff.rfl

omit [DecidableEq N] in
theorem thr_le (G : SimpleGraph N) (w : Sym2 N → ℕ) (k : ℕ) : thr G w k ≤ G := fun _ _ h => h.1

theorem mem_edgeSet_thr {G : SimpleGraph N} {w : Sym2 N → ℕ} {k : ℕ} {e : Sym2 N} :
    e ∈ (thr G w k).edgeSet ↔ e ∈ G.edgeSet ∧ k ≤ w e := by
  cases e with
  | h a b => simp

/-- In an acyclic graph, all edges of a path weigh at least `k` exactly when its ends are joined by
edges of weight at least `k`. -/
theorem path_thr {G : SimpleGraph N} (hG : G.IsAcyclic) (w : Sym2 N → ℕ) (k : ℕ) {u v : N}
    (p : G.Walk u v) (hp : p.IsPath) :
    (∀ e ∈ p.edges, k ≤ w e) ↔ (thr G w k).Reachable u v := by
  constructor
  · intro h
    exact ⟨p.transfer (thr G w k) fun e he =>
      mem_edgeSet_thr.2 ⟨p.edges_subset_edgeSet he, h e he⟩⟩
  · rintro ⟨q⟩
    have hq : (q.bypass.mapLe (thr_le G w k)).IsPath := q.bypass_isPath.mapLe _
    have h := (hG.subsingleton_path u v).elim ⟨p, hp⟩ ⟨_, hq⟩
    have hpq : p = q.bypass.mapLe (thr_le G w k) := congrArg Subtype.val h
    intro e he
    rw [hpq, Walk.edges_mapLe_eq_edges] at he
    exact (mem_edgeSet_thr.1 (q.bypass.edges_subset_edgeSet he)).2

omit [DecidableEq N] in
/-- An acyclic graph has no triangle. -/
theorem no_triangle {G : SimpleGraph N} (hG : G.IsAcyclic) {a b c : N} (hab : G.Adj a b)
    (hbc : G.Adj b c) (hca : G.Adj c a) : False := by
  have hp1 : (Walk.cons hab (Walk.cons hbc Walk.nil)).IsPath := by
    simp [Walk.cons_isPath_iff, hab.ne, hbc.ne, hca.ne.symm]
  have hp2 : (Walk.cons hca.symm Walk.nil).IsPath := by
    simp [Walk.cons_isPath_iff, hca.ne.symm]
  have h := (hG.subsingleton_path a c).elim ⟨_, hp1⟩ ⟨_, hp2⟩
  have h' := congrArg (fun p : G.Path a c => p.1.length) h
  simp at h'

/-- The node of the merged tree that `x` goes to: `y` goes to `z`, every other node stays. -/
def proj (y z : N) (hz : z ≠ y) (x : N) : {x : N // x ≠ y} :=
  if h : x = y then ⟨z, hz⟩ else ⟨x, h⟩

section Merge

variable {y z : N} (hz : z ≠ y)

theorem proj_self : proj y z hz y = ⟨z, hz⟩ := by simp [proj]

theorem proj_of_ne {x : N} (hx : x ≠ y) : proj y z hz x = ⟨x, hx⟩ := by simp [proj, hx]

theorem proj_z : proj y z hz z = ⟨z, hz⟩ := proj_of_ne hz hz

theorem proj_val (p : {x : N // x ≠ y}) : proj y z hz p.1 = p := proj_of_ne hz p.2

theorem proj_eq_iff {a c : N} :
    proj y z hz a = proj y z hz c ↔ a = c ∨ (a = y ∧ c = z) ∨ (a = z ∧ c = y) := by
  by_cases ha : a = y <;> by_cases hc : c = y
  · subst ha hc; simp
  · subst ha
    rw [proj_self, proj_of_ne hz hc, Subtype.mk.injEq]
    constructor
    · intro h; exact Or.inr (Or.inl ⟨rfl, h.symm⟩)
    · rintro (h | ⟨-, h⟩ | ⟨h, -⟩)
      · exact absurd h.symm hc
      · exact h.symm
      · exact absurd h.symm hz
  · subst hc
    rw [proj_self, proj_of_ne hz ha, Subtype.mk.injEq]
    constructor
    · intro h; exact Or.inr (Or.inr ⟨h, rfl⟩)
    · rintro (h | ⟨h, -⟩ | ⟨h, -⟩)
      · exact absurd h ha
      · exact absurd h ha
      · exact h
  · rw [proj_of_ne hz ha, proj_of_ne hz hc, Subtype.mk.injEq]
    constructor
    · intro h; exact Or.inl h
    · rintro (h | ⟨h, -⟩ | ⟨-, h⟩)
      · exact h
      · exact absurd h ha
      · exact absurd h hc

theorem proj_eq_of_pair {c d : N} (h : s(c, d) = s(y, z)) : proj y z hz c = proj y z hz d := by
  rw [Sym2.eq_iff] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rw [proj_self, proj_z]
  · rw [proj_self, proj_z]

variable (T : SimpleGraph N) (w : Sym2 N → ℕ)

/-- The merged graph on the nodes other than `y`. -/
def merge : SimpleGraph {x : N // x ≠ y} where
  Adj p q := p ≠ q ∧ ∃ a b, T.Adj a b ∧ proj y z hz a = p ∧ proj y z hz b = q
  symm := ⟨fun _ _ ⟨h, a, b, hab, ha, hb⟩ => ⟨h.symm, b, a, hab.symm, hb, ha⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

/-- The weight of an edge of the merged graph: the largest weight of an edge of `T` that maps to it.
By `mergeW_eq` this is the weight of its unique edge in `T` when `T` is acyclic. -/
noncomputable def mergeW [Fintype N] (e : Sym2 {x : N // x ≠ y}) : ℕ := by
  classical
  exact ((Finset.univ : Finset (Sym2 N)).filter
    (fun f => f ∈ T.edgeSet ∧ f.map (proj y z hz) = e)).sup w

/-- `yz` is a heaviest edge at `y`. -/
def Heaviest (y z : N) : Prop := ∀ a, T.Adj y a → w s(y, a) ≤ w s(y, z)

theorem le_mergeW_iff [Fintype N] {k : ℕ} (hk : 0 < k) (e : Sym2 {x : N // x ≠ y}) :
    k ≤ mergeW hz T w e ↔ ∃ f, f ∈ T.edgeSet ∧ f.map (proj y z hz) = e ∧ k ≤ w f := by
  classical
  unfold mergeW
  rw [Finset.le_sup_iff hk]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨f, ⟨h1, h2⟩, h3⟩; exact ⟨f, h1, h2, h3⟩
  · rintro ⟨f, h1, h2, h3⟩; exact ⟨f, ⟨h1, h2⟩, h3⟩

theorem thr_merge_adj [Fintype N] {k : ℕ} {p q : {x : N // x ≠ y}} :
    (thr (merge hz T) (mergeW hz T w) k).Adj p q ↔
      p ≠ q ∧ ∃ a b, T.Adj a b ∧ k ≤ w s(a, b) ∧ proj y z hz a = p ∧ proj y z hz b = q := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp only [thr_adj, zero_le, and_true, true_and]
    exact Iff.rfl
  · rw [thr_adj, le_mergeW_iff hz T w hk]
    constructor
    · rintro ⟨⟨hpq, -⟩, f, hf, hfe, hkf⟩
      cases f with
      | h a b =>
        rw [Sym2.map_mk, Sym2.eq_iff] at hfe
        rcases hfe with ⟨ha, hb⟩ | ⟨ha, hb⟩
        · exact ⟨hpq, a, b, hf, hkf, ha, hb⟩
        · exact ⟨hpq, b, a, (T.mem_edgeSet.1 hf).symm, by rwa [Sym2.eq_swap], hb, ha⟩
    · rintro ⟨hpq, a, b, hab, hk', ha, hb⟩
      exact ⟨⟨hpq, a, b, hab, ha, hb⟩, s(a, b), hab, by simp [ha, hb], hk'⟩

/-! ### Thresholds -/

theorem map_thr [Fintype N] {k : ℕ} {a b : N} (h : (thr T w k).Reachable a b) :
    (thr (merge hz T) (mergeW hz T w) k).Reachable (proj y z hz a) (proj y z hz b) := by
  obtain ⟨P⟩ := h
  induction P with
  | nil => exact Reachable.refl _
  | @cons c d e hcd _ ih =>
    refine Reachable.trans ?_ ih
    by_cases heq : proj y z hz c = proj y z hz d
    · rw [heq]
    · exact Adj.reachable ((thr_merge_adj hz T w).2 ⟨heq, c, d, hcd.1, hcd.2, rfl, rfl⟩)

theorem rep_thr (hyz : T.Adj y z) (hH : Heaviest T w y z) {k : ℕ} {a b : N} (hab : T.Adj a b)
    (hk : k ≤ w s(a, b)) : (thr T w k).Reachable (proj y z hz a).1 a := by
  by_cases ha : a = y
  · subst ha
    rw [proj_self]
    refine Adj.reachable ⟨hyz.symm, ?_⟩
    rw [Sym2.eq_swap]
    exact hk.trans (hH b hab)
  · rw [proj_of_ne hz ha]

theorem lift_thr [Fintype N] (hyz : T.Adj y z) (hH : Heaviest T w y z) {k : ℕ}
    {p q : {x : N // x ≠ y}} (h : (thr (merge hz T) (mergeW hz T w) k).Reachable p q) :
    (thr T w k).Reachable p.1 q.1 := by
  obtain ⟨P⟩ := h
  induction P with
  | nil => exact Reachable.refl _
  | @cons p p' q h _ ih =>
    obtain ⟨-, a, b, hab, hk, ha, hb⟩ := (thr_merge_adj hz T w).1 h
    refine Reachable.trans ?_ ih
    subst ha hb
    have h1 := rep_thr hz T w hyz hH hab hk
    have h2 := rep_thr hz T w hyz hH (k := k) hab.symm (by rw [Sym2.eq_swap]; exact hk)
    exact h1.trans ((Adj.reachable (show (thr T w k).Adj a b from ⟨hab, hk⟩)).trans h2.symm)

/-- Threshold connectivity between nodes other than `y` is the same before and after the merge. -/
theorem thr_reach_iff [Fintype N] (hyz : T.Adj y z) (hH : Heaviest T w y z) (k : ℕ) {u v : N}
    (hu : u ≠ y) (hv : v ≠ y) :
    (thr T w k).Reachable u v ↔
      (thr (merge hz T) (mergeW hz T w) k).Reachable (proj y z hz u) (proj y z hz v) := by
  refine ⟨map_thr hz T w, fun h => ?_⟩
  have := lift_thr hz T w hyz hH h
  rwa [proj_of_ne hz hu, proj_of_ne hz hv] at this

/-! ### Sides of an edge -/

theorem rep_del (hyz : T.Adj y z) {a b : N} (hab' : s(a, b) ≠ s(y, z)) (x : N) :
    (T.deleteEdges {s(a, b)}).Reachable (proj y z hz x).1 x := by
  by_cases hx : x = y
  · subst hx
    rw [proj_self]
    refine Adj.reachable ?_
    rw [deleteEdges_adj, Set.mem_singleton_iff, Sym2.eq_swap]
    exact ⟨hyz.symm, fun h => hab' h.symm⟩
  · rw [proj_of_ne hz hx]

theorem lift_del (hyz : T.Adj y z) {a b : N} (hab' : s(a, b) ≠ s(y, z)) {p q : {x : N // x ≠ y}}
    (h : ((merge hz T).deleteEdges {s(proj y z hz a, proj y z hz b)}).Reachable p q) :
    (T.deleteEdges {s(a, b)}).Reachable p.1 q.1 := by
  obtain ⟨P⟩ := h
  induction P with
  | nil => exact Reachable.refl _
  | @cons p p' q h _ ih =>
    rw [deleteEdges_adj, Set.mem_singleton_iff] at h
    obtain ⟨⟨-, c, d, hcd, hc, hd⟩, hne⟩ := h
    refine Reachable.trans ?_ ih
    subst hc hd
    have hcd' : s(c, d) ≠ s(a, b) := by
      intro he
      apply hne
      have := congrArg (Sym2.map (proj y z hz)) he
      simpa using this
    have h1 := rep_del hz T hyz hab' c
    have h2 := rep_del hz T hyz hab' d
    refine h1.trans ((Adj.reachable ?_).trans h2.symm)
    rw [deleteEdges_adj, Set.mem_singleton_iff]
    exact ⟨hcd, hcd'⟩

/-- In an acyclic graph, an edge of the merged graph comes from exactly one edge other than `yz`. -/
theorem preimage_unique (hT : T.IsAcyclic) (hyz : T.Adj y z) {a b c d : N} (hab : T.Adj a b)
    (hcd : T.Adj c d) (hab' : s(a, b) ≠ s(y, z)) (h : proj y z hz a = proj y z hz c)
    (h' : proj y z hz b = proj y z hz d) : s(a, b) = s(c, d) := by
  rw [proj_eq_iff] at h h'
  rcases h with h | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases h' with h' | ⟨h3, h4⟩ | ⟨h3, h4⟩
  · rw [h, h']
  · rw [h, h3] at hab; rw [h4] at hcd
    exact (no_triangle hT hab hyz hcd.symm).elim
  · rw [h, h3] at hab; rw [h4] at hcd
    exact (no_triangle hT hcd hyz hab.symm).elim
  · rw [h1, h'] at hab; rw [h2] at hcd
    exact (no_triangle hT hyz hcd hab.symm).elim
  · rw [h1, h3] at hab; exact (hab.ne rfl).elim
  · rw [h1, h3] at hab'; exact (hab' rfl).elim
  · rw [h1, h'] at hab; rw [h2] at hcd
    exact (no_triangle hT hyz hab hcd.symm).elim
  · rw [h1, h3, Sym2.eq_swap] at hab'; exact (hab' rfl).elim
  · rw [h1, h3] at hab; exact (hab.ne rfl).elim

theorem map_del (hT : T.IsAcyclic) (hyz : T.Adj y z) {a b : N} (hab : T.Adj a b) {x₁ x₂ : N} (h : (T.deleteEdges {s(a, b)}).Reachable x₁ x₂) :
    ((merge hz T).deleteEdges {s(proj y z hz a, proj y z hz b)}).Reachable
      (proj y z hz x₁) (proj y z hz x₂) := by
  obtain ⟨P⟩ := h
  induction P with
  | nil => exact Reachable.refl _
  | @cons c d e hcd _ ih =>
    refine Reachable.trans ?_ ih
    rw [deleteEdges_adj, Set.mem_singleton_iff] at hcd
    obtain ⟨hcd, hne⟩ := hcd
    by_cases heq : proj y z hz c = proj y z hz d
    · rw [heq]
    · refine Adj.reachable ?_
      rw [deleteEdges_adj, Set.mem_singleton_iff]
      refine ⟨⟨heq, c, d, hcd, rfl, rfl⟩, fun he => ?_⟩
      have hcd' : s(c, d) ≠ s(y, z) := fun h => heq (proj_eq_of_pair hz h)
      rw [Sym2.eq_iff] at he
      rcases he with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact hne (preimage_unique hz T hT hyz hcd hab hcd' h1 h2)
      · exact hne ((preimage_unique hz T hT hyz hcd hab.symm hcd' h1 h2).trans Sym2.eq_swap)

/-- Every remaining edge splits the nodes as before, with `y` on the side of `z`. -/
theorem side_iff (hT : T.IsAcyclic) (hyz : T.Adj y z) {a b : N} (hab : T.Adj a b)
    (hab' : s(a, b) ≠ s(y, z)) (x₁ x₂ : N) :
    (T.deleteEdges {s(a, b)}).Reachable x₁ x₂ ↔
      ((merge hz T).deleteEdges {s(proj y z hz a, proj y z hz b)}).Reachable
        (proj y z hz x₁) (proj y z hz x₂) := by
  refine ⟨map_del hz T hT hyz hab, fun h => ?_⟩
  exact (rep_del hz T hyz hab' x₁).symm.trans
    ((lift_del hz T hyz hab' h).trans (rep_del hz T hyz hab' x₂))

/-! ### The merged graph is a tree -/

theorem map_reach {a b : N} (h : T.Reachable a b) :
    (merge hz T).Reachable (proj y z hz a) (proj y z hz b) := by
  obtain ⟨P⟩ := h
  induction P with
  | nil => exact Reachable.refl _
  | @cons c d e hcd _ ih =>
    refine Reachable.trans ?_ ih
    by_cases heq : proj y z hz c = proj y z hz d
    · rw [heq]
    · exact Adj.reachable ⟨heq, c, d, hcd, rfl, rfl⟩

theorem merge_isTree (hT : T.IsTree) (hyz : T.Adj y z) : (merge hz T).IsTree := by
  have : Nonempty {x : N // x ≠ y} := ⟨⟨z, hz⟩⟩
  refine ⟨⟨fun p q => ?_⟩, ?_⟩
  · have := map_reach hz T (hT.connected.preconnected p.1 q.1)
    rwa [proj_val, proj_val] at this
  · rw [isAcyclic_iff_forall_adj_isBridge]
    rintro p q ⟨hne, a, b, hab, rfl, rfl⟩
    rw [isBridge_iff]
    intro hr
    have hab' : s(a, b) ≠ s(y, z) := fun h => hne (proj_eq_of_pair hz h)
    have h := (rep_del hz T hyz hab' a).symm.trans
      ((lift_del hz T hyz hab' hr).trans (rep_del hz T hyz hab' b))
    exact (isAcyclic_iff_forall_adj_isBridge.1 hT.isAcyclic hab) h

/-- An edge of the merged tree has the weight of its edge in `T`. -/
theorem mergeW_eq [Fintype N] (hT : T.IsAcyclic) (hyz : T.Adj y z) {a b : N} (hab : T.Adj a b)
    (hab' : s(a, b) ≠ s(y, z)) :
    mergeW hz T w s(proj y z hz a, proj y z hz b) = w s(a, b) := by
  classical
  apply le_antisymm
  · unfold mergeW
    apply Finset.sup_le
    intro f hf
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hf
    obtain ⟨hfE, hfm⟩ := hf
    cases f with
    | h c d =>
      rw [mem_edgeSet] at hfE
      rw [Sym2.map_mk, Sym2.eq_iff] at hfm
      rcases hfm with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [preimage_unique hz T hT hyz hab hfE hab' h1.symm h2.symm]
      · rw [preimage_unique hz T hT hyz hab hfE.symm hab' h2.symm h1.symm, Sym2.eq_swap]
  · unfold mergeW
    apply Finset.le_sup
    simp [hab]

/-- The path between two nodes other than `y` has the same minimum weight before and after the merge:
for every `k`, all its edges weigh at least `k` in `T` exactly when all edges of the merged path do. -/
theorem path_min_iff [Fintype N] (hT : T.IsTree) (hyz : T.Adj y z) (hH : Heaviest T w y z)
    {u v : N} (hu : u ≠ y) (hv : v ≠ y) (P : T.Walk u v) (hP : P.IsPath)
    (P' : (merge hz T).Walk (proj y z hz u) (proj y z hz v)) (hP' : P'.IsPath) (k : ℕ) :
    (∀ e ∈ P.edges, k ≤ w e) ↔ (∀ e ∈ P'.edges, k ≤ mergeW hz T w e) := by
  rw [path_thr hT.isAcyclic w k P hP,
    path_thr (merge_isTree hz T hT hyz).isAcyclic (mergeW hz T w) k P' hP']
  exact thr_reach_iff hz T w hyz hH k hu hv

end Merge

/-! ### Content of the hypotheses and of the conclusion -/

theorem hz0 : (0 : Fin 3) ≠ 1 := by decide

/-- Weights `3` and `5` on the path `0 - 1 - 2`. -/
def w3 (e : Sym2 (Fin 3)) : ℕ := if e = s(0, 1) then 3 else if e = s(1, 2) then 5 else 0

/-- Merging node `1` into `2` satisfies every hypothesis. -/
theorem hyps_hold : (pathGraph 3).IsTree ∧ (pathGraph 3).Adj 1 2 ∧ Heaviest (pathGraph 3) w3 1 2 := by
  refine ⟨isTree_pathGraph.2 (by norm_num), by simp [pathGraph_adj], ?_⟩
  intro a ha
  fin_cases a
  · decide
  · exact absurd ha (by simp)
  · decide

/-- Merging node `1` into `0` along the lighter edge breaks the conclusion of `thr_reach_iff`:
`0` and `2` are not joined by edges of weight at least `5` in the tree, but they are after this
merge. -/
theorem heaviest_needed :
    ¬ Heaviest (pathGraph 3) w3 1 0 ∧ ¬ (thr (pathGraph 3) w3 5).Reachable 0 2 ∧
      (thr (merge hz0 (pathGraph 3)) (mergeW hz0 (pathGraph 3) w3) 5).Reachable
        (proj 1 0 hz0 0) (proj 1 0 hz0 2) := by
  have h01 : (pathGraph 3).Adj 0 1 := by simp [pathGraph_adj]
  have h12 : (pathGraph 3).Adj 1 2 := by simp [pathGraph_adj]
  refine ⟨fun h => ?_, fun h => ?_, ?_⟩
  · have := h 2 h12
    revert this
    decide
  · have hp : (Walk.cons h01 (Walk.cons h12 Walk.nil)).IsPath := by
      simp [Walk.cons_isPath_iff]
    rw [← path_thr (isTree_pathGraph.2 (by norm_num)).isAcyclic w3 5 _ hp] at h
    have := h s(0, 1) (by simp)
    revert this
    decide
  · refine Adj.reachable ((thr_merge_adj _ _ _).2 ⟨?_, 1, 2, h12, by decide, ?_, rfl⟩)
    · rw [proj_of_ne hz0 hz0, proj_of_ne hz0 (by decide)]
      decide
    · rw [proj_self, proj_of_ne hz0 hz0]

end GHMerge
