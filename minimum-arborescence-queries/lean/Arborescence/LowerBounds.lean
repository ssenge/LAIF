import Arborescence.WeakDuality

/-!
# The reductions of Theorem 2

Exact statements about the instances of section 5 of the README, with no query model:

* `exists_arb_iff_connected`: the bidirected graph has an arborescence iff the undirected one is connected.
* `tree_to_arb`, `arb_to_tree`, `isMinArb_to_isMST`, `isMST_to_isMinArb`: minimum arborescences of bidirected
  symmetric weights are the minimum spanning trees, with equal costs. Trees are Mathlib's `SimpleGraph.IsTree`:
  a spanning tree of `G` is a `T : SimpleGraph V` with `T ≤ G` and `T.IsTree`.
* `or_iff_cost_lt`, `or_iff_ne_star`, `star_unique`: the classical family, where the minimum cost, and the output
  alone, decide the OR of the hidden bits.
* `hidden_isMinArb_iff`, `hidden_reveals`: the family "hidden parents".

The query lower bounds that these feed are cited (quant-ph/0401091, Theorems 23, 24, and the bounds for OR and for reading bits)
and do not appear here.
-/

set_option linter.unusedSectionVars false

open Finset

namespace Arborescence

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## Bidirected graphs and connectivity -/

/-- The bidirection of `G`, with weights from a symmetric cost on unordered pairs. -/
def bidirect (G : SimpleGraph V) [DecidableRel G.Adj] (c : Sym2 V → ℤ) (r : V) : Graph V :=
  ⟨fun u v => decide (G.Adj u v), fun u v => c s(u, v), r⟩

variable {G : SimpleGraph V} [DecidableRel G.Adj] {c : Sym2 V → ℤ} {r : V}

theorem reachable_of_iterate {T : SimpleGraph V} {p : V → V} (h : ∀ v, v ≠ r → T.Adj (p v) v) :
    ∀ (k : ℕ) (v : V), p^[k] v = r → T.Reachable v r := by
  intro k
  induction k with
  | zero =>
    intro v hv
    rw [Function.iterate_zero, id] at hv
    rw [hv]
  | succ k ih =>
    intro v hv
    by_cases hvr : v = r
    · rw [hvr]
    · rw [Function.iterate_succ_apply] at hv
      exact (ih (p v) hv).symm.trans (h v hvr).reachable |>.symm

theorem connected_of_reach {T : SimpleGraph V} {p : V → V} (h : ∀ v, v ≠ r → T.Adj (p v) v)
    (hr : ∀ v, ∃ k : ℕ, p^[k] v = r) : T.Connected := by
  haveI : Nonempty V := ⟨r⟩
  refine ⟨fun u v => ?_⟩
  obtain ⟨k, hk⟩ := hr u
  obtain ⟨l, hl⟩ := hr v
  exact (reachable_of_iterate h k u hk).trans (reachable_of_iterate h l v hl).symm

/-- In a connected graph, a vertex other than `r` has a neighbour closer to `r`. -/
theorem exists_parent {T : SimpleGraph V} (hT : T.Connected) {v : V} (hv : v ≠ r) :
    ∃ u, T.Adj u v ∧ T.dist u r + 1 = T.dist v r := by
  obtain ⟨w, hw⟩ := hT.exists_walk_length_eq_dist v r
  cases w with
  | nil => exact absurd rfl hv
  | @cons _ u _ h q =>
    refine ⟨u, h.symm, ?_⟩
    have h1 : T.dist u r ≤ q.length := SimpleGraph.dist_le q
    have h2 : T.dist v r ≤ T.dist v u + T.dist u r := hT.dist_triangle
    have h3 : T.dist v u ≤ 1 := by
      simpa using SimpleGraph.dist_le (SimpleGraph.Walk.cons h SimpleGraph.Walk.nil)
    simp only [SimpleGraph.Walk.length_cons] at hw
    omega

/-- The parent function towards `r` in a connected graph, from the distance to `r`. -/
noncomputable def distParent (T : SimpleGraph V) (hT : T.Connected) (r v : V) : V :=
  if hv : v = r then r else (exists_parent hT hv).choose

theorem distParent_root {T : SimpleGraph V} (hT : T.Connected) : distParent T hT r r = r := by
  simp [distParent]

theorem distParent_spec {T : SimpleGraph V} (hT : T.Connected) {v : V} (hv : v ≠ r) :
    T.Adj (distParent T hT r v) v ∧ T.dist (distParent T hT r v) r + 1 = T.dist v r := by
  simp only [distParent, hv, dite_false]
  exact (exists_parent hT hv).choose_spec

theorem distParent_reach {T : SimpleGraph V} (hT : T.Connected) (v : V) :
    ∃ k : ℕ, (distParent T hT r)^[k] v = r := by
  induction hd : T.dist v r generalizing v with
  | zero => exact ⟨0, (hT.dist_eq_zero_iff.mp hd)⟩
  | succ n ih =>
    have hv : v ≠ r := by
      rintro rfl
      simp at hd
    obtain ⟨k, hk⟩ := ih (distParent T hT r v) (by have := (distParent_spec hT hv).2; omega)
    exact ⟨k + 1, by rw [Function.iterate_succ_apply]; exact hk⟩

/-- **Reduction for connectivity.** The bidirected graph has an arborescence iff `G` is connected. -/
theorem exists_arb_iff_connected : (∃ p, IsArb (bidirect G c r) p) ↔ G.Connected := by
  constructor
  · rintro ⟨p, hp⟩
    exact connected_of_reach (p := p) (fun v hv => by simpa [bidirect] using hp.edge v hv) hp.reach
  · intro hG
    refine ⟨distParent G hG r, distParent_root hG, fun v hv => ?_, distParent_reach hG⟩
    simpa [bidirect] using (distParent_spec hG hv).1

/-! ## Minimum spanning trees -/

open Classical in
/-- The cost of a graph: the sum of `c` over its edges. -/
noncomputable def treeCost (c : Sym2 V → ℤ) (T : SimpleGraph V) : ℤ := ∑ e ∈ T.edgeFinset, c e

/-- `T` is a minimum spanning tree of `G`. -/
def IsMST (G : SimpleGraph V) (c : Sym2 V → ℤ) (T : SimpleGraph V) : Prop :=
  T ≤ G ∧ T.IsTree ∧ ∀ T' : SimpleGraph V, T' ≤ G → T'.IsTree → treeCost c T ≤ treeCost c T'

open Classical in
/-- If `v ↦ s(p v, v)` is injective on `V \ {r}` with image in the edges of a tree, the sum over the edges is
the sum over the vertices. -/
theorem sum_edges_eq_of_tree {T : SimpleGraph V} (hT : T.IsTree) {p : V → V}
    (hedge : ∀ v, v ≠ r → T.Adj (p v) v)
    (hinj : Set.InjOn (fun v => s(p v, v)) (↑(univ.erase r) : Set V)) (c : Sym2 V → ℤ) :
    treeCost c T = ∑ v ∈ univ.erase r, c s(p v, v) := by
  have hsub : (univ.erase r).image (fun v => s(p v, v)) ⊆ T.edgeFinset := by
    intro e he
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp he
    simpa using hedge v (Finset.mem_erase.mp hv).1
  have hcard : T.edgeFinset.card ≤ ((univ.erase r).image (fun v => s(p v, v))).card := by
    rw [Finset.card_image_of_injOn hinj, Finset.card_erase_of_mem (mem_univ r), Finset.card_univ]
    have := hT.card_edgeFinset
    omega
  have himg := Finset.eq_of_subset_of_card_le hsub hcard
  rw [treeCost, ← himg, Finset.sum_image hinj]

/-- A spanning tree gives an arborescence of the same cost. -/
theorem tree_to_arb {T : SimpleGraph V} (hTG : T ≤ G) (hT : T.IsTree) :
    ∃ p, IsArb (bidirect G c r) p ∧ cost (bidirect G c r) p = treeCost c T := by
  have hC := hT.1
  refine ⟨distParent T hC r, ⟨distParent_root hC, fun v hv => ?_, distParent_reach hC⟩, ?_⟩
  · simpa [bidirect] using hTG (distParent_spec hC hv).1
  · have hinj : Set.InjOn (fun v => s(distParent T hC r v, v)) (↑(univ.erase r) : Set V) := by
      intro v hv w hw hvw
      have hv' : v ≠ r := by simpa using hv
      have hw' : w ≠ r := by simpa using hw
      have h1 := (distParent_spec hC hv').2
      have h2 := (distParent_spec hC hw').2
      rcases Sym2.eq_iff.mp hvw with ⟨_, h⟩ | ⟨h3, h4⟩
      · exact h
      · rw [h3] at h1
        rw [← h4] at h2
        omega
    rw [sum_edges_eq_of_tree hT (fun v hv => (distParent_spec hC hv).1) hinj c]
    rfl

/-- The graph of the edges of a parent function. -/
def parentGraph (p : V → V) (r : V) : SimpleGraph V :=
  SimpleGraph.fromRel fun a b => b ≠ r ∧ a = p b

/-- An arborescence gives a spanning tree of the same cost. -/
theorem arb_to_tree {p : V → V} (hp : IsArb (bidirect G c r) p) :
    ∃ T, T ≤ G ∧ T.IsTree ∧ treeCost c T = cost (bidirect G c r) p := by
  have hroot : (bidirect G c r).root = r := rfl
  have hadj : ∀ v, v ≠ r → G.Adj (p v) v := fun v hv => by
    simpa [bidirect] using hp.edge v hv
  have hne : ∀ v, v ≠ r → p v ≠ v := fun v hv => (hadj v hv).ne
  have hreach : ∀ v, ∃ k : ℕ, p^[k] v = r := hp.reach
  set T := parentGraph p r with hTdef
  have hTadj : ∀ v, v ≠ r → T.Adj (p v) v := fun v hv => by
    rw [hTdef, parentGraph, SimpleGraph.fromRel_adj]
    exact ⟨hne v hv, Or.inl ⟨hv, rfl⟩⟩
  have hTG : T ≤ G := by
    intro a b hab
    rw [hTdef, parentGraph, SimpleGraph.fromRel_adj] at hab
    rcases hab.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h2]
      exact hadj b h1
    · rw [h2]
      exact (hadj a h1).symm
  have hconn : T.Connected := connected_of_reach hTadj hreach
  have hinj : Set.InjOn (fun v => s(p v, v)) (↑(univ.erase r) : Set V) := by
    intro v hv w hw hvw
    have hv' : v ≠ r := by simpa using hv
    have hw' : w ≠ r := by simpa using hw
    rcases Sym2.eq_iff.mp hvw with ⟨_, h⟩ | ⟨h3, h4⟩
    · exact h
    · by_contra hvwne
      obtain ⟨k, hk⟩ := hreach v
      have : ∀ j : ℕ, p^[j] v = v ∨ p^[j] v = w := by
        intro j
        induction j with
        | zero => exact Or.inl rfl
        | succ j ih =>
          rw [Function.iterate_succ_apply']
          rcases ih with ih | ih
          · rw [ih]
            exact Or.inr h3
          · rw [ih]
            exact Or.inl h4.symm
      rcases this k with h | h
      · exact hv' (h.symm.trans hk)
      · exact hw' (h.symm.trans hk)
  classical
  have himg : T.edgeFinset = (univ.erase r).image fun v => s(p v, v) := by
    ext e
    induction e with
    | _ a b =>
      simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet, Finset.mem_image, Finset.mem_erase,
        ne_eq, mem_univ, and_true]
      constructor
      · intro hab
        rw [hTdef, parentGraph, SimpleGraph.fromRel_adj] at hab
        rcases hab.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact ⟨b, h1, by rw [h2]⟩
        · exact ⟨a, h1, by rw [h2, Sym2.eq_swap]⟩
      · rintro ⟨v, hv, hve⟩
        have := hTadj v hv
        rw [← SimpleGraph.mem_edgeSet, ← hve] at *
        simpa using this
  have hcard : T.edgeFinset.card + 1 = Fintype.card V := by
    rw [himg, Finset.card_image_of_injOn hinj, Finset.card_erase_of_mem (mem_univ r), Finset.card_univ]
    have : 0 < Fintype.card V := Fintype.card_pos_iff.mpr ⟨r⟩
    omega
  have hTree : T.IsTree := by
    rw [SimpleGraph.isTree_iff_connected_and_card]
    refine ⟨hconn, ?_⟩
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, ← SimpleGraph.edgeFinset_card]
    convert hcard
  refine ⟨T, hTG, hTree, ?_⟩
  rw [sum_edges_eq_of_tree hTree hTadj hinj c]
  rfl

/-- **Reduction for MST, first direction.** A minimum arborescence of the bidirected graph yields a minimum
spanning tree of the same cost. -/
theorem isMinArb_to_isMST {p : V → V} (hp : IsMinArb (bidirect G c r) p) :
    ∃ T, IsMST G c T ∧ treeCost c T = cost (bidirect G c r) p := by
  obtain ⟨T, hTG, hT, hc⟩ := arb_to_tree hp.1
  refine ⟨T, ⟨hTG, hT, fun T' hT'G hT' => ?_⟩, hc⟩
  obtain ⟨q, hq, hqc⟩ := tree_to_arb (c := c) (r := r) hT'G hT'
  rw [hc, ← hqc]
  exact hp.2 q hq

/-- **Reduction for MST, second direction.** A minimum spanning tree yields a minimum arborescence of the same
cost. So the minimum costs are equal, whichever root is chosen. -/
theorem isMST_to_isMinArb {T : SimpleGraph V} (hT : IsMST G c T) :
    ∃ p, IsMinArb (bidirect G c r) p ∧ cost (bidirect G c r) p = treeCost c T := by
  obtain ⟨p, hp, hc⟩ := tree_to_arb (c := c) (r := r) hT.1 hT.2.1
  refine ⟨p, ⟨hp, fun q hq => ?_⟩, hc⟩
  obtain ⟨T', hT'G, hT', hc'⟩ := arb_to_tree hq
  rw [hc, ← hc']
  exact hT.2.2 T' hT'G hT'

/-! ## The classical family -/

/-- The family of the classical bound. Every non-root `v` has an edge from the root of weight `1`. The positions
`(u, v)` with `u, v ≠ r`, `u ≠ v`, and `present u v` are edges of weight `0` if `bit u v`, and `2` otherwise. The
matrix model is `present = true`. -/
def orGraph (r : V) (present bit : V → V → Bool) : Graph V where
  adj u v := decide (u ≠ v ∧ v ≠ r ∧ (u = r ∨ present u v = true))
  w u v := if u = r then 1 else if bit u v = true then 0 else 2
  root := r

/-- The OR of the hidden bits. -/
def hiddenOr (r : V) (present bit : V → V → Bool) : Prop :=
  ∃ u v, u ≠ r ∧ v ≠ r ∧ u ≠ v ∧ present u v = true ∧ bit u v = true

variable {present bit : V → V → Bool}

theorem star_isArb : IsArb (orGraph r present bit) (fun _ => r) := by
  refine ⟨rfl, fun v hv => ?_, fun v => ⟨1, rfl⟩⟩
  have hv' : v ≠ r := hv
  simp [orGraph, hv'.symm, hv']

theorem star_cost : cost (orGraph r present bit) (fun _ => r) = (Fintype.card V : ℤ) - 1 := by
  have h : (orGraph r present bit).root = r := rfl
  simp only [cost, h]
  have hpos : 1 ≤ Fintype.card V := Fintype.card_pos_iff.mpr ⟨r⟩
  simp [orGraph, Finset.card_erase_of_mem]
  omega

/-- The arborescence that uses one hidden edge and the star otherwise. -/
theorem or_witness {u v : V} (hu : u ≠ r) (hv : v ≠ r) (huv : u ≠ v) (hp : present u v = true)
    (hb : bit u v = true) :
    ∃ q, IsArb (orGraph r present bit) q ∧ cost (orGraph r present bit) q = (Fintype.card V : ℤ) - 2 := by
  have h : (orGraph r present bit).root = r := rfl
  let q : V → V := fun x => if x = v then u else r
  have hqv : q v = u := by simp [q]
  have hqo : ∀ x, x ≠ v → q x = r := fun x hx => by simp [q, hx]
  refine ⟨q, ⟨hqo _ hv.symm, fun x hx => ?_, fun x => ?_⟩, ?_⟩
  · have hx' : x ≠ r := hx
    by_cases hxv : x = v
    · subst hxv
      simp [orGraph, hqv, huv, hx', hp]
    · simp [orGraph, hqo x hxv, hx', hx'.symm]
  · by_cases hxv : x = v
    · subst hxv
      refine ⟨2, ?_⟩
      show q^[2] x = r
      simp [hqv, hqo u huv]
    · exact ⟨1, hqo x hxv⟩
  · simp only [cost, h]
    have hv' : v ∈ univ.erase r := by simp [hv]
    rw [← Finset.add_sum_erase _ _ hv']
    have h1 : (orGraph r present bit).w (q v) v = 0 := by simp [orGraph, hqv, hu, hb]
    have h2 : ∀ x ∈ (univ.erase r).erase v, (orGraph r present bit).w (q x) x = 1 := by
      intro x hx
      simp [orGraph, hqo x (Finset.mem_erase.mp hx).1]
    rw [h1, Finset.sum_congr rfl h2]
    have hc : ((univ.erase r).erase v).card + 2 = Fintype.card V := by
      rw [Finset.card_erase_of_mem hv', Finset.card_erase_of_mem (mem_univ r), Finset.card_univ]
      have : 2 ≤ Fintype.card V := Fintype.one_lt_card_iff.mpr ⟨v, r, hv⟩
      omega
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one, zero_add]
    have : ((((univ.erase r).erase v).card : ℕ) : ℤ) + 2 = (Fintype.card V : ℤ) := by exact_mod_cast hc
    omega

/-- If no hidden bit is set, a parent function other than the star costs at least `n`. -/
theorem cost_of_ne_star (hor : ¬ hiddenOr r present bit) {p : V → V} (hp : IsArb (orGraph r present bit) p)
    (hne : p ≠ fun _ => r) : (Fintype.card V : ℤ) ≤ cost (orGraph r present bit) p := by
  have h : (orGraph r present bit).root = r := rfl
  have hroot : p r = r := hp.root_fix
  obtain ⟨v, hv⟩ : ∃ v, p v ≠ r := by
    by_contra hcon
    push Not at hcon
    exact hne (funext hcon)
  have hvr : v ≠ r := fun hvr => hv (hvr ▸ hroot)
  have hedge : ∀ x, x ≠ r → p x ≠ x ∧ (p x = r ∨ present (p x) x = true) := fun x hx => by
    have := hp.edge x hx
    simp only [orGraph, decide_eq_true_eq] at this
    exact ⟨this.1, this.2.2⟩
  have hw1 : ∀ x ∈ univ.erase r, 1 ≤ (orGraph r present bit).w (p x) x := by
    intro x hx
    have hx' := (Finset.mem_erase.mp hx).1
    by_cases hpx : p x = r
    · simp [orGraph, hpx]
    · have hb : bit (p x) x ≠ true := fun hb => hor
        ⟨p x, x, hpx, hx', (hedge x hx').1, ((hedge x hx').2.resolve_left hpx), hb⟩
      simp [orGraph, hpx, hb]
  have hw2 : (orGraph r present bit).w (p v) v = 2 := by
    have hb : bit (p v) v ≠ true := fun hb => hor
      ⟨p v, v, hv, hvr, (hedge v hvr).1, ((hedge v hvr).2.resolve_left hv), hb⟩
    simp [orGraph, hv, hb]
  simp only [cost, h]
  have hv' : v ∈ univ.erase r := by simp [hvr]
  rw [← Finset.add_sum_erase _ _ hv', hw2]
  have h3 : ∑ x ∈ (univ.erase r).erase v, (1 : ℤ) ≤
      ∑ x ∈ (univ.erase r).erase v, (orGraph r present bit).w (p x) x :=
    Finset.sum_le_sum fun x hx => hw1 x (Finset.mem_of_mem_erase hx)
  have hc : ((univ.erase r).erase v).card + 2 = Fintype.card V := by
    rw [Finset.card_erase_of_mem hv', Finset.card_erase_of_mem (mem_univ r), Finset.card_univ]
    have : 2 ≤ Fintype.card V := Fintype.one_lt_card_iff.mpr ⟨v, r, hvr⟩
    omega
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one] at h3
  have : ((((univ.erase r).erase v).card : ℕ) : ℤ) + 2 = (Fintype.card V : ℤ) := by exact_mod_cast hc
  omega

/-- **The classical family, by cost.** The minimum cost is below `n - 1` exactly when a hidden bit is set. -/
theorem or_iff_cost_lt {p : V → V} (hp : IsMinArb (orGraph r present bit) p) :
    cost (orGraph r present bit) p < (Fintype.card V : ℤ) - 1 ↔ hiddenOr r present bit := by
  constructor
  · intro hlt
    by_contra hor
    have hstar := star_cost (r := r) (present := present) (bit := bit)
    by_cases hne : p = fun _ => r
    · rw [hne] at hlt
      omega
    · have := cost_of_ne_star hor hp.1 hne
      omega
  · rintro ⟨u, v, hu, hv, huv, hpres, hb⟩
    obtain ⟨q, hq, hc⟩ := or_witness hu hv huv hpres hb
    have := hp.2 q hq
    omega

/-- **The classical family, by the output alone.** An output is the star exactly when no hidden bit is set. -/
theorem or_iff_ne_star {p : V → V} (hp : IsMinArb (orGraph r present bit) p) :
    p ≠ (fun _ => r) ↔ hiddenOr r present bit := by
  have hstar := star_cost (r := r) (present := present) (bit := bit)
  constructor
  · intro hne
    by_contra hor
    have h1 := cost_of_ne_star hor hp.1 hne
    have h2 := hp.2 _ (star_isArb (r := r) (present := present) (bit := bit))
    omega
  · intro hor heq
    have := (or_iff_cost_lt hp).mpr hor
    rw [heq] at this
    omega

/-- If no hidden bit is set, the star is the unique minimum arborescence. -/
theorem star_unique (hor : ¬ hiddenOr r present bit) {p : V → V} :
    IsMinArb (orGraph r present bit) p ↔ p = fun _ => r := by
  constructor
  · intro hp
    by_contra hne
    exact hor ((or_iff_ne_star hp).mp hne)
  · rintro rfl
    refine ⟨star_isArb, fun q hq => ?_⟩
    rw [star_cost]
    by_cases hne : q = fun _ => r
    · rw [hne, star_cost]
    · have := cost_of_ne_star hor hq hne
      omega

/-! ## Hidden parents

The vertices are `Fin (n + 1)`, with root `0`. Vertex `i + 1` has a hidden parent, the root or the vertex `i`, by
the bit `b i`. The hidden edges have weight `0`, and all other edges, in an arbitrary edge set, have positive weight.
-/

/-- The hidden parent function. -/
def hiddenParent {n : ℕ} (b : Fin n → Bool) : Fin (n + 1) → Fin (n + 1) :=
  Fin.cases 0 fun i => if b i then 0 else i.castSucc

/-- The instance with hidden parents. `extra` is any further set of edges, of weight `W > 0`. -/
def hiddenGraph {n : ℕ} (b : Fin n → Bool) (extra : Fin (n + 1) → Fin (n + 1) → Bool) (W : ℤ) :
    Graph (Fin (n + 1)) where
  adj u v := extra u v || decide (v ≠ 0 ∧ u = hiddenParent b v)
  w u v := if v ≠ 0 ∧ u = hiddenParent b v then 0 else W
  root := 0

theorem hiddenParent_isArb {n : ℕ} (b : Fin n → Bool) (extra : Fin (n + 1) → Fin (n + 1) → Bool) (W : ℤ) :
    IsArb (hiddenGraph b extra W) (hiddenParent b) := by
  refine ⟨by simp [hiddenGraph, hiddenParent], fun v hv => ?_, fun v => ?_⟩
  · have hv' : v ≠ 0 := hv
    simp [hiddenGraph, hv']
  · induction v using Fin.induction with
    | zero => exact ⟨0, rfl⟩
    | succ i ih =>
      obtain ⟨k, hk⟩ := ih
      by_cases hbi : b i = true
      · exact ⟨1, by simp [hiddenParent, hbi, hiddenGraph]⟩
      · refine ⟨k + 1, ?_⟩
        rw [Function.iterate_succ_apply]
        simpa [hiddenParent, hbi] using hk

theorem hidden_cost {n : ℕ} (b : Fin n → Bool) (extra : Fin (n + 1) → Fin (n + 1) → Bool) (W : ℤ) :
    cost (hiddenGraph b extra W) (hiddenParent b) = 0 := by
  refine Finset.sum_eq_zero fun v hv => ?_
  have hv' : v ≠ 0 := (Finset.mem_erase.mp hv).1
  simp [hiddenGraph, hv']

/-- **Hidden parents.** For `W > 0`, the hidden parent function is the unique minimum arborescence. -/
theorem hidden_isMinArb_iff {n : ℕ} (b : Fin n → Bool) (extra : Fin (n + 1) → Fin (n + 1) → Bool) {W : ℤ}
    (hW : 0 < W) {p : Fin (n + 1) → Fin (n + 1)} :
    IsMinArb (hiddenGraph b extra W) p ↔ p = hiddenParent b := by
  have hnn : ∀ q : Fin (n + 1) → Fin (n + 1), ∀ v ∈ univ.erase (hiddenGraph b extra W).root,
      0 ≤ (hiddenGraph b extra W).w (q v) v := by
    intro q v _
    simp only [hiddenGraph]
    split_ifs <;> omega
  constructor
  · intro hp
    have h0 : cost (hiddenGraph b extra W) p ≤ 0 := by
      have := hp.2 _ (hiddenParent_isArb b extra W)
      rwa [hidden_cost] at this
    have hzero := (Finset.sum_eq_zero_iff_of_nonneg (hnn p)).mp (le_antisymm h0 (Finset.sum_nonneg (hnn p)))
    funext v
    by_cases hv : v = 0
    · subst hv
      have : p 0 = 0 := hp.1.root_fix
      simp [this, hiddenParent]
    · have := hzero v (by simp [hiddenGraph, hv])
      simp only [hiddenGraph] at this
      split_ifs at this with h
      · exact h.2
      · omega
  · rintro rfl
    refine ⟨hiddenParent_isArb b extra W, fun q _ => ?_⟩
    rw [hidden_cost]
    exact Finset.sum_nonneg (hnn q)

/-- The output reveals the bits `b i`, for `i ≠ 0`. -/
theorem hidden_reveals {n : ℕ} (b : Fin n → Bool) (i : Fin n) (hi : (i : ℕ) ≠ 0) :
    hiddenParent b i.succ = 0 ↔ b i = true := by
  by_cases hbi : b i = true
  · simp [hiddenParent, hbi]
  · have : i.castSucc ≠ 0 := by
      intro h
      apply hi
      simpa using congrArg Fin.val h
    simp [hiddenParent, hbi, this]

end Arborescence
