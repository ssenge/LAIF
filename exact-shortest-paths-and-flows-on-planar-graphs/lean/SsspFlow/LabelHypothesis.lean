import Mathlib.Basic.Real.ENatENNReal
import SsspFlow.Congest
import SsspFlow.Crossing
import SsspFlow.LemmaVChain

/-!
# The Label Hypothesis and the round bounds in the message model

Statements in the model of `SsspFlow.Congest`. An algorithm is fixed for given numbers `n`, `W`, `e`,
`D` before the network, it runs on the identifiers `Fin n`, and a round moves exactly `B` bits per
edge and direction. Bounds are stated with the scale `L = logScale n W e`, and polylogarithmic means
`C * L ^ c` with absolute constants. A message of `C * L ^ c` bits splits into `O(L ^ c)` messages of
`O(log n)` bits, so this is CONGEST up to polylogarithmic factors in the rounds. The field `out` of
`Cslib.Congest.Algorithm` is meant for decision problems and is not used; results are read from the
final states.

* `LabelWitness`, `LabelsOK`, `LabelHypothesis`: the hypothesis of the paper.
  The bags are named by numbers. `tree x` is a connected subgraph that joins the vertices of the bag
  `x`, and it need not be a tree: a breadth-first tree of it costs as many rounds as its diameter.
  Leaves carry labels like all other bags: a leaf has few vertices, and broadcasting its arcs over its
  subgraph gives exact values. Estimates are natural numbers without loss, since the floor of an
  estimate keeps both bounds. Lengths are not restricted to a polynomial range, as `L` contains
  `log W`.
* `queryC₂`, `lemmaV_chain₂`: Lemma V with the value `toH` held by the start of a path and the value
  `fromH` held by its end, as the labels provide them.
* `LabelWitness.query_bound`: the query computed from the labels is `(1 + 1/e)`-approximate.
* `labelsOK_oneBag`, `labelsOK_triNet`: every small network has labels. With `triNet_planar`, this
  shows that neither side of the hypothesis is empty.

## Stated assumptions

These are classical or published results, stated as propositions and not proved here.

* `RealizationBox`: planar realization of distance matrices with terminals in a given order, [10].
* `DistanceLabelBox`: `(1 + ε)`-approximate distance labels on planar digraphs, [1, Lemma 11].
* `FaceIdBox`: identifiers of faces, [9, Lemma 5.11], deterministically [18, Lemma 3.17].
* `EmbeddingBox`: a planar embedding, computed in `Õ(D)` rounds.
* `AggBox`: minima per key over low congestion subgraphs, by a convergecast and a broadcast.
* `SmoothingBox`: smooth estimates from an approximate oracle, [3, Thm 1.7, Alg. 3].
* `NegReduction`: negative weights from exact nonnegative SSSP with a factor `τ` in the rounds. The
  reduction of [6, Thm 2], with the term `√n + D` replaced by `Õ(D)` through [9, Cor. 4.6, Lemma 4.8]
  and with [6, Cor. 33] in repaired form, gives `τ = tauSubpoly C` for an absolute constant `C`.
  `notes/NEGATIVE.md` gives `τ = tauPolylog c`.

## Round bounds

`ExactSsspBound`, `NegSsspBound` and `MaxFlowBound` state the round bounds of the paper in this
model. They are definitions here, and this file does not assert them.
-/

set_option autoImplicit false

open scoped ENNReal
open Cslib.Congest

namespace SsspFlow

universe u v

namespace RHierarchy

variable {V : Type u} {ι : Type v} {adj : V → V → Prop}
variable (H : RHierarchy V ι adj) (φ : V → ℝ≥0∞) (toH fromH : ι → V → V → ℝ≥0∞)

/-- The query over the chain of `z`, with `toH` for the way to the hub and `fromH` for the way from
the hub. -/
noncomputable def queryC₂ (z : V) : ℝ≥0∞ :=
  ⨅ (x : ι) (_ : H.Chain z x) (h ∈ H.hub x), H.aggC φ toH x h + fromH x h z

/-- **Lemma V for labels along a chain**, with one value for each direction. -/
theorem lemmaV_chain₂ (w : V → V → ℝ≥0∞) (ε : ℝ≥0∞) (hε : ε ≠ ∞)
    (lo₁ : ∀ x a h, H.Chain a x → h ∈ H.hub x → dist adj w Set.univ a h ≤ toH x a h)
    (lo₂ : ∀ x h z, H.Chain z x → h ∈ H.hub x → dist adj w Set.univ h z ≤ fromH x h z)
    (hi₁ : ∀ x a h, H.Chain a x → h ∈ H.hub x →
      toH x a h ≤ (1 + ε) * distR adj w (H.arc x) a h)
    (hi₂ : ∀ x h z, H.Chain z x → h ∈ H.hub x →
      fromH x h z ≤ (1 + ε) * distR adj w (H.arc x) h z)
    (z : V) :
    dsrc adj w φ z ≤ H.queryC₂ φ toH fromH z ∧ H.queryC₂ φ toH fromH z ≤ (1 + ε) * dsrc adj w φ z := by
  constructor
  · simp only [queryC₂, aggC, ENNReal.iInf_add, le_iInf_iff]
    intro x hz h hh a ha
    calc dsrc adj w φ z ≤ φ a + dist adj w Set.univ a z := iInf_le (fun a => _ + _) a
      _ ≤ φ a + (dist adj w Set.univ a h + dist adj w Set.univ h z) := by
          gcongr; exact dist_triangle w _ a h z
      _ ≤ φ a + toH x a h + fromH x h z := by
          rw [add_assoc]; gcongr
          · exact lo₁ x a h ha hh
          · exact lo₂ x h z hz hh
  · have hc0 : (1 + ε) ≠ 0 := (lt_of_lt_of_le one_pos le_self_add).ne'
    have hcT : (1 + ε) ≠ ∞ := ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top, hε⟩
    simp only [dsrc, dist, ENNReal.add_iInf, ENNReal.mul_iInf_of_ne hc0 hcT, le_iInf_iff]
    intro a p _
    obtain ⟨y, h, hh, ha, hz, p₁, p₂, h₁, h₂, hw⟩ :=
      H.descendChain w H.root p (Walk.arcsIn_of_adj H.root_arc p) Chain.root Chain.root
    calc H.queryC₂ φ toH fromH z ≤ H.aggC φ toH y h + fromH y h z :=
          (iInf₂_le y hz).trans (iInf₂_le h hh)
      _ ≤ φ a + toH y a h + fromH y h z := by gcongr; exact iInf₂_le a ha
      _ ≤ φ a + (1 + ε) * p₁.wt w + (1 + ε) * p₂.wt w := by
          gcongr
          · exact (hi₁ y a h ha hh).trans (by gcongr; exact iInf₂_le p₁ h₁)
          · exact (hi₂ y h z hz hh).trans (by gcongr; exact iInf₂_le p₂ h₂)
      _ ≤ (1 + ε) * (φ a + p.wt w) := by
          rw [← hw, mul_add, mul_add, add_assoc]
          gcongr
          exact le_mul_of_one_le_left (by simp) le_self_add

end RHierarchy

namespace Congest

/-- The scale of a problem with `n` nodes, lengths up to `W` and accuracy `1/e`. -/
def logScale (n W e : ℕ) : ℕ := Nat.log 2 (n + W + e) + 1

/-- Natural lengths as lengths in `[0, ∞]`. -/
def lenOf {V : Type} (ℓ : V → V → ℕ) : V → V → ℝ≥0∞ := fun a b => (ℓ a b : ℝ≥0∞)

/-- Lengths in `ℕ∞` as lengths in `[0, ∞]`. -/
def lenTop {V : Type} (ℓ : V → V → ℕ∞) : V → V → ℝ≥0∞ := fun a b => (ℓ a b : ℝ≥0∞)

/-- Offsets in `ℕ∞` as offsets in `[0, ∞]`. -/
def offTop {V : Type} (φ : V → ℕ∞) : V → ℝ≥0∞ := fun a => (φ a : ℝ≥0∞)

/-! ### The Label Hypothesis -/

/-- The input of a node: its neighbours in rotation order and the lengths of its arcs. -/
structure LocalIn (V : Type) where
  /-- The neighbours in rotation order. -/
  nbrs : List V
  /-- The length of the arc to a neighbour; `0` for other nodes. -/
  lenOut : V → ℕ
  /-- The length of the arc from a neighbour; `0` for other nodes. -/
  lenIn : V → ℕ

/-- One hub in the record of a node: the two estimates between the node and the hub. -/
structure HubEntry (V : Type) where
  /-- The hub. -/
  hub : V
  /-- The estimate from the node to the hub. -/
  toHub : ℕ∞
  /-- The estimate from the hub to the node. -/
  fromHub : ℕ∞

/-- One bag on the chain of a node, with its hubs. -/
structure BagEntry (V : Type) where
  /-- The name of the bag. -/
  bag : ℕ
  /-- The hubs of the bag, with estimates. -/
  hubs : List (HubEntry V)

/-- The output of a node. -/
structure LabelOut (V : Type) where
  /-- The bags of the chain of the node. -/
  chain : List (BagEntry V)
  /-- For a neighbour, the bags whose subgraph contains the edge to it. -/
  treeBags : V → List ℕ

section Labels

variable {V : Type} [Fintype V] [DecidableEq V]

/-- The input of the nodes of a network with lengths `ℓ`. -/
def Net.localIn (N : Net V) (ℓ : V → V → ℕ) (v : V) : LocalIn V where
  nbrs := N.rotList v
  lenOut u := if N.G.Adj v u then ℓ v u else 0
  lenIn u := if N.G.Adj v u then ℓ u v else 0

/-- The labels `out` are correct for the network `N`, the lengths `ℓ` and the accuracy `1/e`, with
height `h`, subgraph diameter and hub number `s`, and words of `w` bits. -/
structure LabelWitness (N : Net V) (ℓ : V → V → ℕ) (e h s w : ℕ) (out : V → LabelOut V) where
  /-- The bags. Unused names have empty bags. (V1) to (V3) are the fields of `RHierarchy`. -/
  H : RHierarchy V ℕ N.G.Adj
  /-- The subgraph of a bag. -/
  tree : ℕ → V → V → Prop
  /-- The depth of a bag. -/
  depth : ℕ → ℕ
  depth_kid : ∀ c x, H.kid c x → depth c = depth x + 1
  height : ∀ x, depth x ≤ h
  tree_adj : ∀ x a b, tree x a b → N.G.Adj a b
  tree_symm : ∀ x a b, tree x a b → tree x b a
  /-- The subgraph of a bag joins its vertices by walks with at most `s` arcs. -/
  tree_span : ∀ x a b, a ∈ H.bag x → b ∈ H.bag x →
    ∃ p : Walk (tree x) a b, p.support.length ≤ s + 1
  /-- For every depth, every edge lies in at most two of the subgraphs. -/
  congestion : ∀ d a b, ∃ F : Finset ℕ, F.card ≤ 2 ∧ ∀ x, depth x = d → tree x a b → x ∈ F
  /-- A bag has at most `s` hubs. For a leaf, all its vertices are hubs. -/
  hub_card : ∀ x, (H.hub x).ncard ≤ s
  /-- Every node knows the bags of its chain. -/
  chain_iff : ∀ v x, H.Chain v x ↔ ∃ E ∈ (out v).chain, E.bag = x
  /-- Every node knows the hubs of the bags of its chain. -/
  hubs_iff : ∀ v, ∀ E ∈ (out v).chain, ∀ y, y ∈ H.hub E.bag ↔ ∃ F ∈ E.hubs, F.hub = y
  /-- Every node knows the bags whose subgraph contains an edge at it. -/
  tree_know : ∀ v u, N.G.Adj v u → ∀ x, x ∈ (out v).treeBags u ↔ tree x v u
  /-- (L2), the way to the hub, lower bound. -/
  to_lo : ∀ v, ∀ E ∈ (out v).chain, ∀ F ∈ E.hubs,
    dist N.G.Adj (lenOf ℓ) Set.univ v F.hub ≤ (F.toHub : ℝ≥0∞)
  /-- (L2), the way to the hub, upper bound. -/
  to_hi : ∀ v, ∀ E ∈ (out v).chain, ∀ F ∈ E.hubs,
    (F.toHub : ℝ≥0∞) ≤ (1 + (e : ℝ≥0∞)⁻¹) * distR N.G.Adj (lenOf ℓ) (H.arc E.bag) v F.hub
  /-- (L2), the way from the hub, lower bound. -/
  from_lo : ∀ v, ∀ E ∈ (out v).chain, ∀ F ∈ E.hubs,
    dist N.G.Adj (lenOf ℓ) Set.univ F.hub v ≤ (F.fromHub : ℝ≥0∞)
  /-- (L2), the way from the hub, upper bound. -/
  from_hi : ∀ v, ∀ E ∈ (out v).chain, ∀ F ∈ E.hubs,
    (F.fromHub : ℝ≥0∞) ≤ (1 + (e : ℝ≥0∞)⁻¹) * distR N.G.Adj (lenOf ℓ) (H.arc E.bag) F.hub v
  /-- Names of bags have `w` bits. -/
  name_lt : ∀ v, ∀ E ∈ (out v).chain, E.bag < 2 ^ w
  /-- Names of bags have `w` bits. -/
  treeBags_lt : ∀ v u, ∀ x ∈ (out v).treeBags u, x < 2 ^ w
  /-- Finite estimates have `w` bits. -/
  value_lt : ∀ v, ∀ E ∈ (out v).chain, ∀ F ∈ E.hubs,
    (F.toHub = ⊤ ∨ F.toHub < (2 ^ w : ℕ)) ∧ (F.fromHub = ⊤ ∨ F.fromHub < (2 ^ w : ℕ))

/-- The labels `out` are correct. -/
def LabelsOK (N : Net V) (ℓ : V → V → ℕ) (e h s w : ℕ) (out : V → LabelOut V) : Prop :=
  Nonempty (LabelWitness N ℓ e h s w out)

end Labels

/-- **The Label Hypothesis.** For given `n`, `W`, `e`, `D`, one algorithm computes on every planar
network with `n` nodes, diameter at most `D` and arc lengths in `[1, W]` labels with accuracy `1/e`,
in `Õ(D e)` rounds, with height `O(L)`, subgraph diameter and hub number `Õ(D)`, and words of `O(L)`
bits. -/
def LabelHypothesis : Prop :=
  ∃ C c : ℕ, ∀ n W e D : ℕ, 1 ≤ W → 1 ≤ e → 1 ≤ D →
    ∃ (σ : Type) (A : Algorithm (Fin n) (LocalIn (Fin n)) σ (C * logScale n W e ^ c))
      (out : Fin n → σ → LabelOut (Fin n)),
      ∀ (N : Net (Fin n)) (ℓ : Fin n → Fin n → ℕ), N.toRot.Planar → N.DiamLE D → N.LensIn ℓ W →
        LabelsOK N ℓ e (C * logScale n W e) (C * logScale n W e ^ c * D) (C * logScale n W e)
          (fun v => out v (A.run N.G (N.localIn ℓ) (C * logScale n W e ^ c * D * e) v))

section Query

variable {V : Type} [Fintype V] [DecidableEq V]

/-- The estimate from `a` to `h` in the bag `x`, as the record of `a` holds it. -/
noncomputable def toH (out : V → LabelOut V) (x : ℕ) (a h : V) : ℝ≥0∞ :=
  ⨅ E ∈ (out a).chain, ⨅ (_ : E.bag = x), ⨅ F ∈ E.hubs, ⨅ (_ : F.hub = h), (F.toHub : ℝ≥0∞)

/-- The estimate from `h` to `z` in the bag `x`, as the record of `z` holds it. -/
noncomputable def fromH (out : V → LabelOut V) (x : ℕ) (h z : V) : ℝ≥0∞ :=
  ⨅ E ∈ (out z).chain, ⨅ (_ : E.bag = x), ⨅ F ∈ E.hubs, ⨅ (_ : F.hub = h), (F.fromHub : ℝ≥0∞)

/-- The query computed from correct labels is `(1 + 1/e)`-approximate, for all offsets. -/
theorem LabelWitness.query_bound {N : Net V} {ℓ : V → V → ℕ} {e h s w : ℕ} {out : V → LabelOut V}
    (W : LabelWitness N ℓ e h s w out) (he : 1 ≤ e) (φ : V → ℝ≥0∞) (z : V) :
    dsrc N.G.Adj (lenOf ℓ) φ z ≤ W.H.queryC₂ φ (toH out) (fromH out) z ∧
      W.H.queryC₂ φ (toH out) (fromH out) z ≤ (1 + (e : ℝ≥0∞)⁻¹) * dsrc N.G.Adj (lenOf ℓ) φ z := by
  have hε : ((e : ℝ≥0∞)⁻¹) ≠ ∞ := ENNReal.inv_ne_top.2 (by exact_mod_cast (by omega : e ≠ 0))
  refine W.H.lemmaV_chain₂ φ (toH out) (fromH out) (lenOf ℓ) _ hε ?_ ?_ ?_ ?_ z
  · intro x a y _ _
    simp only [toH, le_iInf_iff]
    rintro E hE rfl F hF rfl
    exact W.to_lo a E hE F hF
  · intro x y a _ _
    simp only [fromH, le_iInf_iff]
    rintro E hE rfl F hF rfl
    exact W.from_lo a E hE F hF
  · intro x a y hc hy
    obtain ⟨E, hE, rfl⟩ := (W.chain_iff a x).1 hc
    obtain ⟨F, hF, rfl⟩ := (W.hubs_iff a E hE y).1 hy
    exact (iInf_le_of_le E <| iInf_le_of_le hE <| iInf_le_of_le rfl <| iInf_le_of_le F <|
      iInf_le_of_le hF <| iInf_le _ rfl).trans (W.to_hi a E hE F hF)
  · intro x y a hc hy
    obtain ⟨E, hE, rfl⟩ := (W.chain_iff a x).1 hc
    obtain ⟨F, hF, rfl⟩ := (W.hubs_iff a E hE y).1 hy
    exact (iInf_le_of_le E <| iInf_le_of_le hE <| iInf_le_of_le rfl <| iInf_le_of_le F <|
      iInf_le_of_le hF <| iInf_le _ rfl).trans (W.from_hi a E hE F hF)

end Query

/-! ### Small networks have labels -/

section OneBag

private theorem wt_nat {V : Type} {adj : V → V → Prop} (ℓ : V → V → ℕ) {a b : V} (p : Walk adj a b) :
    ∃ k : ℕ, p.wt (lenOf ℓ) = k := by
  induction p with
  | nil a => exact ⟨0, by simp⟩
  | cons e p ih =>
    obtain ⟨k, hk⟩ := ih
    exact ⟨_, by rw [Walk.wt_cons, hk, lenOf, ← Nat.cast_add]⟩

private theorem dist_nat {V : Type} {adj : V → V → Prop} (ℓ : V → V → ℕ) {a b : V} (p₀ : Walk adj a b) :
    ∃ k : ℕ, dist adj (lenOf ℓ) Set.univ a b = k := by
  classical
  have hex : ∃ k : ℕ, ∃ p : Walk adj a b, p.wt (lenOf ℓ) = k := by
    obtain ⟨k, hk⟩ := wt_nat ℓ p₀
    exact ⟨k, p₀, hk⟩
  refine ⟨Nat.find hex, le_antisymm ?_ ?_⟩
  · obtain ⟨p, hp⟩ := Nat.find_spec hex
    exact (iInf₂_le p (by simp)).trans_eq hp
  · refine le_iInf₂ fun p _ => ?_
    obtain ⟨k, hk⟩ := wt_nat ℓ p
    rw [hk]
    exact_mod_cast Nat.find_min' hex ⟨p, hk⟩

private theorem dist_le_distR {V : Type} (adj : V → V → Prop) (g : V → V → ℝ≥0∞) (A : V → V → Prop) (a b : V) :
    dist adj g Set.univ a b ≤ distR adj g A a b :=
  le_iInf₂ fun p _ => iInf₂_le p (by simp)

variable {V : Type} [Fintype V] [DecidableEq V]

private theorem toWalk {N : Net V} {ℓ : V → V → ℕ} {W : ℕ} (hℓ : N.LensIn ℓ W) {a b : V}
    (p : N.G.Walk a b) :
    ∃ q : Walk N.G.Adj a b, q.support.length = p.length + 1 ∧
      q.wt (lenOf ℓ) ≤ ((p.length * W : ℕ) : ℝ≥0∞) := by
  induction p with
  | nil => exact ⟨.nil _, by simp, by simp⟩
  | cons h p ih =>
    obtain ⟨q, hq, hw⟩ := ih
    refine ⟨.cons h q, by simp [hq], ?_⟩
    rw [Walk.wt_cons, SimpleGraph.Walk.length_cons, add_mul, one_mul, add_comm (p.length * W),
      Nat.cast_add]
    exact add_le_add (Nat.cast_le.2 (hℓ _ _ h).2) hw

/-- The hierarchy with the one bag `0`, whose vertices are all hubs. -/
private def oneBag (N : Net V) : RHierarchy V ℕ N.G.Adj where
  bag x := {_z | x = 0}
  arc x a b := x = 0 ∧ N.G.Adj a b
  hub x := {_z | x = 0}
  kid _ _ := False
  wf := ⟨fun _ => ⟨_, fun _ h => h.elim⟩⟩
  root := 0
  root_bag _ := rfl
  root_arc _ _ h := ⟨rfl, h⟩
  arc_bag _ _ _ h := ⟨h.1, h.1⟩
  cover _ _ hz hz' := absurd hz hz'
  uniq _ _ _ _ hc := hc.elim
  edge _ _ _ h ha _ := absurd h.1 ha

private theorem oneBag_chain (N : Net V) (v : V) (x : ℕ) : (oneBag N).Chain v x ↔ x = 0 := by
  constructor
  · intro h
    cases h with
    | root => rfl
    | step _ _ hk _ => exact hk.elim
  · rintro rfl
    exact RHierarchy.Chain.root

/-- Every network with at most `s` nodes and diameter at most `s` has correct labels: one bag whose
vertices are all hubs, with exact distances, whose subgraph is the network. -/
theorem labelsOK_oneBag (N : Net V) {ℓ : V → V → ℕ} {W s w : ℕ} (e : ℕ)
    (hc : Fintype.card V ≤ s) (hD : N.DiamLE s) (hℓ : N.LensIn ℓ W) (hw : s * W < 2 ^ w) :
    ∃ out, LabelsOK N ℓ e 0 s w out := by
  classical
  have hd : ∀ a b, ∃ k : ℕ, dist N.G.Adj (lenOf ℓ) Set.univ a b = k ∧ k ≤ s * W := by
    intro a b
    obtain ⟨p, hp⟩ := hD a b
    obtain ⟨q, -, hq⟩ := toWalk hℓ p
    obtain ⟨k, hk⟩ := dist_nat ℓ q
    refine ⟨k, hk, ?_⟩
    have h1 : (k : ℝ≥0∞) ≤ ((p.length * W : ℕ) : ℝ≥0∞) :=
      hk ▸ (iInf₂_le q (by simp)).trans hq
    exact (by exact_mod_cast h1 : k ≤ p.length * W).trans (Nat.mul_le_mul_right _ hp)
  choose d hd hdle using hd
  let out : V → LabelOut V := fun v =>
    { chain := [⟨0, Finset.univ.toList.map fun y => ⟨y, (d v y : ℕ∞), (d y v : ℕ∞)⟩⟩]
      treeBags := fun u => if N.G.Adj v u then [0] else [] }
  have hE : ∀ v, ∀ E ∈ (out v).chain, E.bag = 0 ∧
      ∀ F ∈ E.hubs, F.toHub = (d v F.hub : ℕ∞) ∧ F.fromHub = (d F.hub v : ℕ∞) := by
    intro v E hE
    obtain rfl := List.mem_singleton.1 hE
    refine ⟨rfl, fun F hF => ?_⟩
    obtain ⟨y, -, rfl⟩ := List.mem_map.1 hF
    exact ⟨rfl, rfl⟩
  refine ⟨out, ⟨{
    H := oneBag N
    tree := fun x a b => x = 0 ∧ N.G.Adj a b
    depth := fun _ => 0
    depth_kid := fun _ _ h => h.elim
    height := fun _ => le_rfl
    tree_adj := fun _ _ _ h => h.2
    tree_symm := fun _ _ _ h => ⟨h.1, h.2.symm⟩
    tree_span := ?_
    congestion := fun _ _ _ => ⟨{0}, by simp, fun x _ h => by simp [h.1]⟩
    hub_card := ?_
    chain_iff := ?_
    hubs_iff := ?_
    tree_know := ?_
    to_lo := ?_
    to_hi := ?_
    from_lo := ?_
    from_hi := ?_
    name_lt := fun v E h => by rw [(hE v E h).1]; positivity
    treeBags_lt := ?_
    value_lt := ?_ }⟩⟩
  · rintro x a b (rfl : x = 0) -
    obtain ⟨p, hp⟩ := hD a b
    have key : ∀ {a b : V} (p : N.G.Walk a b),
        ∃ q : Walk (fun a b => (0 : ℕ) = 0 ∧ N.G.Adj a b) a b, q.support.length = p.length + 1 := by
      intro a b p
      induction p with
      | nil => exact ⟨.nil _, by simp⟩
      | cons h p ih =>
        obtain ⟨q, hq⟩ := ih
        exact ⟨.cons ⟨rfl, h⟩ q, by simp [hq]⟩
    obtain ⟨q, hq⟩ := key p
    exact ⟨q, by omega⟩
  · intro x
    by_cases hx : x = 0
    · subst hx
      have : (oneBag N).hub 0 = Set.univ := Set.eq_univ_of_forall fun _ => rfl
      rw [this, Set.ncard_univ, Nat.card_eq_fintype_card]
      exact hc
    · have : (oneBag N).hub x = ∅ := Set.eq_empty_of_forall_notMem fun _ h => hx h
      rw [this, Set.ncard_empty]
      exact Nat.zero_le _
  · intro v x
    rw [oneBag_chain]
    constructor
    · rintro rfl
      exact ⟨_, List.mem_singleton.2 rfl, rfl⟩
    · rintro ⟨E, hEm, rfl⟩
      exact (hE v E hEm).1
  · intro v E hEm y
    constructor
    · intro _
      obtain rfl := List.mem_singleton.1 hEm
      exact ⟨⟨y, (d v y : ℕ∞), (d y v : ℕ∞)⟩,
        List.mem_map.2 ⟨y, Finset.mem_toList.2 (Finset.mem_univ y), rfl⟩, rfl⟩
    · intro _
      exact (hE v E hEm).1
  · intro v u hvu x
    show x ∈ (if N.G.Adj v u then [0] else []) ↔ x = 0 ∧ N.G.Adj v u
    simp [hvu]
  · intro v E hEm F hF
    rw [(hE v E hEm).2 F hF |>.1, hd]
    simp
  · intro v E hEm F hF
    rw [(hE v E hEm).2 F hF |>.1]
    simp only [ENat.toENNReal_coe]
    rw [← hd]
    exact (dist_le_distR _ _ _ _ _).trans (le_mul_of_one_le_left (by simp) le_self_add)
  · intro v E hEm F hF
    rw [(hE v E hEm).2 F hF |>.2, hd]
    simp
  · intro v E hEm F hF
    rw [(hE v E hEm).2 F hF |>.2]
    simp only [ENat.toENNReal_coe]
    rw [← hd]
    exact (dist_le_distR _ _ _ _ _).trans (le_mul_of_one_le_left (by simp) le_self_add)
  · intro v u x hx
    have hx' : x ∈ (if N.G.Adj v u then [0] else []) := hx
    split_ifs at hx' with h
    · rw [List.mem_singleton.1 hx']
      positivity
    · simp at hx'
  · intro v E hEm F hF
    obtain ⟨h1, h2⟩ := (hE v E hEm).2 F hF
    rw [h1, h2]
    exact ⟨Or.inr (by exact_mod_cast (hdle _ _).trans_lt hw),
      Or.inr (by exact_mod_cast (hdle _ _).trans_lt hw)⟩

/-- The triangle with unit lengths has labels with one bag. -/
theorem labelsOK_triNet : ∃ out, LabelsOK triNet (fun _ _ => 1) 1 0 3 2 out :=
  labelsOK_oneBag triNet 1 (by simp) (fun u v => by
    obtain ⟨p, hp⟩ := triNet_diam u v
    exact ⟨p, by omega⟩) (fun _ _ _ => ⟨le_rfl, le_rfl⟩) (by norm_num : 3 * 1 < 2 ^ 2)

end OneBag

/-! ### Stated assumptions -/

/-- (G3) [10, Thm 1]. A matrix of positive finite distances with `k` terminals that satisfies the
triangle inequality and the crossing inequalities for the terminals in the order `0, …, k - 1` is
realized by a planar map with at most `C * k ^ 6` vertices and these terminals in this order along one
face. The inequalities are those of `RotSystem.DiskDrawn.monge`. -/
def RealizationBox (C : ℕ) : Prop :=
  ∀ k : ℕ, 2 ≤ k → ∀ d : Fin k → Fin k → ℝ≥0∞,
    (∀ i, d i i = 0) → (∀ i j, i ≠ j → d i j ≠ 0 ∧ d i j ≠ ⊤) →
    (∀ i j l, d i l ≤ d i j + d j l) →
    (∀ a b c f u v x z : Fin k, [a, b, c, f].Sublist (List.finRange k) →
      ((u = a ∧ v = c) ∨ (u = c ∧ v = a)) → ((x = b ∧ z = f) ∨ (x = f ∧ z = b)) →
      d u z + d x v ≤ d u v + d x z) →
    ∃ (m : ℕ) (K : RotSystem (Fin m)) (g : Fin m → ℝ≥0∞) (l : Fin k → Fin m),
      K.numVertices ≤ C * k ^ 6 ∧ K.DiskDrawn (List.ofFn l) ∧
        ∀ i j, K.walkDist g (K.tail (l i)) (K.tail (l j)) = d i j

/-- (G5) [1, Lemma 11]. `(1 + 1/e)`-approximate distance labels on planar digraphs with lengths in
`{0, …, N, ∞}`, of `Õ(e)` words of `O(log S)` bits. The query is fixed before the map. -/
def DistanceLabelBox (C c : ℕ) : Prop :=
  ∀ e : ℕ, 1 ≤ e → ∃ query : List ℕ → List ℕ → ℕ∞,
    ∀ (D : Type) [Fintype D] [DecidableEq D] (R : RotSystem D) (N : ℕ) (g : D → ℕ∞),
      R.Planar → (∀ x, g x = ⊤ ∨ g x ≤ N) →
      ∃ label : R.Vertex → List ℕ, ∀ u v,
        (label u).length ≤ C * Nat.log 2 (R.numVertices + N + 2) ^ c * e ∧
        (∀ x ∈ label u, x < (R.numVertices + N + 2) ^ c) ∧
        R.walkDist (fun x => (g x : ℝ≥0∞)) u v ≤ (query (label u) (label v) : ℝ≥0∞) ∧
        (query (label u) (label v) : ℝ≥0∞) ≤
          (1 + (e : ℝ≥0∞)⁻¹) * R.walkDist (fun x => (g x : ℝ≥0∞)) u v

/-- (G6) [9, Lemma 5.11], [18, Lemma 3.17]. From the rotation lists, in `Õ(D)` rounds, every node
learns for each dart at it the identifier of its face, of `O(L)` bits. -/
def FaceIdBox : Prop :=
  ∃ C c : ℕ, ∀ n D : ℕ, 1 ≤ D →
    ∃ (σ : Type) (A : Algorithm (Fin n) (List (Fin n)) σ (C * logScale n 0 0 ^ c))
      (out : Fin n → σ → Fin n → ℕ),
      ∀ N : Net (Fin n), N.toRot.Planar → N.DiamLE D →
        ∀ d d' : N.G.Dart,
          let T := C * logScale n 0 0 ^ c * D
          let id := fun x : N.G.Dart => out x.fst (A.run N.G N.rotList T x.fst) x.snd
          (id d = id d' ↔ N.toRot.faceOf d = N.toRot.faceOf d') ∧ id d < 2 ^ (C * logScale n 0 0)

/-- A planar embedding in `Õ(D)` rounds: from its neighbours in any order, every node of a planar
network learns a rotation list, and these lists form a plane network on the same graph. -/
def EmbeddingBox : Prop :=
  ∃ C c : ℕ, ∀ n D : ℕ, 1 ≤ D →
    ∃ (σ : Type) (A : Algorithm (Fin n) (List (Fin n)) σ (C * logScale n 0 0 ^ c))
      (out : Fin n → σ → List (Fin n)),
      ∀ N : Net (Fin n), N.toRot.Planar → N.DiamLE D →
        ∀ nb : Fin n → List (Fin n), (∀ v w, w ∈ nb v ↔ N.G.Adj v w) →
          ∃ N' : Net (Fin n), N'.G = N.G ∧ N'.toRot.Planar ∧
            ∀ v, N'.rotList v = out v (A.run N.G nb (C * logScale n 0 0 ^ c * D) v)

/-- The input of a node for one aggregation over many subgraphs. -/
structure AggIn (V : Type) where
  /-- For a neighbour, the subgraphs that contain the edge to it. -/
  subgraphs : V → List ℕ
  /-- The subgraphs of which the node is a member. -/
  member : List ℕ
  /-- The items of the node: subgraph, key, value. -/
  items : List (ℕ × ℕ × ℕ)

section Agg

variable {V : Type} [Fintype V] [DecidableEq V]

/-- A valid input: members of a subgraph are joined by walks of at most `s` arcs inside it, an edge
lies in at most `c` subgraphs, a subgraph has at most `k` keys, and all fields have `b` bits. -/
structure AggIn.Valid (N : Net V) (inp : V → AggIn V) (s c k b : ℕ) : Prop where
  symm : ∀ v u, N.G.Adj v u → ∀ x, x ∈ (inp v).subgraphs u ↔ x ∈ (inp u).subgraphs v
  span : ∀ x a a', x ∈ (inp a).member → x ∈ (inp a').member →
    ∃ p : Walk (fun u v => N.G.Adj u v ∧ x ∈ (inp u).subgraphs v) a a', p.support.length ≤ s + 1
  congestion : ∀ v u, N.G.Adj v u → ((inp v).subgraphs u).length ≤ c
  keys : ∀ x, ∃ K : Finset ℕ, K.card ≤ k ∧ ∀ v, ∀ t ∈ (inp v).items, t.1 = x → t.2.1 ∈ K
  items_member : ∀ v, ∀ t ∈ (inp v).items, t.1 ∈ (inp v).member
  fields : ∀ v, ∀ t ∈ (inp v).items, t.1 < 2 ^ b ∧ t.2.1 < 2 ^ b ∧ t.2.2 < 2 ^ b
  names : ∀ v u, ∀ x ∈ (inp v).subgraphs u, x < 2 ^ b

/-- `r` is the least value of the items of the subgraph `x` with the key `κ`, and `none` if there is
no such item. -/
def AggIn.IsMin (inp : V → AggIn V) (x κ : ℕ) : Option ℕ → Prop
  | none => ∀ v m, (x, κ, m) ∉ (inp v).items
  | some m => (∃ v, (x, κ, m) ∈ (inp v).items) ∧ ∀ v m', (x, κ, m') ∈ (inp v).items → m ≤ m'

end Agg

/-- Aggregation, classical. Per subgraph: a leader by flooding, a breadth-first tree, a pipelined
convergecast of the minima in the order of the keys, and a broadcast. An edge serves its at most `c`
subgraphs in turn, in sorted order. Every member of a subgraph learns the minimum per key. -/
def AggBox : Prop :=
  ∃ C : ℕ, ∀ n s c k b : ℕ,
    ∃ (σ : Type) (A : Algorithm (Fin n) (AggIn (Fin n)) σ (C * (b + logScale n 0 0)))
      (out : Fin n → σ → ℕ → ℕ → Option ℕ),
      ∀ (N : Net (Fin n)) (inp : Fin n → AggIn (Fin n)), AggIn.Valid N inp s c k b →
        ∀ v, ∀ x ∈ (inp v).member, ∀ κ,
          AggIn.IsMin inp x κ (out v (A.run N.G inp (C * c * (s + k + 1)) v) x κ)

/-- The input of a node for shortest paths from a virtual source: its neighbours in rotation order,
the lengths of its arcs and its offset, with `⊤` for a missing arc or offset. -/
structure OracleIn (V : Type) where
  /-- The neighbours in rotation order. -/
  nbrs : List V
  /-- The length of the arc to a neighbour; `⊤` for other nodes. -/
  lenOut : V → ℕ∞
  /-- The length of the arc from a neighbour; `⊤` for other nodes. -/
  lenIn : V → ℕ∞
  /-- The length of the arc from the virtual source. -/
  offset : ℕ∞

section Oracle

variable {V : Type} [Fintype V] [DecidableEq V]

/-- The input of the nodes of a network with lengths `ℓ` and offsets `φ`. -/
def Net.oracleIn (N : Net V) (ℓ : V → V → ℕ∞) (φ : V → ℕ∞) (v : V) : OracleIn V where
  nbrs := N.rotList v
  lenOut u := if N.G.Adj v u then ℓ v u else ⊤
  lenIn u := if N.G.Adj v u then ℓ u v else ⊤
  offset := φ v

/-- Finite lengths lie in `[m, W]`, finite offsets in `[0, W]`. -/
def OracleValid (N : Net V) (m W : ℕ) (ℓ : V → V → ℕ∞) (φ : V → ℕ∞) : Prop :=
  (∀ u v, N.G.Adj u v → ℓ u v = ⊤ ∨ ((m : ℕ∞) ≤ ℓ u v ∧ ℓ u v ≤ W)) ∧ ∀ v, φ v = ⊤ ∨ φ v ≤ W

/-- The distance from the virtual source. -/
noncomputable def Net.dsrcTop (N : Net V) (ℓ : V → V → ℕ∞) (φ : V → ℕ∞) (v : V) : ℝ≥0∞ :=
  dsrc N.G.Adj (lenTop ℓ) (offTop φ) v

end Oracle

/-- `A` is a `(1 + 1/e)`-approximate oracle in `T` rounds, on planar networks of diameter at most `D`
with lengths in `[1, W]`. -/
def ApproxOracleOK {σ : Type} {B : ℕ} (n W e D T : ℕ) (A : Algorithm (Fin n) (OracleIn (Fin n)) σ B)
    (out : Fin n → σ → ℕ∞) : Prop :=
  ∀ (N : Net (Fin n)) (ℓ : Fin n → Fin n → ℕ∞) (φ : Fin n → ℕ∞),
    N.toRot.Planar → N.DiamLE D → OracleValid N 1 W ℓ φ → ∀ v,
      N.dsrcTop ℓ φ v ≤ (out v (A.run N.G (N.oracleIn ℓ φ) T v) : ℝ≥0∞) ∧
        (out v (A.run N.G (N.oracleIn ℓ φ) T v) : ℝ≥0∞) ≤ (1 + (e : ℝ≥0∞)⁻¹) * N.dsrcTop ℓ φ v

/-- `A` is an exact oracle in `T` rounds, on planar networks of diameter at most `D` with lengths in
`[0, W]`. -/
def ExactOracleOK {σ : Type} {B : ℕ} (n W D T : ℕ) (A : Algorithm (Fin n) (OracleIn (Fin n)) σ B)
    (out : Fin n → σ → ℕ∞) : Prop :=
  ∀ (N : Net (Fin n)) (ℓ : Fin n → Fin n → ℕ∞) (φ : Fin n → ℕ∞),
    N.toRot.Planar → N.DiamLE D → OracleValid N 0 W ℓ φ → ∀ v,
      (out v (A.run N.G (N.oracleIn ℓ φ) T v) : ℝ≥0∞) = N.dsrcTop ℓ φ v

/-- [3, Thm 1.7, Alg. 3]. From a `(1 + 1/e₀)`-approximate oracle, `O(L)` calls with `e₀ = O(L)` give
estimates `d` for finite offsets, in units of one half, with `2 d(σ, v) ≤ d v`,
`d b ≤ d a + 4 ℓ(a, b)` and `d v ≤ 4 φ v`. So `d / 2` does not underestimate and is `2`-smooth on the
arcs and on the arcs from the virtual source, which is the contract of `Boost.Run` with a constant
`α`. -/
def SmoothingBox : Prop :=
  ∃ C c : ℕ, ∀ n W D T B : ℕ, ∀ (σ : Type) (A : Algorithm (Fin n) (OracleIn (Fin n)) σ B)
    (out : Fin n → σ → ℕ∞),
    ApproxOracleOK n ((n + W + 2) ^ C) (C * logScale n W 0) D T A out →
    ∃ (σ' : Type) (Q : Algorithm (Fin n) (OracleIn (Fin n)) σ' (B + C * logScale n W 0 ^ c))
      (out' : Fin n → σ' → ℕ),
      ∀ (N : Net (Fin n)) (ℓ : Fin n → Fin n → ℕ∞) (φ : Fin n → ℕ∞),
        N.toRot.Planar → N.DiamLE D → OracleValid N 1 W ℓ φ → (∀ v, φ v ≠ ⊤) →
        let d := fun v => out' v (Q.run N.G (N.oracleIn ℓ φ) (C * logScale n W 0 * (T + D + 1)) v)
        (∀ v, 2 * N.dsrcTop ℓ φ v ≤ (d v : ℝ≥0∞)) ∧
          (∀ a b, N.G.Adj a b → (d b : ℕ∞) ≤ d a + 4 * ℓ a b) ∧
          ∀ v, (d v : ℕ∞) ≤ 4 * φ v

/-! ### Negative weights -/

/-- The input of a node for negative weights: its neighbours in rotation order, the weights of its
arcs, with `none` for a missing arc, and whether it is the source. -/
structure NegIn (V : Type) where
  /-- The neighbours in rotation order. -/
  nbrs : List V
  /-- The weight of the arc to a neighbour. -/
  wOut : V → Option ℤ
  /-- The weight of the arc from a neighbour. -/
  wIn : V → Option ℤ
  /-- Whether the node is the source. -/
  isSource : Bool

/-- Walks with integer weights: `WalkZ adj w a b y` says that a walk from `a` to `b` has weight `y`. -/
inductive WalkZ {V : Type} (adj : V → V → Prop) (w : V → V → Option ℤ) : V → V → ℤ → Prop
  | nil (a : V) : WalkZ adj w a a 0
  | cons {a b c : V} {x y : ℤ} : adj a b → w a b = some x → WalkZ adj w b c y →
      WalkZ adj w a c (x + y)

/-- The number of private strings with a property. -/
noncomputable def strCount {V ρ : Type} [Fintype V] [DecidableEq V] [Fintype ρ]
    (bad : (V → ρ) → Prop) : ℕ := by
  classical
  exact (Finset.univ.filter bad).card

section Neg

variable {V : Type} [Fintype V] [DecidableEq V]

/-- The input of the nodes of a network with weights `w` and source `s`. -/
def Net.negIn (N : Net V) (w : V → V → Option ℤ) (s v : V) : NegIn V where
  nbrs := N.rotList v
  wOut u := if N.G.Adj v u then w v u else none
  wIn u := if N.G.Adj v u then w u v else none
  isSource := decide (v = s)

/-- The network has a closed walk of negative weight. -/
def Net.HasNegCycle (N : Net V) (w : V → V → Option ℤ) : Prop :=
  ∃ a y, WalkZ N.G.Adj w a a y ∧ y < 0

/-- A correct answer: with a negative cycle all nodes report `none`, and otherwise every node reports
its distance from `s`, with `some none` for an unreachable node. -/
def Net.NegSpec (N : Net V) (w : V → V → Option ℤ) (s : V) (r : V → Option (Option ℤ)) : Prop :=
  (N.HasNegCycle w ∧ ∀ v, r v = none) ∨
    (¬ N.HasNegCycle w ∧ ∀ v,
      (r v = some none ∧ ∀ y, ¬ WalkZ N.G.Adj w s v y) ∨
      ∃ d, r v = some (some d) ∧ IsLeast {y | WalkZ N.G.Adj w s v y} d)

/-- Weights have absolute value at most `W`. -/
def Net.NegValid (N : Net V) (W : ℕ) (w : V → V → Option ℤ) : Prop :=
  ∀ a b, N.G.Adj a b → ∀ x, w a b = some x → |x| ≤ W

end Neg

/-- `(log x)^(C √log x)`, the factor of the reduction of [6, Thm 2]. -/
def tauSubpoly (C x : ℕ) : ℕ := (Nat.log 2 x + 1) ^ (C * (Nat.sqrt (Nat.log 2 x) + 1))

/-- `(log x)^c`, the factor of the reduction of `notes/NEGATIVE.md`. -/
def tauPolylog (c x : ℕ) : ℕ := (Nat.log 2 x + 1) ^ c

/-- Negative weights from exact nonnegative SSSP: for every exponent `k`, an exact oracle in `T`
rounds gives an algorithm with private strings in `C * τ(n + W + 2) * (T + Õ(D))` rounds, wrong on at
most a fraction `1 / (n + 1) ^ k` of the strings. -/
def NegReduction (τ : ℕ → ℕ) : Prop :=
  ∀ k : ℕ, ∃ C c : ℕ, ∀ n W D T B : ℕ, 1 ≤ D →
    ∀ (σ : Type) (A : Algorithm (Fin n) (OracleIn (Fin n)) σ B) (out : Fin n → σ → ℕ∞),
    ExactOracleOK n ((n + W + 2) ^ C) D T A out →
    ∃ (ρ : Type) (_ : Fintype ρ) (σ' : Type)
      (P : Algorithm (Fin n) (NegIn (Fin n) × ρ) σ' (B + C * logScale n W 0 ^ c))
      (out' : Fin n → σ' → Option (Option ℤ)),
      ∀ (N : Net (Fin n)) (w : Fin n → Fin n → Option ℤ) (s : Fin n),
        N.toRot.Planar → N.DiamLE D → N.NegValid W w →
        strCount (fun r : Fin n → ρ => ¬ N.NegSpec w s (fun v =>
          out' v (P.run N.G (fun u => (N.negIn w s u, r u))
            (C * τ (n + W + 2) * (T + C * logScale n W 0 ^ c * D)) v))) * (n + 1) ^ k ≤
        Fintype.card (Fin n → ρ)

/-! ### Round bounds -/

section Bounds

variable {V : Type} [Fintype V] [DecidableEq V]

/-- A correct answer for shortest paths from a virtual source: exact distances, and parents that form
a shortest-path forest whose roots are the nodes reached directly from the virtual source. A node
without a parent is unreachable, or its distance is its offset. -/
structure Net.ExactSpec (N : Net V) (ℓ : V → V → ℕ∞) (φ : V → ℕ∞) (r : V → ℕ∞ × Option V) : Prop where
  dist_eq : ∀ v, ((r v).1 : ℝ≥0∞) = N.dsrcTop ℓ φ v
  parent : ∃ rank : V → ℕ, ∀ v,
    (∃ p, (r v).2 = some p ∧ N.G.Adj p v ∧ (r v).1 ≠ ⊤ ∧ (r p).1 + ℓ p v = (r v).1 ∧
      rank p < rank v) ∨
    ((r v).2 = none ∧ ((r v).1 = ⊤ ∨ (r v).1 = φ v))

/-- The input of the nodes for maximum flow. -/
structure FlowIn (V : Type) where
  /-- The neighbours in rotation order. -/
  nbrs : List V
  /-- The capacity of the arc to a neighbour. -/
  capOut : V → ℕ
  /-- The capacity of the arc from a neighbour. -/
  capIn : V → ℕ
  /-- Whether the node is the source. -/
  isSource : Bool
  /-- Whether the node is the sink. -/
  isSink : Bool

/-- The input of the nodes of a network with capacities `c`, source `s` and sink `t`. -/
def Net.flowIn (N : Net V) (c : V → V → ℕ) (s t v : V) : FlowIn V where
  nbrs := N.rotList v
  capOut u := if N.G.Adj v u then c v u else 0
  capIn u := if N.G.Adj v u then c u v else 0
  isSource := decide (v = s)
  isSink := decide (v = t)

/-- `f` is an `st`-flow of value `β`, as the net flow on the edges. -/
structure Net.IsFlow (N : Net V) (c : V → V → ℕ) (s t : V) (f : V → V → ℤ) (β : ℤ) : Prop where
  skew : ∀ a b, N.G.Adj a b → f b a = - f a b
  cap : ∀ a b, N.G.Adj a b → f a b ≤ c a b
  cons : ∀ v, v ≠ s → v ≠ t → ∑ u ∈ N.G.neighborFinset v, f v u = 0
  val : ∑ u ∈ N.G.neighborFinset s, f s u = β

/-- A correct answer for maximum flow: every node reports the value and the flow on its edges, and
this is a flow of maximum value. -/
def Net.FlowSpec (N : Net V) (c : V → V → ℕ) (s t : V) (r : V → ℕ × (V → ℤ)) : Prop :=
  ∃ β : ℕ, (∀ v, (r v).1 = β) ∧ N.IsFlow c s t (fun v u => (r v).2 u) β ∧
    ∀ f β', N.IsFlow c s t f β' → β' ≤ β

end Bounds

/-- Exact SSSP from a virtual source with lengths in `{0, …, W, ∞}` in `Õ(D)` rounds,
deterministically: the Exact SSSP Theorem. -/
def ExactSsspBound : Prop :=
  ∃ C c : ℕ, ∀ n W D : ℕ, 1 ≤ D →
    ∃ (σ : Type) (A : Algorithm (Fin n) (OracleIn (Fin n)) σ (C * logScale n W 0 ^ c))
      (out : Fin n → σ → ℕ∞ × Option (Fin n)),
      ∀ (N : Net (Fin n)) (ℓ : Fin n → Fin n → ℕ∞) (φ : Fin n → ℕ∞),
        N.toRot.Planar → N.DiamLE D → OracleValid N 0 W ℓ φ →
        N.ExactSpec ℓ φ (fun v =>
          out v (A.run N.G (N.oracleIn ℓ φ) (C * logScale n W 0 ^ c * D) v))

/-- Negative weights in `C * τ(n + W + 2) * Õ(D)` rounds with high probability: the Negative Weights
Theorem for `τ = tauSubpoly C`. -/
def NegSsspBound (τ : ℕ → ℕ) : Prop :=
  ∀ k : ℕ, ∃ C c : ℕ, ∀ n W D : ℕ, 1 ≤ D →
    ∃ (ρ : Type) (_ : Fintype ρ) (σ : Type)
      (P : Algorithm (Fin n) (NegIn (Fin n) × ρ) σ (C * logScale n W 0 ^ c))
      (out : Fin n → σ → Option (Option ℤ)),
      ∀ (N : Net (Fin n)) (w : Fin n → Fin n → Option ℤ) (s : Fin n),
        N.toRot.Planar → N.DiamLE D → N.NegValid W w →
        strCount (fun r : Fin n → ρ => ¬ N.NegSpec w s (fun v =>
          out v (P.run N.G (fun u => (N.negIn w s u, r u))
            (C * τ (n + W + 2) * logScale n W 0 ^ c * D) v))) * (n + 1) ^ k ≤
        Fintype.card (Fin n → ρ)

/-- Maximum flow with capacities in `{0, …, W}` in `C * τ(n + W + 2) * Õ(D)` rounds with high
probability: the value and the flow on every edge, as in the Maximum Flow Theorem for
`τ = tauSubpoly C`. -/
def MaxFlowBound (τ : ℕ → ℕ) : Prop :=
  ∀ k : ℕ, ∃ C c : ℕ, ∀ n W D : ℕ, 1 ≤ D →
    ∃ (ρ : Type) (_ : Fintype ρ) (σ : Type)
      (P : Algorithm (Fin n) (FlowIn (Fin n) × ρ) σ (C * logScale n W 0 ^ c))
      (out : Fin n → σ → ℕ × (Fin n → ℤ)),
      ∀ (N : Net (Fin n)) (cap : Fin n → Fin n → ℕ) (s t : Fin n),
        N.toRot.Planar → N.DiamLE D → (∀ a b, N.G.Adj a b → cap a b ≤ W) → s ≠ t →
        strCount (fun r : Fin n → ρ => ¬ N.FlowSpec cap s t (fun v =>
          out v (P.run N.G (fun u => (N.flowIn cap s t u, r u))
            (C * τ (n + W + 2) * logScale n W 0 ^ c * D) v))) * (n + 1) ^ k ≤
        Fintype.card (Fin n → ρ)

end Congest

end SsspFlow
