import SsspFlow.DualNet
import SsspFlow.LabelHypothesis

/-!
# Flows and shortest paths on the dual network

The identifiers of the dual network of `N` are the triples `(v, i, k)` of two nodes and a kind, so a
network with `n` nodes has a dual network with `5 n ^ 2` identifiers whatever its edges are, and every
identifier names its host `v`.

* `dualNet`: the expansion of `N` with all remaining identifiers as pendant nodes. It is planar
  (`dualNet_planar`), and its diameter is at most `5 D + 6` (`dualNet_diam`).
* `dualNet_rotList`: the host computes the rotation list of an identifier from its own rotation list.
* `dualW`: the arcs. An arc between two corners at a node crosses a dart and has its cost, and arcs along
  a ring have weight zero in both directions.
* `no_negCycle_of_flow`: for a unit flow `σ`, a flow of value `β` rules out negative cycles for the costs
  `c - β σ`. The proof uses `RotSystem.exists_face_potential`.
* `isFlow_of_spec`: distances for the costs `c - β σ` give a flow of value `β`. Planarity is not used.
* `hasNegCycle_mono`: a negative cycle for `β ≥ 0` stays negative for all larger values.
* `negIn_eq`, `dual_adj_cross`: a host computes the inputs of its identifiers, and the edges between
  different hosts follow the edges of `N`, at most two per edge and direction.
-/

set_option autoImplicit false

namespace SsspFlow.Congest

open XNode Kind

/-! ### Walks -/

section Walks

variable {V : Type} {adj : V → V → Prop} {w : V → V → Option ℤ}

theorem WalkZ.trans {a b c : V} {y z : ℤ} (h₁ : WalkZ adj w a b y) (h₂ : WalkZ adj w b c z) :
    WalkZ adj w a c (y + z) := by
  induction h₁ with
  | nil a => simpa using h₂
  | cons h hw _ ih =>
    rw [add_assoc]
    exact .cons h hw (ih h₂)

/-- A potential bounds all walks. -/
theorem WalkZ.pot_le_of_adj (pot : V → ℤ)
    (h : ∀ a b x, adj a b → w a b = some x → pot a ≤ x + pot b) {a b : V} {y : ℤ}
    (hp : WalkZ adj w a b y) : pot a ≤ y + pot b := by
  induction hp with
  | nil a => simp
  | cons hab hw _ ih =>
    have := h _ _ _ hab hw
    linarith

end Walks

/-! ### Sums over darts -/

namespace Net

variable {V : Type} [Fintype V] [DecidableEq V] (N : Net V)

theorem sum_fiber {M : Type*} [AddCommMonoid M] (v : V) (F : V → M) :
    ∑ y ∈ Finset.univ.filter (fun y : N.G.Dart => y.fst = v), F y.snd =
      ∑ u ∈ N.G.neighborFinset v, F u := by
  refine Finset.sum_bij (fun y _ => y.snd) ?_ ?_ ?_ (fun _ _ => rfl)
  · intro y hy
    have hf := (Finset.mem_filter.1 hy).2
    rw [SimpleGraph.mem_neighborFinset, ← hf]
    exact y.adj
  · intro y₁ h₁ y₂ h₂ h
    have hf₁ := (Finset.mem_filter.1 h₁).2
    have hf₂ := (Finset.mem_filter.1 h₂).2
    exact SimpleGraph.Dart.ext _ _ (Prod.ext (hf₁.trans hf₂.symm) h)
  · intro u hu
    exact ⟨⟨(v, u), (SimpleGraph.mem_neighborFinset _ _ _).1 hu⟩, by simp, rfl⟩

theorem sum_dart {M : Type*} [AddCommMonoid M] (F : V → V → M) :
    ∑ y : N.G.Dart, F y.fst y.snd = ∑ v, ∑ u ∈ N.G.neighborFinset v, F v u := by
  rw [← Finset.sum_fiberwise (s := Finset.univ) (g := fun y : N.G.Dart => y.fst)]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [← N.sum_fiber v (F v)]
  refine Finset.sum_congr rfl fun y hy => ?_
  rw [(Finset.mem_filter.1 hy).2]

/-- A skew function on the edges has no net total. -/
theorem sum_skew (f : V → V → ℤ) (h : ∀ a b, N.G.Adj a b → f b a = - f a b) :
    ∑ v, ∑ u ∈ N.G.neighborFinset v, f v u = 0 := by
  rw [← N.sum_dart f]
  have h1 : ∑ y : N.G.Dart, f y.snd y.fst = ∑ y : N.G.Dart, f y.fst y.snd :=
    Equiv.sum_comp (⟨SimpleGraph.Dart.symm, SimpleGraph.Dart.symm, SimpleGraph.Dart.symm_symm,
      SimpleGraph.Dart.symm_symm⟩ : N.G.Dart ≃ N.G.Dart) fun y => f y.fst y.snd
  have h2 : ∑ y : N.G.Dart, f y.snd y.fst = - ∑ y : N.G.Dart, f y.fst y.snd := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun y _ => h _ _ y.adj
  omega

/-- A function that is invariant along the rotation depends only on the tail. -/
theorem rot_invariant {M : Type*} (q : N.G.Dart → M) (h : ∀ x, q (N.rotPerm x) = q x) (x y : N.G.Dart)
    (hxy : x.fst = y.fst) : q x = q y := by
  have h1 : FourColor.fconnect (⇑N.rotPerm) x y :=
    (N.toRot.tail_eq_iff x y).1 (N.tail_eq_iff.2 hxy)
  obtain ⟨m, hm⟩ := FourColor.fconnect_iff_iterate.1 h1
  rw [← hm]
  clear hm h1 hxy
  induction m with
  | zero => rfl
  | succ m ih => rw [Function.iterate_succ_apply', h, ih]

end Net

/-! ### The identifiers -/

section Ids

variable {V : Type} [Fintype V] [DecidableEq V] {W : Type} [Fintype W] [DecidableEq W]
variable (N : Net V) (e : V × V × Kind ≃ W)

/-- The node of the expansion for an identifier. -/
def xBack (p : V × V × Kind) : XNode V N.G.Dart :=
  if h : N.G.Adj p.1 p.2.1 then node p.2.2 ⟨(p.1, p.2.1), h⟩ else center p.1

/-- The identifiers of the expansion, and the centres at which all others hang. -/
noncomputable def xPad : PadMap (XNode V N.G.Dart) W where
  ι
    | center v => e (v, v, corner)
    | node k x => e (x.fst, x.snd, k)
  back a := xBack N (e.symm a)
  back_ι a := by
    cases a with
    | center v =>
      simp only [Equiv.symm_apply_apply, xBack]
      rw [dite_eq_right_iff.2 fun h => absurd h (N.G.loopless.irrefl v)]
    | node k x =>
      simp only [Equiv.symm_apply_apply, xBack]
      rw [dite_eq_left x.adj]
  order s := s.toList
  order_nodup s := s.nodup_toList
  mem_order _ _ := Finset.mem_toList

/-- The identifier of the node of kind `k` of a dart. -/
def idx (k : Kind) (x : N.G.Dart) : W := e (x.fst, x.snd, k)

/-- The dual network: the expansion with all remaining identifiers as pendant nodes. -/
noncomputable def dualNet : Net W := padNet (xPad N e) N.xNet

variable {N e}

theorem dualNet_diam {D : ℕ} (hD : N.DiamLE D) : (dualNet N e).DiamLE (5 * D + 6) :=
  padNet_diam (D := 5 * D + 4) (N.xNet_diam hD)

/-- The dual network of a connected planar network is planar. -/
theorem dualNet_planar (hP : N.toRot.Planar) (hN : ∀ v, ∃ u, N.G.Adj v u) {D : ℕ} (hD : N.DiamLE D)
    (hc : N.toRot.Connected) : (dualNet N e).toRot.Planar :=
  padNet_planar (xPad N e) (N.xNet_noIso hN) (N.xNet_planar hP hN hD hc) (N.xNet_connected hD hc)
    (N.xNet_diam hD)

omit [Fintype W] [DecidableEq W] in
private theorem xPad_real_of_adj {v i : V} (h : N.G.Adj v i) (k : Kind) :
    (xPad N e).ι ((xPad N e).back (e (v, i, k))) = e (v, i, k) := by
  have : (xPad N e).back (e (v, i, k)) = node k ⟨(v, i), h⟩ := by
    show xBack N (e.symm (e (v, i, k))) = _
    rw [Equiv.symm_apply_apply, xBack]
    exact dite_eq_left h
  rw [this]
  rfl

omit [Fintype W] [DecidableEq W] in
private theorem xPad_back_of_not_adj {v i : V} (h : ¬ N.G.Adj v i) (k : Kind) :
    (xPad N e).back (e (v, i, k)) = center v := by
  show xBack N (e.symm (e (v, i, k))) = _
  rw [Equiv.symm_apply_apply, xBack]
  exact dite_eq_right h

private theorem xPad_extras_node (k : Kind) (x : N.G.Dart) : (xPad N e).extras (node k x) = ∅ := by
  ext a
  simp only [PadMap.mem_extras, Finset.notMem_empty, iff_false, not_and]
  intro ha hb
  obtain ⟨⟨v, i, l⟩, rfl⟩ := e.surjective a
  by_cases h : N.G.Adj v i
  · exact ha (xPad_real_of_adj h l).symm
  · rw [xPad_back_of_not_adj h] at hb
    cases hb

/-- The identifiers at a node that hang at its centre. -/
def extrasAt (e : V × V × Kind ≃ W) (v : V) (L : List V) : Finset W :=
  Finset.univ.filter fun a => (e.symm a).1 = v ∧ (e.symm a).2.1 ∉ L ∧
    ¬ ((e.symm a).2.1 = v ∧ (e.symm a).2.2 = corner)

private theorem xPad_extras_center (v : V) :
    (xPad N e).extras (center v) = extrasAt e v (N.rotList v) := by
  ext a
  simp only [PadMap.mem_extras, extrasAt, Finset.mem_filter, Finset.mem_univ, true_and]
  obtain ⟨⟨u, i, l⟩, rfl⟩ := e.surjective a
  simp only [Equiv.symm_apply_apply, N.mem_rotList]
  by_cases h : N.G.Adj u i
  · have h1 := xPad_real_of_adj (e := e) h l
    constructor
    · rintro ⟨h2, -⟩
      exact absurd h1.symm h2
    · rintro ⟨rfl, h2, -⟩
      exact absurd h h2
  · rw [xPad_back_of_not_adj h]
    have hreal : (xPad N e).IsReal (e (u, i, l)) ↔ (i = u ∧ l = corner) := by
      show e (u, i, l) = (xPad N e).ι ((xPad N e).back (e (u, i, l))) ↔ _
      rw [xPad_back_of_not_adj h]
      show e (u, i, l) = e (u, u, corner) ↔ _
      simp [e.injective.eq_iff]
    rw [hreal]
    constructor
    · rintro ⟨h2, h3⟩
      cases h3
      exact ⟨rfl, h, h2⟩
    · rintro ⟨rfl, -, h2⟩
      exact ⟨h2, rfl⟩

/-- The rotation list of an identifier, as its host `v` computes it from its own rotation list `L`. -/
noncomputable def vRot (e : V × V × Kind ≃ W) (v : V) (L : List V) (i : V) (k : Kind) : List W :=
  if i ∈ L then
    match k with
    | corner => [e (v, v, corner), e (v, i, m1), e (v, i, r1), e (v, L.formPerm i, r2),
        e (v, L.formPerm i, m2)]
    | m1 => [e (v, i, corner), e (v, i, m2)]
    | m2 => [e (v, i, m1), e (v, L.formPerm.symm i, corner)]
    | r1 => [e (v, i, corner), e (i, v, r2)]
    | r2 => [e (i, v, r1), e (v, L.formPerm.symm i, corner)]
  else if i = v ∧ k = corner then
    L.map (fun u => e (v, u, corner)) ++ (extrasAt e v L).toList
  else [e (v, v, corner)]

/-- **The host knows the rotation lists.** -/
theorem dualNet_rotList (v i : V) (k : Kind) :
    (dualNet N e).rotList (e (v, i, k)) = vRot e v (N.rotList v) i k := by
  show padList (xPad N e) N.xNet (e (v, i, k)) = _
  by_cases h : N.G.Adj v i
  · let x : N.G.Dart := ⟨(v, i), h⟩
    have ha : e (v, i, k) = (xPad N e).ι (node k x) := rfl
    have hi : i ∈ N.rotList v := (N.mem_rotList _ _).2 h
    rw [ha, padList_ι, xPad_extras_node, PadMap.order_empty, List.append_nil]
    unfold vRot
    rw [ite_eq_left hi]
    cases k <;> rfl
  · have hi : i ∉ N.rotList v := fun hi => h ((N.mem_rotList _ _).1 hi)
    by_cases hk : i = v ∧ k = corner
    · obtain ⟨rfl, rfl⟩ := hk
      have ha : e (i, i, corner) = (xPad N e).ι (center i) := rfl
      rw [ha, padList_ι, xPad_extras_center]
      unfold vRot
      rw [ite_eq_right hi, ite_eq_left ⟨rfl, rfl⟩]
      congr 1
      simp only [Net.xNet, Net.xList, Net.dartsAt, List.map_map]
      conv_rhs => rw [← List.attach_map_subtype_val (N.rotList i)]
      rw [List.map_map]
      rfl
    · have hreal : ¬ (xPad N e).IsReal (e (v, i, k)) := by
        intro hr
        have hr' : e (v, i, k) = (xPad N e).ι ((xPad N e).back (e (v, i, k))) := hr
        rw [xPad_back_of_not_adj h] at hr'
        have := e.injective hr'
        simp only [Prod.mk.injEq] at this
        exact hk ⟨this.2.1, this.2.2⟩
      rw [padList_of_not hreal, xPad_back_of_not_adj h]
      unfold vRot
      rw [ite_eq_right hi, ite_eq_right hk]
      rfl

/-! ### The arcs -/

/-- The weight of an arc between two kinds of nodes. -/
def kindW (y : ℤ) : Kind → Kind → Option ℤ
  | corner, m1 => some y
  | m1, m2 => some 0
  | m2, corner => some 0
  | corner, r1 => some 0
  | r1, corner => some 0
  | r1, r2 => some 0
  | r2, r1 => some 0
  | r2, corner => some 0
  | corner, r2 => some 0
  | _, _ => none

theorem kindW_cases {y x : ℤ} {k l : Kind} (h : kindW y k l = some x) :
    (k = corner ∧ l = m1 ∧ x = y) ∨ (x = 0 ∧ ∀ y', kindW y' k l = some 0) := by
  cases k <;> cases l <;> simp_all [kindW]

/-- The arcs of the dual network. Centres have no arcs. -/
def dualW (e : V × V × Kind ≃ W) (g : V → V → ℤ) (a b : W) : Option ℤ :=
  if (e.symm a).2.1 = (e.symm a).1 ∨ (e.symm b).2.1 = (e.symm b).1 then none
  else kindW (g (e.symm a).1 (e.symm a).2.1) (e.symm a).2.2 (e.symm b).2.2

variable (g : V → V → ℤ)

omit [Fintype W] [DecidableEq W] in
theorem dualW_idx (k l : Kind) (x y : N.G.Dart) :
    dualW e g (idx N e k x) (idx N e l y) = kindW (g x.fst x.snd) k l := by
  have hx : x.snd ≠ x.fst := x.adj.ne'
  have hy : y.snd ≠ y.fst := y.adj.ne'
  simp [dualW, idx, hx, hy]

theorem adj_idx {k l : Kind} {x y : N.G.Dart} (h : node l y ∈ N.xList (node k x)) :
    (dualNet N e).G.Adj (idx N e k x) (idx N e l y) :=
  padNet_adj_ι (P := xPad N e) (N₀ := N.xNet) h

variable {g}

variable (N e g) in
/-- The arcs of the dual network. -/
inductive DualArc : W → W → ℤ → Prop
  | cost (x : N.G.Dart) : DualArc (idx N e corner x) (idx N e m1 x) (g x.fst x.snd)
  | m12 (x : N.G.Dart) : DualArc (idx N e m1 x) (idx N e m2 x) 0
  | m2c (x : N.G.Dart) : DualArc (idx N e m2 x) (idx N e corner (N.rotPerm.symm x)) 0
  | cr1 (x : N.G.Dart) : DualArc (idx N e corner x) (idx N e r1 x) 0
  | r1c (x : N.G.Dart) : DualArc (idx N e r1 x) (idx N e corner x) 0
  | r12 (x : N.G.Dart) : DualArc (idx N e r1 x) (idx N e r2 x.symm) 0
  | r21 (x : N.G.Dart) : DualArc (idx N e r2 x) (idx N e r1 x.symm) 0
  | r2c (x : N.G.Dart) : DualArc (idx N e r2 x) (idx N e corner (N.rotPerm.symm x)) 0
  | cr2 (x : N.G.Dart) : DualArc (idx N e corner x) (idx N e r2 (N.rotPerm x)) 0

/-- **The arcs of the dual network.** -/
theorem dual_arc {a b : W} {y : ℤ} (hab : (dualNet N e).G.Adj a b) (hw : dualW e g a b = some y) :
    DualArc N e g a b y := by
  have hnone : ∀ c v, dualW e g c (e (v, v, corner)) ≠ some y := fun c v h => by
    simp [dualW] at h
  have hnone' : ∀ c v, dualW e g (e (v, v, corner)) c ≠ some y := fun c v h => by
    simp [dualW] at h
  have hab' : b ∈ padList (xPad N e) N.xNet a := hab
  by_cases ha : (xPad N e).IsReal a
  · obtain ⟨p, rfl⟩ : ∃ p, a = (xPad N e).ι p := ⟨_, ha⟩
    rw [padList_ι, List.mem_append] at hab'
    cases p with
    | center v => exact absurd hw (hnone' _ v)
    | node k x =>
      rcases hab' with hb | hb
      · obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hb
        cases q with
        | center v => exact absurd hw (hnone _ v)
        | node l z =>
          have hw' : kindW (g x.fst x.snd) k l = some y := by
            rw [← dualW_idx]
            exact hw
          have hl : (node l z : XNode V N.G.Dart) ∈ N.xList (node k x) := hq
          show DualArc N e g (idx N e k x) (idx N e l z) y
          cases k <;> cases l <;> simp [Net.xList] at hl <;> simp [kindW] at hw'
          all_goals subst hl
          all_goals subst hw'
          · exact .cost _
          · exact .cr1 _
          · exact .cr2 _
          · exact .m12 _
          · exact .m2c _
          · exact .r1c _
          · exact .r12 _
          · exact .r2c _
          · exact .r21 _
      · rw [xPad_extras_node, PadMap.order_empty] at hb
        simp at hb
  · rw [padList_of_not ha, List.mem_singleton] at hab'
    subst hab'
    obtain ⟨⟨v, i, l⟩, rfl⟩ := e.surjective a
    by_cases h : N.G.Adj v i
    · exact absurd (xPad_real_of_adj h l).symm ha
    · rw [xPad_back_of_not_adj h] at hw
      exact absurd hw (hnone _ v)

/-- Arcs of bounded weight. -/
theorem dualW_valid {U : ℕ} (h : ∀ a b, N.G.Adj a b → |g a b| ≤ U) :
    (dualNet N e).NegValid U (dualW e g) := by
  intro a b hab x hx
  cases dual_arc hab hx with
  | cost d => exact h _ _ d.adj
  | _ => simp

/-! ### Duality: no negative cycle -/

/-- The potential of a node of the expansion. -/
private def potOf (π : N.G.Dart → ℤ) : XNode V N.G.Dart → ℤ
  | center _ => 0
  | node corner x => - π x
  | node m1 x => - π (N.rotPerm.symm x)
  | node m2 x => - π (N.rotPerm.symm x)
  | node r1 x => - π x
  | node r2 x => - π (N.rotPerm.symm x)

/-- A potential on the darts that is constant on faces and bounded by the costs across darts rules out
negative cycles. -/
theorem no_negCycle (π : N.G.Dart → ℤ) (hf : ∀ x, π (N.rotPerm.symm x.symm) = π x)
    (hc : ∀ y, π (N.rotPerm.symm y) - π y ≤ g y.fst y.snd) :
    ¬ (dualNet N e).HasNegCycle (dualW e g) := by
  rintro ⟨a, y, hw, hy⟩
  let pot : W → ℤ := fun a => potOf π ((xPad N e).back a)
  have hpot : ∀ k x, pot (idx N e k x) = potOf π (node k x) := fun k x => by
    show potOf π ((xPad N e).back ((xPad N e).ι (node k x))) = _
    rw [PadMap.back_ι]
  have key := WalkZ.pot_le_of_adj pot (fun a b x hab hx => ?_) hw
  · omega
  · cases dual_arc hab hx with
    | cost d =>
      rw [hpot, hpot]
      have := hc d
      simp only [potOf]
      omega
    | m12 d =>
      rw [hpot, hpot]
      simp [potOf]
    | m2c d =>
      rw [hpot, hpot]
      simp [potOf]
    | cr1 d =>
      rw [hpot, hpot]
      simp [potOf]
    | r1c d =>
      rw [hpot, hpot]
      simp [potOf]
    | r12 d =>
      rw [hpot, hpot]
      simp [potOf, hf d]
    | r21 d =>
      rw [hpot, hpot]
      have := hf d.symm
      rw [SimpleGraph.Dart.symm_symm] at this
      simp [potOf, this]
    | r2c d =>
      rw [hpot, hpot]
      simp [potOf]
    | cr2 d =>
      rw [hpot, hpot]
      simp [potOf]

/-- A unit of flow from `s` to `t`. -/
structure UnitFlow (N : Net V) (s t : V) (σ : V → V → ℤ) : Prop where
  skew : ∀ a b, N.G.Adj a b → σ b a = - σ a b
  net : ∀ v, ∑ u ∈ N.G.neighborFinset v, σ v u = (if v = s then 1 else 0) - (if v = t then 1 else 0)
  bound : ∀ a b, N.G.Adj a b → |σ a b| ≤ 1

/-- The cost of a dart for the flow value `β`. -/
def flowCost (cap : V → V → ℕ) (σ : V → V → ℤ) (β : ℤ) (a b : V) : ℤ := cap a b - σ a b * β

variable {cap : V → V → ℕ} {s t : V} {σ : V → V → ℤ}

/-- **A flow of value `β` rules out negative cycles for the costs `c - β σ`.** -/
theorem no_negCycle_of_flow (hP : N.toRot.Planar) (hc : N.toRot.Connected) (hst : s ≠ t)
    (hσ : UnitFlow N s t σ) {f : V → V → ℤ} {β : ℤ} (hf : N.IsFlow cap s t f β) :
    ¬ (dualNet N e).HasNegCycle (dualW e (flowCost cap σ β)) := by
  let G : N.G.Dart → ℤ := fun y => f y.fst y.snd - β * σ y.fst y.snd
  have hnet : ∀ v, ∑ u ∈ N.G.neighborFinset v, (f v u - β * σ v u) = 0 := by
    have hval : ∀ v, ∑ u ∈ N.G.neighborFinset v, f v u =
        β * ((if v = s then 1 else 0) - (if v = t then 1 else 0)) := by
      have hne : ∀ v, v ≠ t → ∑ u ∈ N.G.neighborFinset v, f v u =
          β * ((if v = s then 1 else 0) - (if v = t then 1 else 0)) := by
        intro v hv
        by_cases h : v = s
        · subst h
          rw [hf.val, ite_eq_left rfl, ite_eq_right hv]
          ring
        · rw [hf.cons v h hv, ite_eq_right h, ite_eq_right hv]
          ring
      intro v
      by_cases hv : v = t
      · subst hv
        have htot := N.sum_skew f hf.skew
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ v)] at htot
        have hrest : ∑ x ∈ Finset.univ.erase v, ∑ u ∈ N.G.neighborFinset x, f x u = β := by
          rw [Finset.sum_congr rfl fun x hx => hne x (Finset.ne_of_mem_erase hx)]
          rw [← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_ite_eq' , ite_eq_left]
          · have : ∑ x ∈ Finset.univ.erase v, (if x = v then (1 : ℤ) else 0) = 0 :=
              Finset.sum_eq_zero fun x hx => ite_eq_right (Finset.ne_of_mem_erase hx)
            rw [this]
            ring
          · exact Finset.mem_erase.2 ⟨hst, Finset.mem_univ _⟩
        rw [ite_eq_left rfl, ite_eq_right hst.symm]
        linarith
      · exact hne v hv
    intro v
    rw [Finset.sum_sub_distrib, hval v, ← Finset.mul_sum, hσ.net v]
    ring
  have hrev : ∀ y, G (N.toRot.rev y) = - G y := fun y => by
    show f y.snd y.fst - β * σ y.snd y.fst = - (f y.fst y.snd - β * σ y.fst y.snd)
    rw [hf.skew _ _ y.adj, hσ.skew _ _ y.adj]
    ring
  have hcons : ∀ q : N.G.Dart → ℚ, (∀ x, q (N.toRot.rot x) = q x) → ∑ y, q y * (G y : ℚ) = 0 := by
    intro q hq
    rw [← Finset.sum_fiberwise (s := Finset.univ) (g := fun y : N.G.Dart => y.fst)]
    refine Finset.sum_eq_zero fun v _ => ?_
    by_cases hne : (Finset.univ.filter fun y : N.G.Dart => y.fst = v).Nonempty
    · obtain ⟨y₀, hy₀⟩ := hne
      have hy₀' := (Finset.mem_filter.1 hy₀).2
      have h1 : ∀ y ∈ Finset.univ.filter (fun y : N.G.Dart => y.fst = v),
          q y * (G y : ℚ) = q y₀ * ((f v y.snd - β * σ v y.snd : ℤ) : ℚ) := by
        intro y hy
        have hyv := (Finset.mem_filter.1 hy).2
        rw [N.rot_invariant q hq y y₀ (hyv.trans hy₀'.symm)]
        show _ * ((f y.fst y.snd - β * σ y.fst y.snd : ℤ) : ℚ) = _
        rw [hyv]
      rw [Finset.sum_congr rfl h1, ← Finset.mul_sum, ← Int.cast_sum,
        N.sum_fiber v fun u => f v u - β * σ v u, hnet v]
      simp
    · rw [Finset.not_nonempty_iff_eq_empty.1 hne, Finset.sum_empty]
  obtain ⟨π, h1, h2⟩ := N.toRot.exists_face_potential hP hc G hrev hcons
  refine no_negCycle π h1 fun y => ?_
  rw [show π (N.rotPerm.symm y) - π y = G y from h2 y]
  have := hf.cap _ _ y.adj
  show f y.fst y.snd - β * σ y.fst y.snd ≤ (cap y.fst y.snd : ℤ) - σ y.fst y.snd * β
  linarith [mul_comm β (σ y.fst y.snd)]

/-! ### Duality: distances give flows -/

/-- Reindexing along the rotation at a node. -/
theorem sum_rot (v : V) (F : V → ℤ) :
    ∑ u ∈ N.G.neighborFinset v, F ((N.rotList v).formPerm.symm u) = ∑ u ∈ N.G.neighborFinset v, F u := by
  refine Equiv.Perm.sum_comp (N.rotList v).formPerm.symm _ F fun a ha => ?_
  have ha' : (N.rotList v).formPerm.symm a ≠ a := ha
  rw [Finset.mem_coe, N.neighborFinset_eq, List.mem_toFinset]
  by_contra hnot
  apply ha'
  rw [Equiv.symm_apply_eq]
  exact (List.formPerm_apply_of_notMem hnot).symm

/-- Values at the corners that are constant on faces and bounded by the costs give a flow of value
`β`. -/
theorem isFlow_of_dist (hst : s ≠ t) (hσ : UnitFlow N s t σ) {β : ℤ} (dv : V → V → ℤ)
    (hring : ∀ x : N.G.Dart, dv x.snd ((N.rotList x.snd).formPerm.symm x.fst) = dv x.fst x.snd)
    (hcost : ∀ y : N.G.Dart, dv y.fst ((N.rotList y.fst).formPerm.symm y.snd) ≤
      dv y.fst y.snd + flowCost cap σ β y.fst y.snd) :
    N.IsFlow cap s t (fun v u => dv v ((N.rotList v).formPerm.symm u) - dv v u + σ v u * β) β := by
  have hnet : ∀ v, ∑ u ∈ N.G.neighborFinset v,
      (dv v ((N.rotList v).formPerm.symm u) - dv v u + σ v u * β) =
      ((if v = s then 1 else 0) - (if v = t then 1 else 0)) * β := by
    intro v
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, sum_rot (N := N) v (dv v), sub_self, zero_add,
      ← Finset.sum_mul, hσ.net v]
  refine ⟨fun a b hab => ?_, fun a b hab => ?_, fun v hs ht => ?_, ?_⟩
  · have h1 := hring ⟨(a, b), hab⟩
    have h2 := hring ⟨(b, a), hab.symm⟩
    have h3 := hσ.skew a b hab
    simp only at h1 h2 ⊢
    rw [h1, h2, h3]
    ring
  · have := hcost ⟨(a, b), hab⟩
    simp only [flowCost] at this
    show dv a _ - dv a b + σ a b * β ≤ _
    linarith
  · rw [hnet v, ite_eq_right hs, ite_eq_right ht]
    ring
  · rw [hnet s, ite_eq_left rfl, ite_eq_right hst]
    ring

/-- The distance in an answer. -/
def readZ : Option (Option ℤ) → ℤ
  | some (some d) => d
  | _ => 0

private theorem walk_crown (x : N.G.Dart) : WalkZ (dualNet N e).G.Adj (dualW e g) (idx N e corner x)
    (idx N e corner (N.rotPerm.symm x)) (g x.fst x.snd) := by
  have h1 : (dualNet N e).G.Adj (idx N e corner x) (idx N e m1 x) := adj_idx (by simp [Net.xList])
  have h2 : (dualNet N e).G.Adj (idx N e m1 x) (idx N e m2 x) := adj_idx (by simp [Net.xList])
  have h3 : (dualNet N e).G.Adj (idx N e m2 x) (idx N e corner (N.rotPerm.symm x)) :=
    adj_idx (by simp [Net.xList])
  have w1 := dualW_idx (N := N) (e := e) g corner m1 x x
  have w2 := dualW_idx (N := N) (e := e) g m1 m2 x x
  have w3 := dualW_idx (N := N) (e := e) g m2 corner x (N.rotPerm.symm x)
  simpa using WalkZ.cons h1 w1 (WalkZ.cons h2 w2 (WalkZ.cons h3 w3 (.nil _)))

private theorem walk_ring (x : N.G.Dart) : WalkZ (dualNet N e).G.Adj (dualW e g) (idx N e corner x)
    (idx N e corner (N.rotPerm.symm x.symm)) 0 := by
  have h1 : (dualNet N e).G.Adj (idx N e corner x) (idx N e r1 x) := adj_idx (by simp [Net.xList])
  have h2 : (dualNet N e).G.Adj (idx N e r1 x) (idx N e r2 x.symm) := adj_idx (by simp [Net.xList])
  have h3 : (dualNet N e).G.Adj (idx N e r2 x.symm) (idx N e corner (N.rotPerm.symm x.symm)) :=
    adj_idx (by simp [Net.xList])
  have w1 := dualW_idx (N := N) (e := e) g corner r1 x x
  have w2 := dualW_idx (N := N) (e := e) g r1 r2 x x.symm
  have w3 := dualW_idx (N := N) (e := e) g r2 corner x.symm (N.rotPerm.symm x.symm)
  simpa using WalkZ.cons h1 w1 (WalkZ.cons h2 w2 (WalkZ.cons h3 w3 (.nil _)))

private theorem walk_ring' (x : N.G.Dart) : WalkZ (dualNet N e).G.Adj (dualW e g)
    (idx N e corner (N.rotPerm.symm x.symm)) (idx N e corner x) 0 := by
  have h1 : (dualNet N e).G.Adj (idx N e corner (N.rotPerm.symm x.symm)) (idx N e r2 x.symm) :=
    adj_idx (by simp [Net.xList])
  have h2 : (dualNet N e).G.Adj (idx N e r2 x.symm) (idx N e r1 x) := adj_idx (by simp [Net.xList])
  have h3 : (dualNet N e).G.Adj (idx N e r1 x) (idx N e corner x) := adj_idx (by simp [Net.xList])
  have w1 := dualW_idx (N := N) (e := e) g corner r2 (N.rotPerm.symm x.symm) x.symm
  have w2 := dualW_idx (N := N) (e := e) g r2 r1 x.symm x
  have w3 := dualW_idx (N := N) (e := e) g r1 corner x x
  simpa using WalkZ.cons h1 w1 (WalkZ.cons h2 w2 (WalkZ.cons h3 w3 (.nil _)))

/-- All corners can be reached from every corner. -/
theorem reach_corner (hc : N.toRot.Connected) (x₀ x : N.G.Dart) :
    ∃ y, WalkZ (dualNet N e).G.Adj (dualW e g) (idx N e corner x₀) (idx N e corner x) y := by
  have hsymm : ∀ x, (∃ y, WalkZ (dualNet N e).G.Adj (dualW e g) (idx N e corner x₀)
      (idx N e corner x) y) → ∃ y, WalkZ (dualNet N e).G.Adj (dualW e g) (idx N e corner x₀)
      (idx N e corner (N.rotPerm.symm x)) y := fun x ⟨y, hy⟩ => ⟨_, hy.trans (walk_crown x)⟩
  have hrot : ∀ x, (∃ y, WalkZ (dualNet N e).G.Adj (dualW e g) (idx N e corner x₀)
      (idx N e corner x) y) → ∃ y, WalkZ (dualNet N e).G.Adj (dualW e g) (idx N e corner x₀)
      (idx N e corner (N.rotPerm x)) y := by
    intro x hx
    have hs : (N.rotPerm⁻¹).SameCycle x (N.rotPerm x) := ⟨-1, by simp⟩
    obtain ⟨m, hm⟩ := hs.exists_nat_pow_eq
    rw [← hm]
    clear hm hs
    induction m with
    | zero => exact hx
    | succ m ih =>
      rw [pow_succ', Equiv.Perm.mul_apply]
      exact hsymm _ ih
  refine N.toRot.forall_of_closed hc (fun x => ∃ y, WalkZ (dualNet N e).G.Adj (dualW e g)
    (idx N e corner x₀) (idx N e corner x) y) (fun x hx => ?_) hrot
    (fun x ⟨y, hy⟩ => ⟨_, hy.trans (walk_ring x)⟩) (x₀ := x₀) ⟨0, .nil _⟩ x
  obtain ⟨y, hy⟩ := hx
  have h1 := hrot _ ⟨_, hy.trans (walk_ring x)⟩
  simpa using h1

/-- An answer `none` means a negative cycle. -/
theorem hasNegCycle_of_none {s₀ : W} {r : W → Option (Option ℤ)}
    (hS : (dualNet N e).NegSpec (dualW e g) s₀ r) {a : W} (ha : r a = none) :
    (dualNet N e).HasNegCycle (dualW e g) := by
  rcases hS with ⟨h, -⟩ | ⟨-, h⟩
  · exact h
  · rcases h a with ⟨h1, -⟩ | ⟨d, h1, -⟩ <;> simp [ha] at h1

/-- **Distances give a flow.** If the answer is not `none`, the distances at the corners give a flow of
value `β`. -/
theorem isFlow_of_spec (hc : N.toRot.Connected) (hst : s ≠ t) (hσ : UnitFlow N s t σ) {β : ℤ}
    {x₀ : N.G.Dart} {r : W → Option (Option ℤ)}
    (hS : (dualNet N e).NegSpec (dualW e (flowCost cap σ β)) (idx N e corner x₀) r) {a₀ : W}
    (ha₀ : r a₀ ≠ none) :
    N.IsFlow cap s t (fun v u => readZ (r (e (v, (N.rotList v).formPerm.symm u, corner))) -
      readZ (r (e (v, u, corner))) + σ v u * β) β := by
  rcases hS with ⟨-, h⟩ | ⟨-, hall⟩
  · exact absurd (h a₀) ha₀
  have hleast : ∀ x : N.G.Dart, IsLeast {y | WalkZ (dualNet N e).G.Adj (dualW e (flowCost cap σ β))
      (idx N e corner x₀) (idx N e corner x) y} (readZ (r (idx N e corner x))) := by
    intro x
    rcases hall (idx N e corner x) with ⟨-, hno⟩ | ⟨d, h1, h2⟩
    · obtain ⟨y, hy⟩ := reach_corner (e := e) (g := flowCost cap σ β) hc x₀ x
      exact absurd hy (hno y)
    · rw [h1]
      exact h2
  refine isFlow_of_dist hst hσ (fun v i => readZ (r (e (v, i, corner)))) (fun x => ?_) (fun y => ?_)
  · have h1 := (hleast (N.rotPerm.symm x.symm)).2 ((hleast x).1.trans (walk_ring x))
    have h2 := (hleast x).2 ((hleast (N.rotPerm.symm x.symm)).1.trans (walk_ring' x))
    rw [add_zero] at h1 h2
    exact le_antisymm h1 h2
  · exact (hleast (N.rotPerm.symm y)).2 ((hleast y).1.trans (walk_crown y))

/-! ### Monotonicity -/

omit [Fintype V] [Fintype W] [DecidableEq W] in
private theorem arc_split {β β' : ℤ} {a b : W} {x : ℤ}
    (h : dualW e (flowCost cap σ β) a b = some x) :
    ∃ C S : ℤ, 0 ≤ C ∧ x = C - β * S ∧ dualW e (flowCost cap σ β') a b = some (C - β' * S) := by
  unfold dualW at h ⊢
  split_ifs at h ⊢
  rcases kindW_cases h with ⟨hk, hl, hx⟩ | ⟨hx, hall⟩
  · refine ⟨cap (e.symm a).1 (e.symm a).2.1, σ (e.symm a).1 (e.symm a).2.1, by positivity, ?_, ?_⟩
    · rw [hx, flowCost]
      ring
    · rw [hk, hl]
      simp only [kindW, flowCost]
      congr 1
      ring
  · exact ⟨0, 0, le_rfl, by simp [hx], by simp [hall]⟩

private theorem walk_split {β β' : ℤ} {a b : W} {y : ℤ}
    (h : WalkZ (dualNet N e).G.Adj (dualW e (flowCost cap σ β)) a b y) :
    ∃ C S : ℤ, 0 ≤ C ∧ y = C - β * S ∧
      WalkZ (dualNet N e).G.Adj (dualW e (flowCost cap σ β')) a b (C - β' * S) := by
  induction h with
  | nil a => exact ⟨0, 0, le_rfl, by simp, by simpa using .nil a⟩
  | cons hab hw _ ih =>
    obtain ⟨C, S, hC, hy, hp⟩ := ih
    obtain ⟨C₀, S₀, hC₀, hx, hw'⟩ := arc_split (β' := β') hw
    refine ⟨C₀ + C, S₀ + S, by omega, by rw [hx, hy]; ring, ?_⟩
    have := WalkZ.cons hab hw' hp
    convert this using 1
    ring

/-- A negative cycle for `β ≥ 0` stays negative for all larger values. -/
theorem hasNegCycle_mono {β β' : ℤ} (h0 : 0 ≤ β) (hββ : β ≤ β')
    (h : (dualNet N e).HasNegCycle (dualW e (flowCost cap σ β))) :
    (dualNet N e).HasNegCycle (dualW e (flowCost cap σ β')) := by
  obtain ⟨a, y, hw, hy⟩ := h
  obtain ⟨C, S, hC, rfl, hp⟩ := walk_split (β' := β') hw
  refine ⟨a, _, hp, ?_⟩
  have hS : 0 < S := by
    by_contra hS
    have : β * S ≤ 0 := mul_nonpos_of_nonneg_of_nonpos h0 (by omega)
    omega
  nlinarith

/-! ### What a host computes -/

omit [Fintype V] [DecidableEq V] [Fintype W] in
theorem kindW_indep {k : Kind} (hk : k ≠ m1) (y y' : ℤ) (l : Kind) : kindW y l k = kindW y' l k := by
  cases l <;> cases k <;> first | rfl | exact absurd rfl hk

/-- The input of an identifier `a`, as its host `v` computes it, from its rotation list `L`, the costs
`gv` of its darts and whether it is the source. -/
noncomputable def vNegIn (e : V × V × Kind ≃ W) (v : V) (L : List V) (gv : V → ℤ) (src : Bool) (a : W) :
    NegIn W where
  nbrs := vRot e v L (e.symm a).2.1 (e.symm a).2.2
  wOut b := if b ∈ vRot e v L (e.symm a).2.1 (e.symm a).2.2 then dualW e (fun _ => gv) a b else none
  wIn b := if b ∈ vRot e v L (e.symm a).2.1 (e.symm a).2.2 then dualW e (fun _ => gv) b a else none
  isSource := src && decide ((e.symm a).2.1 = L.headD v ∧ (e.symm a).2.2 = corner)

omit [Fintype V] [DecidableEq W] in
/-- All identifiers in the list of a node of kind `m1` are at its host. -/
private theorem vRot_m1_host {v i : V} {L : List V} {b : W} (h : b ∈ vRot e v L i m1) :
    (e.symm b).1 = v := by
  unfold vRot at h
  split_ifs at h with h1 h2
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl <;> simp
  · exact absurd h2.2 (by simp)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rw [h]
    simp

/-- **The host knows the input of an identifier.** -/
theorem negIn_eq (s : V) {v : V} {a : W} (ha : (e.symm a).1 = v) :
    (dualNet N e).negIn (dualW e g) (e (s, (N.rotList s).headD s, corner)) a =
      vNegIn e v (N.rotList v) (g v) (decide (v = s)) a := by
  obtain ⟨⟨u, i, k⟩, rfl⟩ := e.surjective a
  simp only [Equiv.symm_apply_apply] at ha
  subst ha
  have hl := dualNet_rotList (N := N) (e := e) u i k
  have hadj : ∀ b, (dualNet N e).G.Adj (e (u, i, k)) b ↔ b ∈ vRot e u (N.rotList u) i k := fun b => by
    rw [← hl]
    exact ((dualNet N e).mem_rotList _ _).symm
  simp only [Net.negIn, vNegIn, Equiv.symm_apply_apply]
  have h1 : (fun w => if (dualNet N e).G.Adj (e (u, i, k)) w then dualW e g (e (u, i, k)) w else none) =
      fun b => if b ∈ vRot e u (N.rotList u) i k then
        dualW e (fun _ => g u) (e (u, i, k)) b else none := by
    funext b
    by_cases h : (dualNet N e).G.Adj (e (u, i, k)) b
    · rw [ite_eq_left h, ite_eq_left ((hadj b).1 h)]
      simp [dualW]
    · rw [ite_eq_right h, ite_eq_right (fun x => h ((hadj b).2 x))]
  have h2 : (fun w => if (dualNet N e).G.Adj (e (u, i, k)) w then dualW e g w (e (u, i, k)) else none) =
      fun b => if b ∈ vRot e u (N.rotList u) i k then
        dualW e (fun _ => g u) b (e (u, i, k)) else none := by
    funext b
    by_cases h : (dualNet N e).G.Adj (e (u, i, k)) b
    · rw [ite_eq_left h, ite_eq_left ((hadj b).1 h)]
      unfold dualW
      simp only [Equiv.symm_apply_apply]
      split_ifs
      · rfl
      · by_cases hb : (e.symm b).1 = u
        · rw [hb]
        · have hk : k ≠ m1 := by
            rintro rfl
            exact hb (vRot_m1_host ((hadj b).1 h))
          exact kindW_indep hk _ _ _
    · rw [ite_eq_right h, ite_eq_right (fun x => h ((hadj b).2 x))]
  have h3 : decide (e (u, i, k) = e (s, (N.rotList s).headD s, corner)) =
      (decide (u = s) && decide (i = (N.rotList u).headD u ∧ k = corner)) := by
    by_cases hu : u = s
    · subst hu
      simp [e.injective.eq_iff]
    · simp [e.injective.eq_iff, hu]
  rw [h1, h2, h3, hl]

/-- The pairs of identifiers that exchange messages over the edge from `v` to `u`. -/
def crossId (e : V × V × Kind ≃ W) (v u : V) (j : Fin 2) : W × W :=
  if j = 0 then (e (v, u, r1), e (u, v, r2)) else (e (v, u, r2), e (u, v, r1))

/-- **Edges of the dual network between two hosts.** -/
theorem dual_adj_cross {b a : W} (h : (e.symm b).1 ≠ (e.symm a).1) :
    (dualNet N e).G.Adj b a ↔
      N.G.Adj (e.symm b).1 (e.symm a).1 ∧ ∃ j, crossId e (e.symm b).1 (e.symm a).1 j = (b, a) := by
  obtain ⟨⟨v, i, k⟩, rfl⟩ := e.surjective b
  simp only [Equiv.symm_apply_apply] at h ⊢
  have hmem : (dualNet N e).G.Adj (e (v, i, k)) a ↔ a ∈ vRot e v (N.rotList v) i k := by
    rw [← dualNet_rotList]
    exact ((dualNet N e).mem_rotList _ _).symm
  rw [hmem]
  constructor
  · intro ha
    unfold vRot at ha
    split_ifs at ha with h1 h2
    · have hadj : N.G.Adj v i := (N.mem_rotList _ _).1 h1
      cases k <;> simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
      · rcases ha with rfl | rfl | rfl | rfl | rfl <;> simp at h
      · rcases ha with rfl | rfl <;> simp at h
      · rcases ha with rfl | rfl <;> simp at h
      · rcases ha with rfl | rfl
        · simp at h
        · simp only [Equiv.symm_apply_apply]
          exact ⟨hadj, 0, by simp [crossId]⟩
      · rcases ha with rfl | rfl
        · simp only [Equiv.symm_apply_apply]
          exact ⟨hadj, 1, by simp [crossId]⟩
        · simp at h
    · exfalso
      obtain ⟨rfl, rfl⟩ := h2
      rcases List.mem_append.1 ha with ha | ha
      · obtain ⟨u, -, rfl⟩ := List.mem_map.1 ha
        simp at h
      · have := (Finset.mem_filter.1 (Finset.mem_toList.1 ha)).2.1
        exact h this.symm
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
      subst ha
      simp at h
  · rintro ⟨hadj, j, hj⟩
    have hi := (N.mem_rotList _ _).2 hadj
    have hb : (e (v, i, k)) = (crossId e v (e.symm a).1 j).1 := by rw [hj]
    have ha : a = (crossId e v (e.symm a).1 j).2 := by rw [hj]
    unfold crossId at hb ha
    by_cases hj0 : j = 0
    · subst hj0
      simp only [ite_true, e.injective.eq_iff, Prod.mk.injEq] at hb ha
      obtain ⟨-, rfl, rfl⟩ := hb
      unfold vRot
      rw [ite_eq_left hi]
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      exact Or.inr ha
    · rw [ite_eq_right hj0] at hb ha
      simp only [e.injective.eq_iff, Prod.mk.injEq] at hb
      obtain ⟨-, rfl, rfl⟩ := hb
      unfold vRot
      rw [ite_eq_left hi]
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      exact Or.inl ha

end Ids

end SsspFlow.Congest
