import Dominators.Lemma3

/-!
# The gadgets of Section 4

`G` is an undirected graph, as a symmetric relation, with a vertex `v₀`.

* `sinkGraph`: flow-graph bridges. `sink_bridge_iff`: the edge `v → t_v` is a bridge iff `v` is reachable from
  `v₀`.
* `sbGraph`: strong bridges. `sb_bridge_iff`: the edge `v₀ → a_v` is a strong bridge iff `v` is connected to `v₀`.
  `sb_strongConn`, `sb_isolated`, `sb_no_change`: what happens in each case. `sb_edge_always_bridge`: this gadget
  fails for flow-graph bridges.
* `sapGraph`: strong articulation points. `sap_iff`: `b_v` is one iff `v` is connected to `v₀`.
  `sap_count_conn`, `sap_count_not`: the exact change of the count, and `sap_a_alone`, `sap_b_alone` when `v` is cut off.
* `orGraph`: the classical instance. `or_idom_no_edge`, `or_idom_edge`, `or_of_output`.
-/

namespace Dominators

universe u v

variable {V : Type u}

/-- In a symmetric relation, reachability is symmetric. -/
theorem Reach.symm_of {G : V → V → Prop} (hsym : ∀ a b, G a b → G b a) {x y : V} (h : Reach G x y) :
    Reach G y x := by
  obtain ⟨p⟩ := h
  induction p with
  | nil a => exact Reach.refl G a
  | cons hxy _ ih => exact ih.tail (hsym _ _ hxy)

/-- A symmetric graph is connected iff everything is reachable from one vertex. -/
theorem strongConn_iff_reach {G : V → V → Prop} (hsym : ∀ a b, G a b → G b a) (v₀ : V) :
    StrongConn G ↔ ∀ v, Reach G v₀ v :=
  ⟨fun h v => h v₀ v, fun h x y => (Reach.symm_of hsym (h x)).trans (h y)⟩

/-- The last edge of a walk to `z` that does not start at `z`. -/
theorem Reach.last_edge {E : V → V → Prop} {x z : V} (h : Reach E x z) (hne : x ≠ z) :
    ∃ w, Reach E x w ∧ E w z := by
  obtain ⟨p⟩ := h
  rcases p.firstArrival with h | ⟨w, q, hw, _⟩
  · exact absurd h hne
  · exact ⟨w, ⟨q⟩, hw⟩

/-! ## The sink gadget, for bridges of a flow graph -/

section Sink

/-- The graph `G` with a sink `t_v` and an edge `v → t_v` for each `v`. -/
def sinkGraph (G : V → V → Prop) : V ⊕ V → V ⊕ V → Prop
  | .inl a, .inl b => G a b
  | .inl a, .inr c => a = c
  | .inr _, _ => False

variable {G : V → V → Prop}

/-- From a vertex of `G`, a walk reaches only what `G` allows. -/
theorem sink_reach {a : V} {z : V ⊕ V} (h : Reach (sinkGraph G) (.inl a) z) :
    Sum.elim (Reach G a) (Reach G a) z := by
  refine Reach.mem_of_closed (S := Sum.elim (Reach G a) (Reach G a)) ?_ h (Reach.refl G a)
  rintro (x | x) (y | y) hx he
  · exact Reach.tail (E := G) hx he
  · have h' : x = y := he
    subst h'
    exact hx
  · exact he.elim
  · exact he.elim

theorem sink_reach_lift {a b : V} (h : Reach G a b) : Reach (sinkGraph G) (.inl a) (.inl b) :=
  Reach.map (F := sinkGraph G) Sum.inl (fun _ _ he => he) h

/-- **The sink gadget.** The edge `v → t_v` is a bridge of the flow graph from `v₀` iff `v` is reachable from
`v₀` in `G`. -/
theorem sink_bridge_iff (v₀ v : V) :
    IsBridge (sinkGraph G) (.inl v₀) (.inl v) (.inr v) ↔ Reach G v₀ v := by
  constructor
  · rintro ⟨_, h, _⟩
    exact sink_reach h
  · intro h
    have he : sinkGraph G (.inl v) (.inr v) := rfl
    refine ⟨he, (sink_reach_lift h).tail he, ?_⟩
    intro p
    rcases p.firstArrival with hne | ⟨w, _, hw, _, _, _, hl⟩
    · cases hne
    · cases w with
      | inl a =>
        have : a = v := hw
        subst this
        exact hl
      | inr c => exact hw.elim

/-- So the output of a bridge algorithm decides Connectivity. -/
theorem sink_connected_iff (hsym : ∀ a b, G a b → G b a) (v₀ : V) :
    StrongConn G ↔ ∀ v, IsBridge (sinkGraph G) (.inl v₀) (.inl v) (.inr v) := by
  rw [strongConn_iff_reach hsym v₀]
  simp only [sink_bridge_iff]

end Sink

/-! ## The gadget for strong bridges -/

section StrongBridge

/-- The new vertices `a_v`, one for each `v ≠ v₀`. -/
abbrev NewV (v₀ : V) := {v : V // v ≠ v₀}

/-- `G` bidirected, with `v₀ → a_v → v` for each `v ≠ v₀`. -/
def sbGraph (G : V → V → Prop) (v₀ : V) : V ⊕ NewV v₀ → V ⊕ NewV v₀ → Prop
  | .inl a, .inl b => G a b
  | .inl a, .inr _ => a = v₀
  | .inr c, .inl b => b = c.1
  | .inr _, .inr _ => False

variable {G : V → V → Prop} {v₀ : V}

theorem sb_lift {a b : V} (h : Reach G a b) : Reach (sbGraph G v₀) (.inl a) (.inl b) :=
  Reach.map (F := sbGraph G v₀) Sum.inl (fun _ _ he => he) h

/-- From a vertex not connected to `v₀`, a walk stays in `G`. -/
theorem sb_reach_of_not {x : V} (hx : ¬ Reach G x v₀) {z : V ⊕ NewV v₀}
    (h : Reach (sbGraph G v₀) (.inl x) z) : ∃ y, z = .inl y ∧ Reach G x y := by
  refine Reach.mem_of_closed (S := fun z => ∃ y, z = .inl y ∧ Reach G x y) ?_ h ⟨x, rfl, Reach.refl G x⟩
  rintro _ z' ⟨y, rfl, hy⟩ he
  cases z' with
  | inl b => exact ⟨b, rfl, hy.tail he⟩
  | inr c =>
    have : y = v₀ := he
    exact absurd (this ▸ hy) hx

/-- A walk from `a_v` goes through `v`. -/
theorem sb_reach_new {c : NewV v₀} {z : V ⊕ NewV v₀} (h : Reach (sbGraph G v₀) (.inr c) z) :
    z = .inr c ∨ Reach (sbGraph G v₀) (.inl c.1) z := by
  refine Reach.mem_of_closed (S := fun z => z = .inr c ∨ Reach (sbGraph G v₀) (.inl c.1) z) ?_ h (Or.inl rfl)
  rintro x y (rfl | hx) he
  · cases y with
    | inl b =>
      have : b = c.1 := he
      exact Or.inr (this ▸ Reach.refl _ _)
    | inr _ => exact he.elim
  · exact Or.inr (hx.tail he)

/-- The edges of the gadget. -/
theorem sb_edge_in (c : NewV v₀) : sbGraph G v₀ (.inl v₀) (.inr c) := rfl

theorem sb_edge_out (c : NewV v₀) : sbGraph G v₀ (.inr c) (.inl c.1) := rfl

/-- `a_v` reaches `v₀` iff `v` is connected to `v₀`. -/
theorem sb_new_reach_iff (hsym : ∀ a b, G a b → G b a) (c : NewV v₀) :
    Reach (sbGraph G v₀) (.inr c) (.inl v₀) ↔ Reach G v₀ c.1 := by
  constructor
  · intro h
    rcases sb_reach_new h with h1 | h1
    · cases h1
    · by_contra hn
      have hn' : ¬ Reach G c.1 v₀ := fun h2 => hn (Reach.symm_of hsym h2)
      obtain ⟨y, hy, h2⟩ := sb_reach_of_not hn' h1
      cases hy
      exact hn' h2
  · intro h
    exact Reach.head (sb_edge_out c) (sb_lift (Reach.symm_of hsym h))

/-- With a connected `G`, the whole gadget is one component. -/
theorem sb_strongConn (hsym : ∀ a b, G a b → G b a) (hC : StrongConn G) : StrongConn (sbGraph G v₀) := by
  have hto : ∀ z, Reach (sbGraph G v₀) (.inl v₀) z := by
    rintro (a | c)
    · exact sb_lift (hC v₀ a)
    · exact Reach.edge (sb_edge_in c)
  have hfrom : ∀ z, Reach (sbGraph G v₀) z (.inl v₀) := by
    rintro (a | c)
    · exact sb_lift (hC a v₀)
    · exact (sb_new_reach_iff hsym c).mpr (hC v₀ c.1)
  exact fun x y => (hfrom x).trans (hto y)

/-- `a_v` has one edge in. So removing it cuts `a_v` off from `v₀`. -/
theorem sb_not_reach_del (c : NewV v₀) :
    ¬ Reach (delEdge (sbGraph G v₀) (.inl v₀) (.inr c)) (.inl v₀) (.inr c) := by
  intro h
  have := Reach.mem_of_closed (S := fun z => z ≠ (.inr c : V ⊕ NewV v₀)) ?_ h (by simp)
  · exact this rfl
  · rintro x y hx ⟨he, hne⟩ rfl
    cases x with
    | inl a =>
      have : a = v₀ := he
      exact hne ⟨by rw [this], rfl⟩
    | inr _ => exact he.elim

variable [Finite V]

/-- **The strong-bridge gadget.** The edge `v₀ → a_v` is a strong bridge iff `v` is connected to `v₀`, whether or
not all of `G` is connected. -/
theorem sb_bridge_iff (hsym : ∀ a b, G a b → G b a) (c : NewV v₀) :
    IsStrongBridge (sbGraph G v₀) (.inl v₀) (.inr c) ↔ Reach G v₀ c.1 := by
  constructor
  · intro h
    exact (sb_new_reach_iff hsym c).mp h.mutual.2
  · intro h
    refine ⟨sb_edge_in c, (sccCount_delEdge_lt_iff _ _).mpr ⟨.inr c, .inl v₀, ?_, ?_⟩⟩
    · exact ⟨(sb_new_reach_iff hsym c).mpr h, Reach.edge (sb_edge_in c)⟩
    · exact fun hm => sb_not_reach_del c hm.2

omit [Finite V] in
/-- If `v` is not connected to `v₀`, then `a_v` is on no cycle: its component is itself. -/
theorem sb_isolated (hsym : ∀ a b, G a b → G b a) {c : NewV v₀} (hn : ¬ Reach G v₀ c.1)
    {x : V ⊕ NewV v₀} (hm : Mutual (sbGraph G v₀) (.inr c) x) : x = .inr c := by
  by_contra hne
  obtain ⟨w, hw, he⟩ := hm.2.last_edge hne
  cases w with
  | inl a =>
    have ha : a = v₀ := he
    subst ha
    exact hn ((sb_new_reach_iff hsym c).mp (hm.1.trans hw))
  | inr _ => exact he.elim

/-- If `v` is not connected to `v₀`, then removing `v₀ → a_v` changes no component. -/
theorem sb_no_change (hsym : ∀ a b, G a b → G b a) {c : NewV v₀} (hn : ¬ Reach G v₀ c.1)
    (x y : V ⊕ NewV v₀) :
    Mutual (sbGraph G v₀) x y ↔ Mutual (delEdge (sbGraph G v₀) (.inl v₀) (.inr c)) x y := by
  constructor
  · intro hm
    by_contra hno
    have hlt : sccCount (sbGraph G v₀) < sccCount (delEdge (sbGraph G v₀) (.inl v₀) (.inr c)) :=
      (sccCount_delEdge_lt_iff _ _).mpr ⟨x, y, hm, hno⟩
    exact hn ((sb_bridge_iff hsym c).mp ⟨sb_edge_in c, hlt⟩)
  · exact Mutual.mono (delEdge_le _ _ _)

/-- So the output of a strong-bridge algorithm decides Connectivity. -/
theorem sb_connected_iff (hsym : ∀ a b, G a b → G b a) :
    StrongConn G ↔ ∀ c : NewV v₀, IsStrongBridge (sbGraph G v₀) (.inl v₀) (.inr c) := by
  rw [strongConn_iff_reach hsym v₀]
  simp only [sb_bridge_iff hsym]
  constructor
  · exact fun h c => h c.1
  · intro h v
    by_cases hv : v = v₀
    · rw [hv]
      exact Reach.refl _ _
    · exact h ⟨v, hv⟩

omit [Finite V] in
/-- This gadget does not work for flow-graph bridges: `v₀ → a_v` is always a bridge from `v₀`, since it is the
only way into `a_v`. This is why `sinkGraph` exists. -/
theorem sb_edge_always_bridge (c : NewV v₀) :
    IsBridge (sbGraph G v₀) (.inl v₀) (.inl v₀) (.inr c) :=
  ⟨sb_edge_in c, Reach.edge (sb_edge_in c), onAllPaths_iff_not_reach_delEdge.mpr (sb_not_reach_del c)⟩

end StrongBridge

/-! ## The gadget for strong articulation points -/

section SAP

/-- `G` bidirected, with `v₀ → a_v → b_v → v` for each `v ≠ v₀`. Here `a_v` is `inr (inl v)` and `b_v` is
`inr (inr v)`. -/
def sapGraph (G : V → V → Prop) (v₀ : V) : V ⊕ (NewV v₀ ⊕ NewV v₀) → V ⊕ (NewV v₀ ⊕ NewV v₀) → Prop
  | .inl a, .inl b => G a b
  | .inl a, .inr (.inl _) => a = v₀
  | .inr (.inl c), .inr (.inr c') => c = c'
  | .inr (.inr c), .inl b => b = c.1
  | _, _ => False

variable {G : V → V → Prop} {v₀ : V}

/-- The vertex `a_v`. -/
abbrev aV (c : NewV v₀) : V ⊕ (NewV v₀ ⊕ NewV v₀) := .inr (.inl c)

/-- The vertex `b_v`. -/
abbrev bV (c : NewV v₀) : V ⊕ (NewV v₀ ⊕ NewV v₀) := .inr (.inr c)

theorem sap_lift {a b : V} (h : Reach G a b) : Reach (sapGraph G v₀) (.inl a) (.inl b) :=
  Reach.map (F := sapGraph G v₀) Sum.inl (fun _ _ he => he) h

theorem sap_edge1 (c : NewV v₀) : sapGraph G v₀ (.inl v₀) (aV c) := rfl

theorem sap_edge2 (c : NewV v₀) : sapGraph G v₀ (aV c) (bV c) := rfl

theorem sap_edge3 (c : NewV v₀) : sapGraph G v₀ (bV c) (.inl c.1) := rfl

theorem sap_reach_of_not {x : V} (hx : ¬ Reach G x v₀) {z : V ⊕ (NewV v₀ ⊕ NewV v₀)}
    (h : Reach (sapGraph G v₀) (.inl x) z) : ∃ y, z = .inl y ∧ Reach G x y := by
  refine Reach.mem_of_closed (S := fun z => ∃ y, z = .inl y ∧ Reach G x y) ?_ h ⟨x, rfl, Reach.refl G x⟩
  rintro _ z' ⟨y, rfl, hy⟩ he
  rcases z' with b | c | c
  · exact ⟨b, rfl, hy.tail he⟩
  · have : y = v₀ := he
    exact absurd (this ▸ hy) hx
  · exact he.elim

/-- A walk from `b_v` goes through `v`. -/
theorem sap_reach_b {c : NewV v₀} {z : V ⊕ (NewV v₀ ⊕ NewV v₀)} (h : Reach (sapGraph G v₀) (bV c) z) :
    z = bV c ∨ Reach (sapGraph G v₀) (.inl c.1) z := by
  refine Reach.mem_of_closed (S := fun z => z = bV c ∨ Reach (sapGraph G v₀) (.inl c.1) z) ?_ h (Or.inl rfl)
  rintro x y (rfl | hx) he
  · rcases y with b | d | d
    · have : b = c.1 := he
      exact Or.inr (this ▸ Reach.refl _ _)
    · exact he.elim
    · exact he.elim
  · exact Or.inr (hx.tail he)

/-- A walk from `a_v` goes through `b_v`. -/
theorem sap_reach_a {c : NewV v₀} {z : V ⊕ (NewV v₀ ⊕ NewV v₀)} (h : Reach (sapGraph G v₀) (aV c) z) :
    z = aV c ∨ Reach (sapGraph G v₀) (bV c) z := by
  refine Reach.mem_of_closed (S := fun z => z = aV c ∨ Reach (sapGraph G v₀) (bV c) z) ?_ h (Or.inl rfl)
  rintro x y (rfl | hx) he
  · rcases y with b | d | d
    · exact he.elim
    · exact he.elim
    · have : c = d := he
      exact Or.inr (this ▸ Reach.refl _ _)
  · exact Or.inr (hx.tail he)

/-- The only edge into `a_v` comes from `v₀`. -/
theorem sap_into_a {c : NewV v₀} {w : V ⊕ (NewV v₀ ⊕ NewV v₀)} (he : sapGraph G v₀ w (aV c)) : w = .inl v₀ := by
  rcases w with a | d | d
  · have : a = v₀ := he
    rw [this]
  · exact he.elim
  · exact he.elim

/-- The only edge into `b_v` comes from `a_v`. -/
theorem sap_into_b {c : NewV v₀} {w : V ⊕ (NewV v₀ ⊕ NewV v₀)} (he : sapGraph G v₀ w (bV c)) : w = aV c := by
  rcases w with a | d | d
  · exact he.elim
  · have : d = c := he
    rw [this]
  · exact he.elim

/-- A vertex that reaches `b_v` is `b_v`, or `a_v`, or reaches `v₀`. -/
theorem sap_reach_to_b {c : NewV v₀} {x : V ⊕ (NewV v₀ ⊕ NewV v₀)} (h : Reach (sapGraph G v₀) x (bV c)) :
    x = bV c ∨ x = aV c ∨ Reach (sapGraph G v₀) x (.inl v₀) := by
  by_cases hb : x = bV c
  · exact Or.inl hb
  obtain ⟨w, hw, he⟩ := h.last_edge hb
  rw [sap_into_b he] at hw
  by_cases ha : x = aV c
  · exact Or.inr (Or.inl ha)
  obtain ⟨w', hw', he'⟩ := hw.last_edge ha
  rw [sap_into_a he'] at hw'
  exact Or.inr (Or.inr hw')

/-- `b_v` reaches `v₀` iff `v` is connected to `v₀`. -/
theorem sap_b_reach_iff (hsym : ∀ a b, G a b → G b a) (c : NewV v₀) :
    Reach (sapGraph G v₀) (bV c) (.inl v₀) ↔ Reach G v₀ c.1 := by
  constructor
  · intro h
    rcases sap_reach_b h with h1 | h1
    · cases h1
    · by_contra hn
      have hn' : ¬ Reach G c.1 v₀ := fun h2 => hn (Reach.symm_of hsym h2)
      obtain ⟨y, hy, h2⟩ := sap_reach_of_not hn' h1
      cases hy
      exact hn' h2
  · intro h
    exact Reach.head (sap_edge3 c) (sap_lift (Reach.symm_of hsym h))

/-- If `v` is not connected to `v₀`, then `b_v` is alone in its component. -/
theorem sap_b_alone (hsym : ∀ a b, G a b → G b a) {c : NewV v₀} (hn : ¬ Reach G v₀ c.1)
    {x : V ⊕ (NewV v₀ ⊕ NewV v₀)} (hm : Mutual (sapGraph G v₀) x (bV c)) : x = bV c := by
  rcases sap_reach_to_b hm.1 with h | h | h
  · exact h
  · -- `x = a_v`: the walk from `b_v` back to `a_v` passes `v₀`
    subst h
    exfalso
    have hne : bV c ≠ aV c := by simp
    obtain ⟨w, hw, he⟩ := hm.2.last_edge hne
    rw [sap_into_a he] at hw
    exact hn ((sap_b_reach_iff hsym c).mp hw)
  · exfalso
    exact hn ((sap_b_reach_iff hsym c).mp (hm.2.trans h))

/-- If `v` is not connected to `v₀`, then `a_v` is alone in its component. -/
theorem sap_a_alone (hsym : ∀ a b, G a b → G b a) {c : NewV v₀} (hn : ¬ Reach G v₀ c.1)
    {x : V ⊕ (NewV v₀ ⊕ NewV v₀)} (hm : Mutual (sapGraph G v₀) x (aV c)) : x = aV c := by
  by_contra hne
  obtain ⟨w, hw, he⟩ := hm.1.last_edge hne
  rw [sap_into_a he] at hw
  have hb : Reach (sapGraph G v₀) (bV c) (.inl v₀) := by
    rcases sap_reach_a hm.2 with h | h
    · exact absurd h hne
    · exact h.trans hw
  exact hn ((sap_b_reach_iff hsym c).mp hb)

variable [Finite V]

/-- **The articulation-point gadget.** `b_v` is a strong articulation point iff `v` is connected to `v₀`, whether
or not all of `G` is connected. -/
theorem sap_iff (hsym : ∀ a b, G a b → G b a) (c : NewV v₀) :
    IsSAP (sapGraph G v₀) (bV c) ↔ Reach G v₀ c.1 := by
  constructor
  · intro h
    obtain ⟨x, _, hx, _, _⟩ := isSAP_iff_separates.mp h
    by_contra hn
    exact x.2 (sap_b_alone hsym hn hx)
  · intro h
    have hab : Reach (sapGraph G v₀) (aV c) (bV c) := Reach.edge (sap_edge2 c)
    have hba : Reach (sapGraph G v₀) (bV c) (aV c) :=
      ((sap_b_reach_iff hsym c).mpr h).tail (sap_edge1 c)
    have hne1 : aV c ≠ bV c := by simp
    have hne2 : (.inl v₀ : V ⊕ (NewV v₀ ⊕ NewV v₀)) ≠ bV c := by simp
    refine isSAP_iff_separates.mpr ⟨⟨aV c, hne1⟩, ⟨.inl v₀, hne2⟩, ⟨hab, hba⟩,
      ⟨(Reach.edge (sap_edge1 c)).trans hab, (sap_b_reach_iff hsym c).mpr h⟩, ?_⟩
    rintro ⟨h1, _⟩
    -- in `H - b_v`, `a_v` has no out-edge
    have hstay := Reach.mem_of_closed (E := delVertex (sapGraph G v₀) (bV c))
      (S := fun z => z.1 = aV c) ?_ h1 rfl
    · simp at hstay
    · rintro ⟨x, hx⟩ ⟨y, hy⟩ hxa he
      simp only at hxa
      subst hxa
      rcases y with b | d | d
      · exact he.elim
      · exact he.elim
      · have : c = d := he
        subst this
        exact absurd rfl hy

omit [Finite V] in
/-- With `v` connected to `v₀`, a walk between two old vertices can avoid `b_v`: the detour `v₀ → a_v → b_v → v`
can be replaced by a path of `G`. -/
theorem sap_reroute {c : NewV v₀} (hc : Reach G v₀ c.1)
    (x y : {z : V ⊕ (NewV v₀ ⊕ NewV v₀) // z ≠ bV c}) (hxa : x.1 ≠ aV c) (hya : y.1 ≠ aV c)
    (h : Reach (sapGraph G v₀) x.1 y.1) : Reach (delVertex (sapGraph G v₀) (bV c)) x y := by
  have hv₀ne : (.inl v₀ : V ⊕ (NewV v₀ ⊕ NewV v₀)) ≠ bV c := by simp
  have hvne : (.inl c.1 : V ⊕ (NewV v₀ ⊕ NewV v₀)) ≠ bV c := by simp
  have hane : aV c ≠ bV c := by simp
  have hGlift : ∀ {p q : V}, Reach G p q →
      Reach (delVertex (sapGraph G v₀) (bV c)) ⟨.inl p, by simp⟩ ⟨.inl q, by simp⟩ := by
    intro p q hpq
    exact Reach.map (F := delVertex (sapGraph G v₀) (bV c))
      (fun t : V => (⟨.inl t, by simp⟩ : {z : V ⊕ (NewV v₀ ⊕ NewV v₀) // z ≠ bV c}))
      (fun _ _ he => he) hpq
  -- the set of what `x` reaches in `H - b_v`, with `a_v` and `b_v` added once `x` reaches `v₀`
  let S : V ⊕ (NewV v₀ ⊕ NewV v₀) → Prop := fun z =>
    (∃ hz : z ≠ bV c, Reach (delVertex (sapGraph G v₀) (bV c)) x ⟨z, hz⟩) ∨
      ((z = aV c ∨ z = bV c) ∧ Reach (delVertex (sapGraph G v₀) (bV c)) x ⟨.inl v₀, hv₀ne⟩)
  have hS : S y.1 := by
    refine Reach.mem_of_closed (S := S) ?_ h (Or.inl ⟨x.2, Reach.refl _ _⟩)
    rintro p q (⟨hp, hxp⟩ | ⟨hp, hxv⟩) he
    · by_cases hq : q = bV c
      · -- entering `b_v` needs `a_v`, and entering `a_v` needs `v₀`
        subst hq
        have hpa : p = aV c := sap_into_b he
        subst hpa
        refine Or.inr ⟨Or.inr rfl, ?_⟩
        have hne : x ≠ ⟨aV c, hane⟩ := fun e => hxa (by rw [e])
        obtain ⟨w, hw, hwe⟩ := hxp.last_edge hne
        have hwv : w.1 = .inl v₀ := sap_into_a hwe
        have : w = ⟨.inl v₀, hv₀ne⟩ := Subtype.ext hwv
        rw [← this]
        exact hw
      · exact Or.inl ⟨hq, hxp.tail (E := delVertex (sapGraph G v₀) (bV c)) (z := ⟨q, hq⟩) he⟩
    · rcases hp with rfl | rfl
      · have hq : q = bV c := by
          rcases q with b | d | d
          · exact he.elim
          · exact he.elim
          · have : c = d := he
            rw [this]
        exact Or.inr ⟨Or.inr hq, hxv⟩
      · have hq : q = .inl c.1 := by
          rcases q with b | d | d
          · have : b = c.1 := he
            rw [this]
          · exact he.elim
          · exact he.elim
        subst hq
        exact Or.inl ⟨hvne, hxv.trans (hGlift hc)⟩
  rcases hS with ⟨_, h1⟩ | ⟨h1, _⟩
  · exact h1
  · rcases h1 with h1 | h1
    · exact absurd h1 hya
    · exact absurd h1 y.2

/-- **Not connected: removing `b_v` lowers the count by one.** -/
theorem sap_count_not (hsym : ∀ a b, G a b → G b a) {c : NewV v₀} (hn : ¬ Reach G v₀ c.1) :
    sccCount (delVertex (sapGraph G v₀) (bV c)) + 1 = sccCount (sapGraph G v₀) :=
  sccCount_delVertex_of_alone fun _ hx => sap_b_alone hsym hn hx

omit [Finite V] in
/-- In `H - b_v`, the vertex `a_v` has no out-edge, so it is alone. -/
theorem sap_a_stuck {c : NewV v₀} {x y : {z : V ⊕ (NewV v₀ ⊕ NewV v₀) // z ≠ bV c}} (hx : x.1 = aV c)
    (h : Reach (delVertex (sapGraph G v₀) (bV c)) x y) : y.1 = aV c := by
  refine Reach.mem_of_closed (E := delVertex (sapGraph G v₀) (bV c)) (S := fun z => z.1 = aV c) ?_ h hx
  rintro ⟨p, hp⟩ ⟨q, hq⟩ hpa he
  simp only at hpa
  subst hpa
  rcases q with b | d | d
  · exact he.elim
  · exact he.elim
  · have : c = d := he
    subst this
    exact absurd rfl hq

/-- **Connected: removing `b_v` raises the count by exactly one**, as `a_v` becomes its own component. -/
theorem sap_count_conn (hsym : ∀ a b, G a b → G b a) {c : NewV v₀} (hc : Reach G v₀ c.1) :
    sccCount (sapGraph G v₀) + 1 = sccCount (delVertex (sapGraph G v₀) (bV c)) := by
  classical
  let H := sapGraph G v₀
  let D := delVertex H (bV c)
  let f : {z : V ⊕ (NewV v₀ ⊕ NewV v₀) // z ≠ bV c} → Option (Quotient (sccSetoid H)) := fun x =>
    if x.1 = aV c then none else some (Quotient.mk'' x.1)
  have hf : ∀ x y, (sccSetoid D) x y → f x = f y := by
    intro x y hm
    have hxy : x.1 = aV c ↔ y.1 = aV c := ⟨fun h => sap_a_stuck h hm.1, fun h => sap_a_stuck h hm.2⟩
    by_cases hx : x.1 = aV c
    · simp only [f, hx, hxy.mp hx, ite_true]
    · have hy : y.1 ≠ aV c := fun h => hx (hxy.mpr h)
      simp only [f, hx, hy, ite_false]
      exact congrArg some (Quotient.sound' ⟨hm.1.of_delVertex, hm.2.of_delVertex⟩)
  let F : Quotient (sccSetoid D) → Option (Quotient (sccSetoid H)) := Quotient.lift f hf
  have hv₀ne : (.inl v₀ : V ⊕ (NewV v₀ ⊕ NewV v₀)) ≠ bV c := by simp
  have hbv₀ : Reach H (bV c) (.inl v₀) := (sap_b_reach_iff hsym c).mpr hc
  have hF : Function.Bijective F := by
    constructor
    · intro p q
      induction p using Quotient.inductionOn' with
      | h a =>
        induction q using Quotient.inductionOn' with
        | h b =>
          intro h
          have h' : f a = f b := h
          by_cases ha : a.1 = aV c
          · by_cases hb : b.1 = aV c
            · have : a = b := Subtype.ext (ha.trans hb.symm)
              rw [this]
            · simp [f, ha, hb] at h'
          · by_cases hb : b.1 = aV c
            · simp [f, ha, hb] at h'
            · simp only [f, ha, hb, ite_false, Option.some.injEq] at h'
              have hm : Mutual H a.1 b.1 := Quotient.exact' h'
              exact Quotient.sound'
                ⟨sap_reroute hc a b ha hb hm.1, sap_reroute hc b a hb ha hm.2⟩
    · intro o
      cases o with
      | none =>
        refine ⟨Quotient.mk'' ⟨aV c, by simp⟩, ?_⟩
        show f _ = none
        simp [f]
      | some q =>
        induction q using Quotient.inductionOn' with
        | h z =>
          by_cases hz : z = bV c ∨ z = aV c
          · refine ⟨Quotient.mk'' ⟨.inl v₀, hv₀ne⟩, ?_⟩
            show f _ = _
            have hne : (.inl v₀ : V ⊕ (NewV v₀ ⊕ NewV v₀)) ≠ aV c := by simp
            simp only [f, hne, ite_false]
            refine congrArg some (Quotient.sound' ?_)
            rcases hz with rfl | rfl
            · exact ⟨(Reach.edge (sap_edge1 c)).trans (Reach.edge (sap_edge2 c)), hbv₀⟩
            · exact ⟨Reach.edge (sap_edge1 c), (Reach.edge (sap_edge2 c)).trans hbv₀⟩
          · push Not at hz
            refine ⟨Quotient.mk'' ⟨z, hz.1⟩, ?_⟩
            show f _ = _
            simp [f, hz.2]
  have := Nat.card_eq_of_bijective F hF
  rw [Finite.card_option] at this
  exact this.symm

end SAP

/-! ## The classical instance for dominators -/

section OR

variable {X Y : Type*}

/-- The vertices: `r` is `inl false`, `u` is `inl true`, then `X` and `Y`. The edges: `r → u`, `r → x`, `u → y`,
and `x → y` where the hidden bit is set. -/
def orGraph (bits : X → Y → Bool) : Bool ⊕ (X ⊕ Y) → Bool ⊕ (X ⊕ Y) → Prop
  | .inl false, .inl true => True
  | .inl false, .inr (.inl _) => True
  | .inl true, .inr (.inr _) => True
  | .inr (.inl a), .inr (.inr b) => bits a b = true
  | _, _ => False

variable {bits : X → Y → Bool}

/-- The root of the instance. -/
abbrev orR : Bool ⊕ (X ⊕ Y) := .inl false

/-- The vertex `u` of the instance. -/
abbrev orU : Bool ⊕ (X ⊕ Y) := .inl true

/-- The vertex of `b ∈ Y`. -/
abbrev orV (b : Y) : Bool ⊕ (X ⊕ Y) := .inr (.inr b)

/-- The vertex of `a ∈ X`. -/
abbrev orX (a : X) : Bool ⊕ (X ⊕ Y) := .inr (.inl a)

/-- The walk `r → u → y`. -/
def orWalkU (bits : X → Y → Bool) (b : Y) : Walk (orGraph bits) orR (orV b) :=
  .cons (y := orU) trivial (.cons (y := orV b) trivial (.nil _))

/-- The walk `r → x → y`, if the hidden bit is set. -/
def orWalkX (a : X) (b : Y) (h : bits a b = true) : Walk (orGraph bits) orR (orV b) :=
  .cons (y := orX a) trivial (.cons (y := orV b) h (.nil _))

theorem orWalkU_support (bits : X → Y → Bool) (b : Y) :
    (orWalkU bits b).support = [orR, orU, orV b] := rfl

theorem orWalkX_support (a : X) (b : Y) (h : bits a b = true) :
    (orWalkX a b h).support = [orR, orX a, orV b] := rfl

/-- **If `y` has no hidden in-edge, then `idom(y) = u`.** -/
theorem or_idom_no_edge {b : Y} (hb : ∀ a, bits a b = false) : IsIdom (orGraph bits) orR orU (orV b) := by
  have hdom : Dominates (orGraph bits) orR orU (orV b) := by
    intro p
    rcases p.firstArrival with h | ⟨w, _, hw, _, _, _, hl⟩
    · cases h
    · rcases w with (_ | _) | a | c
      · exact hw.elim
      · exact (p.mem_support_of_mem_edges hl).1
      · have : bits a b = true := hw
        rw [hb a] at this
        cases this
      · exact hw.elim
  refine ⟨⟨orWalkU bits b⟩, by simp, hdom, ?_⟩
  intro d hdb hd
  have h := hd (orWalkU bits b)
  rw [orWalkU_support] at h
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl
  · exact Dominates.root _ _
  · exact Dominates.refl _ _
  · exact absurd rfl hdb

/-- **If `y` has a hidden in-edge, then `idom(y) = r`**: the paths through `u` and through `x` meet only at `r`. -/
theorem or_idom_edge {a : X} {b : Y} (hb : bits a b = true) : IsIdom (orGraph bits) orR orR (orV b) := by
  refine ⟨⟨orWalkU bits b⟩, by simp, Dominates.root _ _, ?_⟩
  intro d hdb hd
  have h1 := hd (orWalkU bits b)
  have h2 := hd (orWalkX a b hb)
  rw [orWalkU_support] at h1
  rw [orWalkX_support] at h2
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h1 h2
  rcases h1 with rfl | rfl | rfl
  · exact Dominates.refl _ _
  · simp at h2
  · exact absurd rfl hdb

/-- **The output determines OR.** If `out` is the immediate dominator table of the instance, then the OR of the
bits is true iff some `y` has `out y = r`. -/
theorem or_of_output {out : Bool ⊕ (X ⊕ Y) → Option (Bool ⊕ (X ⊕ Y))}
    (hout : ∀ u w, out w = some u ↔ IsIdom (orGraph bits) orR u w) :
    (∃ a b, bits a b = true) ↔ ∃ b, out (orV b) = some orR := by
  constructor
  · rintro ⟨a, b, h⟩
    exact ⟨b, (hout _ _).mpr (or_idom_edge h)⟩
  · rintro ⟨b, h⟩
    by_contra hno
    push Not at hno
    have hb : ∀ a, bits a b = false := fun a => by simpa using hno a b
    have h1 := (hout _ _).mp h
    have h2 := or_idom_no_edge hb
    have := h1.unique h2
    simp at this

end OR

end Dominators
