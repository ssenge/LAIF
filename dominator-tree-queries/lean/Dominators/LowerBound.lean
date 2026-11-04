import Dominators.Gadgets

/-!
# Lower bounds by reduction

A query to a gadget's adjacency matrix is one query to the input graph, or a constant. `QAlg.sim` and `DetAlg.sim`
turn an algorithm for the gadget into one for the input with the same number of queries, and this is proved on
the concrete models of `Model.lean`.

* Quantum, from the named hypothesis `DHHM_Thm23`: `dominators_lower_bound`, `bridges_lower_bound`,
  `strongBridges_lower_bound`, `saps_lower_bound`.
* Classical, from the named hypothesis `ClassicalConnectivity`: `classical_bridges_lower_bound`,
  `classical_strongBridges_lower_bound`, `classical_saps_lower_bound`.
* Classical, with no hypothesis: `or_lower_bound` proves the randomized bound for OR, and
  `classical_dominators_lower_bound` applies it to the instance of `orGraph`.
-/

open Finset

namespace Dominators

universe u

/-! ## Simulation -/

section Sim

variable {ι ι' : Type*}

/-- The input of the gadget, computed from the input of the graph. Each bit is one input bit or a constant. -/
def pull (q : ι' → ι ⊕ Bool) (x : ι → Bool) : ι' → Bool := fun i => bitVal x (q i)

variable {S β γ : Type*} [Fintype S] [DecidableEq S] {T : ℕ}

/-- Run an algorithm for the gadget on the graph, with the same unitaries, and decode its output. -/
def QAlg.sim (A : QAlg ι' Bool S β T) (q : ι' → ι ⊕ Bool) (dec : β → γ) : QAlg ι Bool S γ T where
  init := A.init
  U := A.U
  unitary := A.unitary
  query s := match A.query s with
    | .inl (i, g) =>
      match q i with
      | .inl j => .inl (j, g)
      | .inr b => .inr (g b)
    | .inr b => .inr b
  out s := dec (A.out s)

theorem QAlg.sim_val (A : QAlg ι' Bool S β T) (q : ι' → ι ⊕ Bool) (dec : β → γ) (x : ι → Bool) (s : S) :
    QueryTarget.val x ((A.sim q dec).query s) = QueryTarget.val (pull q x) (A.query s) := by
  simp only [QAlg.sim]
  cases A.query s with
  | inl p =>
    obtain ⟨i, g⟩ := p
    simp only [QueryTarget.val, pull]
    cases q i <;> rfl
  | inr b => rfl

theorem QAlg.sim_amp (A : QAlg ι' Bool S β T) (q : ι' → ι ⊕ Bool) (dec : β → γ) (x : ι → Bool) (t : ℕ) :
    (A.sim q dec).amp x t = A.amp (pull q x) t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    simp only [QAlg.amp, ih]
    have : ∀ s, (A.sim q dec).phase x s = A.phase (pull q x) s := by
      intro s
      simp only [QAlg.phase, QAlg.sim_val]
    simp only [this]
    rfl

theorem QAlg.prob_mono (A : QAlg ι Bool S β T) (x : ι → Bool) {P P' : β → Prop} (h : ∀ o, P o → P' o) :
    A.prob x P ≤ A.prob x P' := by
  classical
  unfold QAlg.prob
  refine Finset.sum_le_sum fun s _ => ?_
  by_cases hp : P (A.out s)
  · simp [hp, h _ hp]
  · simp only [hp, ite_false]
    split_ifs <;> positivity

/-- **The quantum reduction.** Same queries, same basis, and correct if the original is. -/
theorem QAlg.sim_solves (A : QAlg ι' Bool S β T) (q : ι' → ι ⊕ Bool) (dec : β → γ)
    {R' : (ι' → Bool) → β → Prop} {R : (ι → Bool) → γ → Prop} (hA : A.Solves R')
    (hR : ∀ x o, R' (pull q x) o → R x (dec o)) : (A.sim q dec).Solves R := by
  classical
  intro x
  refine (hA (pull q x)).trans ?_
  refine (A.prob_mono (pull q x) (P' := fun o => R x (dec o)) (hR x)).trans (le_of_eq ?_)
  simp only [QAlg.prob, QAlg.sim_amp]
  rfl

/-- The decision tree for the gadget, run on the graph. -/
def DetAlg.sim (A : DetAlg ι' β) (q : ι' → ι ⊕ Bool) (dec : β → γ) : DetAlg ι γ where
  query ans := match A.query ans with
    | .inl i => q i
    | .inr b => .inr b
  output ans := dec (A.output ans)

theorem DetAlg.sim_answers (A : DetAlg ι' β) (q : ι' → ι ⊕ Bool) (dec : β → γ) (x : ι → Bool) (t : ℕ) :
    (A.sim q dec).answers x t = A.answers (pull q x) t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    simp only [DetAlg.answers, ih]
    congr 2
    simp only [DetAlg.sim]
    cases A.query (A.answers (pull q x) t) <;> rfl

variable {Ω : Type*} [Fintype Ω]

/-- The randomized algorithm for the gadget, run on the graph. -/
def RandAlg.sim (A : RandAlg ι' β Ω) (q : ι' → ι ⊕ Bool) (dec : β → γ) : RandAlg ι γ Ω where
  p := A.p
  nonneg := A.nonneg
  sum_one := A.sum_one
  alg ω := (A.alg ω).sim q dec

/-- **The classical reduction.** -/
theorem RandAlg.sim_solves (A : RandAlg ι' β Ω) (q : ι' → ι ⊕ Bool) (dec : β → γ) {T : ℕ}
    {R' : (ι' → Bool) → β → Prop} {R : (ι → Bool) → γ → Prop} (hA : A.Solves T R')
    (hR : ∀ x o, R' (pull q x) o → R x (dec o)) : (A.sim q dec).Solves T R := by
  classical
  intro x
  refine (hA (pull q x)).trans ?_
  unfold RandAlg.prob
  refine Finset.sum_le_sum fun ω _ => ?_
  have hans : ((A.sim q dec).alg ω).answers x T = (A.alg ω).answers (pull q x) T :=
    DetAlg.sim_answers _ _ _ _ _
  simp only [hans]
  have hout : ((A.sim q dec).alg ω).output ((A.alg ω).answers (pull q x) T) =
      dec ((A.alg ω).output ((A.alg ω).answers (pull q x) T)) := rfl
  rw [hout]
  have hp : (A.sim q dec).p ω = A.p ω := rfl
  rw [hp]
  by_cases h : R' (pull q x) ((A.alg ω).output ((A.alg ω).answers (pull q x) T))
  · simp [h, hR x _ h]
  · simp only [h, ite_false]
    split_ifs
    · exact A.nonneg ω
    · exact le_rfl

end Sim

/-! ## The problems -/

section Problems

variable {W : Type*}

/-- The digraph of a bit matrix. -/
def gr (x : W × W → Bool) (u v : W) : Prop := x (u, v) = true

/-- The output is the table of immediate dominators from the root `r`. -/
def IdomAnswer (r : W) (x : W × W → Bool) (o : W → Option W) : Prop :=
  ∀ u w, o w = some u ↔ IsIdom (gr x) r u w

/-- The output is the set of bridges of the flow graph from `r`. -/
def BridgeAnswer (r : W) (x : W × W → Bool) (o : Finset (W × W)) : Prop :=
  ∀ u v, (u, v) ∈ o ↔ IsBridge (gr x) r u v

/-- The output is the set of strong bridges. -/
def StrongBridgeAnswer (x : W × W → Bool) (o : Finset (W × W)) : Prop :=
  ∀ u v, (u, v) ∈ o ↔ IsStrongBridge (gr x) u v

/-- The output is the set of strong articulation points. -/
def SAPAnswer (x : W × W → Bool) (o : Finset W) : Prop :=
  ∀ d, d ∈ o ↔ IsSAP (gr x) d

end Problems

/-! ## The query maps -/

section Maps

variable {n : ℕ}

/-- The bit of an undirected pair. A loop is constant false. -/
def ueIndex (a b : Fin n) : UEdge n ⊕ Bool :=
  if h : a < b then .inl ⟨(a, b), h⟩ else if h' : b < a then .inl ⟨(b, a), h'⟩ else .inr false

theorem ueIndex_iff (x : UEdge n → Bool) (a b : Fin n) : bitVal x (ueIndex a b) = true ↔ ugraph x a b := by
  unfold ueIndex ugraph
  by_cases h : a < b
  · have h' : ¬ b < a := lt_asymm h
    simp [h, h', bitVal]
  · by_cases h' : b < a
    · simp [h, h', bitVal]
    · simp [h, h', bitVal]

theorem ugraph_symm (x : UEdge n → Bool) (a b : Fin n) (h : ugraph x a b) : ugraph x b a := Or.symm h

/-- The bidirected graph. -/
def domQ (i : Fin n × Fin n) : UEdge n ⊕ Bool := ueIndex i.1 i.2

theorem gr_domQ (x : UEdge n → Bool) : gr (pull domQ x) = ugraph x := by
  funext a b
  exact propext (ueIndex_iff x a b)

/-- The sink gadget. -/
def sinkQ : (Fin n ⊕ Fin n) × (Fin n ⊕ Fin n) → UEdge n ⊕ Bool
  | (.inl a, .inl b) => ueIndex a b
  | (.inl a, .inr c) => .inr (decide (a = c))
  | (.inr _, _) => .inr false

theorem gr_sinkQ (x : UEdge n → Bool) : gr (pull sinkQ x) = sinkGraph (ugraph x) := by
  funext u v
  apply propext
  rcases u with a | a <;> rcases v with b | b
  · exact ueIndex_iff x a b
  · simp [gr, pull, sinkQ, bitVal, sinkGraph]
  · simp [gr, pull, sinkQ, bitVal, sinkGraph]
  · simp [gr, pull, sinkQ, bitVal, sinkGraph]

/-- The strong-bridge gadget. -/
def sbQ (v₀ : Fin n) : (Fin n ⊕ NewV v₀) × (Fin n ⊕ NewV v₀) → UEdge n ⊕ Bool
  | (.inl a, .inl b) => ueIndex a b
  | (.inl a, .inr _) => .inr (decide (a = v₀))
  | (.inr c, .inl b) => .inr (decide (b = c.1))
  | (.inr _, .inr _) => .inr false

theorem gr_sbQ (v₀ : Fin n) (x : UEdge n → Bool) : gr (pull (sbQ v₀) x) = sbGraph (ugraph x) v₀ := by
  funext u v
  apply propext
  rcases u with a | a <;> rcases v with b | b
  · exact ueIndex_iff x a b
  · simp [gr, pull, sbQ, bitVal, sbGraph]
  · simp [gr, pull, sbQ, bitVal, sbGraph]
  · simp [gr, pull, sbQ, bitVal, sbGraph]

/-- The articulation-point gadget. -/
def sapQ (v₀ : Fin n) :
    (Fin n ⊕ (NewV v₀ ⊕ NewV v₀)) × (Fin n ⊕ (NewV v₀ ⊕ NewV v₀)) → UEdge n ⊕ Bool
  | (.inl a, .inl b) => ueIndex a b
  | (.inl a, .inr (.inl _)) => .inr (decide (a = v₀))
  | (.inr (.inl c), .inr (.inr c')) => .inr (decide (c = c'))
  | (.inr (.inr c), .inl b) => .inr (decide (b = c.1))
  | _ => .inr false

theorem gr_sapQ (v₀ : Fin n) (x : UEdge n → Bool) : gr (pull (sapQ v₀) x) = sapGraph (ugraph x) v₀ := by
  funext u v
  apply propext
  rcases u with a | a | a <;> rcases v with b | b | b
  · exact ueIndex_iff x a b
  all_goals simp [gr, pull, sapQ, bitVal, sapGraph]

/-! ## Decoding Connectivity from each output -/

open Classical in
/-- All non-root vertices have an immediate dominator. -/
noncomputable def domDec (r : Fin n) (o : Fin n → Option (Fin n)) : Bool :=
  decide (∀ w, w ≠ r → (o w).isSome = true)

theorem domDec_spec (r : Fin n) (x : UEdge n → Bool) (o : Fin n → Option (Fin n))
    (h : IdomAnswer r (pull domQ x) o) : ConnAnswer x (domDec r o) := by
  unfold IdomAnswer at h
  rw [gr_domQ] at h
  unfold ConnAnswer domDec
  rw [decide_eq_true_iff, strongConn_iff_reach (ugraph_symm x) r]
  constructor
  · intro hs w
    by_cases hw : w = r
    · rw [hw]
      exact Reach.refl _ _
    · obtain ⟨u, hu⟩ := Option.isSome_iff_exists.mp (hs w hw)
      exact ((h u w).mp hu).1
  · intro hr w hw
    obtain ⟨u, hu⟩ := exists_idom (hr w) hw
    rw [(h u w).mpr hu]
    rfl

open Classical in
/-- All edges `v → t_v` are bridges. -/
noncomputable def sinkDec (o : Finset ((Fin n ⊕ Fin n) × (Fin n ⊕ Fin n))) : Bool :=
  decide (∀ v : Fin n, (.inl v, .inr v) ∈ o)

theorem sinkDec_spec (v₀ : Fin n) (x : UEdge n → Bool) (o : Finset ((Fin n ⊕ Fin n) × (Fin n ⊕ Fin n)))
    (h : BridgeAnswer (.inl v₀) (pull sinkQ x) o) : ConnAnswer x (sinkDec o) := by
  unfold BridgeAnswer at h
  rw [gr_sinkQ] at h
  unfold ConnAnswer sinkDec
  rw [decide_eq_true_iff, sink_connected_iff (ugraph_symm x) v₀]
  simp only [h]

open Classical in
/-- All edges `v₀ → a_v` are strong bridges. -/
noncomputable def sbDec (v₀ : Fin n) (o : Finset ((Fin n ⊕ NewV v₀) × (Fin n ⊕ NewV v₀))) : Bool :=
  decide (∀ c : NewV v₀, (.inl v₀, .inr c) ∈ o)

theorem sbDec_spec (v₀ : Fin n) (x : UEdge n → Bool) (o : Finset ((Fin n ⊕ NewV v₀) × (Fin n ⊕ NewV v₀)))
    (h : StrongBridgeAnswer (pull (sbQ v₀) x) o) : ConnAnswer x (sbDec v₀ o) := by
  unfold StrongBridgeAnswer at h
  rw [gr_sbQ] at h
  unfold ConnAnswer sbDec
  rw [decide_eq_true_iff, sb_connected_iff (v₀ := v₀) (ugraph_symm x)]
  simp only [h]

open Classical in
/-- All vertices `b_v` are strong articulation points. -/
noncomputable def sapDec (v₀ : Fin n) (o : Finset (Fin n ⊕ (NewV v₀ ⊕ NewV v₀))) : Bool :=
  decide (∀ c : NewV v₀, bV c ∈ o)

theorem sapDec_spec (v₀ : Fin n) (x : UEdge n → Bool) (o : Finset (Fin n ⊕ (NewV v₀ ⊕ NewV v₀)))
    (h : SAPAnswer (pull (sapQ v₀) x) o) : ConnAnswer x (sapDec v₀ o) := by
  unfold SAPAnswer at h
  rw [gr_sapQ] at h
  unfold ConnAnswer sapDec
  rw [decide_eq_true_iff, strongConn_iff_reach (ugraph_symm x) v₀]
  simp only [h, sap_iff (ugraph_symm x)]
  constructor
  · intro hc v
    by_cases hv : v = v₀
    · rw [hv]
      exact Reach.refl _ _
    · exact hc ⟨v, hv⟩
  · exact fun hc c => hc c.1

end Maps

/-! ## Quantum lower bounds, from quant-ph/0401091, Theorem 23 -/

/-- **Dominators need `Ω(n^{3/2})` quantum queries**, given `DHHM_Thm23`. The digraph has `n` vertices. -/
theorem dominators_lower_bound (h : DHHM_Thm23) :
    ∃ c : ℝ, 0 < c ∧ ∃ n₀ : ℕ, ∀ n, n₀ ≤ n → ∀ (r : Fin n) (S : Type) [Fintype S] [DecidableEq S] (T : ℕ)
      (A : QAlg (Fin n × Fin n) Bool S (Fin n → Option (Fin n)) T), A.Solves (IdomAnswer r) →
        c * (n : ℝ) ^ (3 / 2 : ℝ) ≤ T := by
  obtain ⟨c, hc, n₀, H⟩ := h
  refine ⟨c, hc, n₀, fun n hn r S _ _ T A hA => ?_⟩
  exact H n hn S T (A.sim domQ (domDec r)) (A.sim_solves _ _ hA (domDec_spec r))

/-- **Flow-graph bridges need `Ω(n^{3/2})` quantum queries**, given `DHHM_Thm23`. The gadget has `2n` vertices. -/
theorem bridges_lower_bound (h : DHHM_Thm23) :
    ∃ c : ℝ, 0 < c ∧ ∃ n₀ : ℕ, ∀ n, n₀ ≤ n → ∀ (v₀ : Fin n) (S : Type) [Fintype S] [DecidableEq S] (T : ℕ)
      (A : QAlg ((Fin n ⊕ Fin n) × (Fin n ⊕ Fin n)) Bool S (Finset ((Fin n ⊕ Fin n) × (Fin n ⊕ Fin n))) T),
        A.Solves (BridgeAnswer (.inl v₀)) → c * (n : ℝ) ^ (3 / 2 : ℝ) ≤ T := by
  obtain ⟨c, hc, n₀, H⟩ := h
  refine ⟨c, hc, n₀, fun n hn v₀ S _ _ T A hA => ?_⟩
  exact H n hn S T (A.sim sinkQ sinkDec) (A.sim_solves _ _ hA (sinkDec_spec v₀))

/-- **Strong bridges need `Ω(n^{3/2})` quantum queries**, given `DHHM_Thm23`. The gadget has `2n - 1` vertices. -/
theorem strongBridges_lower_bound (h : DHHM_Thm23) :
    ∃ c : ℝ, 0 < c ∧ ∃ n₀ : ℕ, ∀ n, n₀ ≤ n → ∀ (v₀ : Fin n) (S : Type) [Fintype S] [DecidableEq S] (T : ℕ)
      (A : QAlg ((Fin n ⊕ NewV v₀) × (Fin n ⊕ NewV v₀)) Bool S (Finset ((Fin n ⊕ NewV v₀) × (Fin n ⊕ NewV v₀))) T),
        A.Solves StrongBridgeAnswer → c * (n : ℝ) ^ (3 / 2 : ℝ) ≤ T := by
  obtain ⟨c, hc, n₀, H⟩ := h
  refine ⟨c, hc, n₀, fun n hn v₀ S _ _ T A hA => ?_⟩
  exact H n hn S T (A.sim (sbQ v₀) (sbDec v₀)) (A.sim_solves _ _ hA (sbDec_spec v₀))

/-- **Strong articulation points need `Ω(n^{3/2})` quantum queries**, given `DHHM_Thm23`. The gadget has `3n - 2`
vertices. -/
theorem saps_lower_bound (h : DHHM_Thm23) :
    ∃ c : ℝ, 0 < c ∧ ∃ n₀ : ℕ, ∀ n, n₀ ≤ n → ∀ (v₀ : Fin n) (S : Type) [Fintype S] [DecidableEq S] (T : ℕ)
      (A : QAlg ((Fin n ⊕ (NewV v₀ ⊕ NewV v₀)) × (Fin n ⊕ (NewV v₀ ⊕ NewV v₀))) Bool S
        (Finset (Fin n ⊕ (NewV v₀ ⊕ NewV v₀))) T),
        A.Solves SAPAnswer → c * (n : ℝ) ^ (3 / 2 : ℝ) ≤ T := by
  obtain ⟨c, hc, n₀, H⟩ := h
  refine ⟨c, hc, n₀, fun n hn v₀ S _ _ T A hA => ?_⟩
  exact H n hn S T (A.sim (sapQ v₀) (sapDec v₀)) (A.sim_solves _ _ hA (sapDec_spec v₀))

/-! ## Classical lower bounds, from classical Connectivity -/

/-- Flow-graph bridges need `Ω(n²)` randomized queries, given `ClassicalConnectivity`. -/
theorem classical_bridges_lower_bound (h : ClassicalConnectivity) :
    ∃ c : ℝ, 0 < c ∧ ∃ n₀ : ℕ, ∀ n, n₀ ≤ n → ∀ (v₀ : Fin n) (Ω : Type) [Fintype Ω] (T : ℕ)
      (A : RandAlg ((Fin n ⊕ Fin n) × (Fin n ⊕ Fin n)) (Finset ((Fin n ⊕ Fin n) × (Fin n ⊕ Fin n))) Ω),
        A.Solves T (BridgeAnswer (.inl v₀)) → c * (n : ℝ) ^ 2 ≤ T := by
  obtain ⟨c, hc, n₀, H⟩ := h
  refine ⟨c, hc, n₀, fun n hn v₀ Ω _ T A hA => ?_⟩
  exact H n hn Ω T (A.sim sinkQ sinkDec) (A.sim_solves _ _ hA (sinkDec_spec v₀))

/-- Strong bridges need `Ω(n²)` randomized queries, given `ClassicalConnectivity`. -/
theorem classical_strongBridges_lower_bound (h : ClassicalConnectivity) :
    ∃ c : ℝ, 0 < c ∧ ∃ n₀ : ℕ, ∀ n, n₀ ≤ n → ∀ (v₀ : Fin n) (Ω : Type) [Fintype Ω] (T : ℕ)
      (A : RandAlg ((Fin n ⊕ NewV v₀) × (Fin n ⊕ NewV v₀)) (Finset ((Fin n ⊕ NewV v₀) × (Fin n ⊕ NewV v₀))) Ω),
        A.Solves T StrongBridgeAnswer → c * (n : ℝ) ^ 2 ≤ T := by
  obtain ⟨c, hc, n₀, H⟩ := h
  refine ⟨c, hc, n₀, fun n hn v₀ Ω _ T A hA => ?_⟩
  exact H n hn Ω T (A.sim (sbQ v₀) (sbDec v₀)) (A.sim_solves _ _ hA (sbDec_spec v₀))

/-- Strong articulation points need `Ω(n²)` randomized queries, given `ClassicalConnectivity`. -/
theorem classical_saps_lower_bound (h : ClassicalConnectivity) :
    ∃ c : ℝ, 0 < c ∧ ∃ n₀ : ℕ, ∀ n, n₀ ≤ n → ∀ (v₀ : Fin n) (Ω : Type) [Fintype Ω] (T : ℕ)
      (A : RandAlg ((Fin n ⊕ (NewV v₀ ⊕ NewV v₀)) × (Fin n ⊕ (NewV v₀ ⊕ NewV v₀)))
        (Finset (Fin n ⊕ (NewV v₀ ⊕ NewV v₀))) Ω),
        A.Solves T SAPAnswer → c * (n : ℝ) ^ 2 ≤ T := by
  obtain ⟨c, hc, n₀, H⟩ := h
  refine ⟨c, hc, n₀, fun n hn v₀ Ω _ T A hA => ?_⟩
  exact H n hn Ω T (A.sim (sapQ v₀) (sapDec v₀)) (A.sim_solves _ _ hA (sapDec_spec v₀))

/-! ## The randomized bound for OR, proved -/

section OR

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The bits read by a decision tree on `x` within `t` queries. -/
def DetAlg.queried {β : Type*} (A : DetAlg ι β) (x : ι → Bool) : ℕ → Finset ι
  | 0 => ∅
  | t + 1 => A.queried x t ∪
    (match A.query (A.answers x t) with
      | .inl i => {i}
      | .inr _ => ∅)

omit [Fintype ι] in
theorem DetAlg.card_queried_le {β : Type*} (A : DetAlg ι β) (x : ι → Bool) (t : ℕ) : (A.queried x t).card ≤ t := by
  induction t with
  | zero => simp [DetAlg.queried]
  | succ t ih =>
    rw [DetAlg.queried]
    refine (Finset.card_union_le _ _).trans ?_
    cases A.query (A.answers x t) <;> simp <;> omega

omit [Fintype ι] in
/-- A decision tree cannot tell apart two inputs that agree on the bits it reads. -/
theorem DetAlg.answers_eq_of_agree {β : Type*} (A : DetAlg ι β) (x x' : ι → Bool) (t : ℕ)
    (h : ∀ i ∈ A.queried x t, x i = x' i) : A.answers x t = A.answers x' t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    have h1 : ∀ i ∈ A.queried x t, x i = x' i := fun i hi => h i (by
      rw [DetAlg.queried]
      exact Finset.mem_union_left _ hi)
    have heq := ih h1
    simp only [DetAlg.answers]
    rw [← heq]
    congr 2
    cases hq : A.query (A.answers x t) with
    | inl i =>
      have : x i = x' i := h i (by
        rw [DetAlg.queried, hq]
        simp)
      simp [bitVal, this]
    | inr b => rfl

/-- The output answers OR correctly. -/
def OrAnswer (x : ι → Bool) (o : Bool) : Prop := o = true ↔ ∃ i, x i = true

/-- **OR needs a third of its bits.** A randomized algorithm for OR on `N` bits, with error at most `1/3` on
every input, makes at least `N/3` queries. -/
theorem or_lower_bound {Ω : Type*} [Fintype Ω] (A : RandAlg ι Bool Ω) (T : ℕ) (hA : A.Solves T OrAnswer) :
    (Fintype.card ι : ℝ) ≤ 3 * T := by
  classical
  let z : ι → Bool := fun _ => false
  let e : ι → ι → Bool := fun i j => decide (j = i)
  let out : (ι → Bool) → Ω → Bool := fun x ω => (A.alg ω).output ((A.alg ω).answers x T)
  let Q : Ω → Finset ι := fun ω => (A.alg ω).queried z T
  have hz : 2 / 3 ≤ ∑ ω, if OrAnswer z (out z ω) then A.p ω else 0 := by
    have := hA z
    unfold RandAlg.prob at this
    convert this
  have he : ∀ i, 2 / 3 ≤ ∑ ω, if OrAnswer (e i) (out (e i) ω) then A.p ω else 0 := by
    intro i
    have := hA (e i)
    unfold RandAlg.prob at this
    convert this
  -- on one tree: for `i` not read on `z`, the tree is correct on at most one of `z` and `e i`
  have hone : ∀ ω i, (if OrAnswer z (out z ω) then A.p ω else 0) + (if OrAnswer (e i) (out (e i) ω) then A.p ω else 0) ≤
      A.p ω + if i ∈ Q ω then A.p ω else 0 := by
    intro ω i
    have hp := A.nonneg ω
    by_cases hi : i ∈ Q ω
    · simp only [hi, ite_true]
      split_ifs <;> linarith
    · simp only [hi, ite_false, add_zero]
      have hsame : out z ω = out (e i) ω := by
        simp only [out]
        rw [DetAlg.answers_eq_of_agree (A.alg ω) z (e i) T]
        intro j hj
        have hji : j ≠ i := fun hh => hi (hh ▸ hj)
        simp [z, e, hji]
      have hcz : OrAnswer z (out z ω) → out z ω = false := by
        intro h
        by_contra hne
        have hto : out z ω = true := by simpa using hne
        obtain ⟨j, hj⟩ := h.mp hto
        simp [z] at hj
      have hce : OrAnswer (e i) (out (e i) ω) → out (e i) ω = true := by
        intro h
        exact h.mpr ⟨i, by simp [e]⟩
      by_cases h1 : OrAnswer z (out z ω)
      · by_cases h2 : OrAnswer (e i) (out (e i) ω)
        · have := hcz h1
          have := hce h2
          simp_all
        · simp [h1, h2]
      · simp only [h1, ite_false, zero_add]
        split_ifs <;> linarith
  -- sum over all `i` and all trees
  have hsum : (Fintype.card ι : ℝ) * (4 / 3) ≤ (Fintype.card ι : ℝ) + T := by
    have h1 : (Fintype.card ι : ℝ) * (4 / 3) ≤
        ∑ i : ι, ((∑ ω, if OrAnswer z (out z ω) then A.p ω else 0) +
          ∑ ω, if OrAnswer (e i) (out (e i) ω) then A.p ω else 0) := by
      have : ∑ _i : ι, (4 / 3 : ℝ) ≤ ∑ i : ι, ((∑ ω, if OrAnswer z (out z ω) then A.p ω else 0) +
          ∑ ω, if OrAnswer (e i) (out (e i) ω) then A.p ω else 0) :=
        Finset.sum_le_sum fun i _ => by linarith [he i]
      simpa [Finset.card_univ, mul_comm] using this
    have h2 : ∑ i : ι, ((∑ ω, if OrAnswer z (out z ω) then A.p ω else 0) +
          ∑ ω, if OrAnswer (e i) (out (e i) ω) then A.p ω else 0) ≤
        ∑ ω, A.p ω * ((Fintype.card ι : ℝ) + T) := by
      have hsw : ∑ i : ι, ((∑ ω, if OrAnswer z (out z ω) then A.p ω else 0) +
          ∑ ω, if OrAnswer (e i) (out (e i) ω) then A.p ω else 0) =
          ∑ ω, ∑ i : ι, ((if OrAnswer z (out z ω) then A.p ω else 0) +
            if OrAnswer (e i) (out (e i) ω) then A.p ω else 0) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.sum_add_distrib]
      rw [hsw]
      refine Finset.sum_le_sum fun ω _ => ?_
      refine (Finset.sum_le_sum fun i _ => hone ω i).trans ?_
      rw [Finset.sum_add_distrib]
      have hp := A.nonneg ω
      have hq : ∑ i : ι, (if i ∈ Q ω then A.p ω else 0) = ((Q ω).card : ℝ) * A.p ω := by
        rw [Finset.sum_ite_mem]
        simp
      have hcard : ((Q ω).card : ℝ) ≤ T := by
        exact_mod_cast (A.alg ω).card_queried_le z T
      rw [hq]
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      nlinarith
    rw [← Finset.sum_mul, A.sum_one, one_mul] at h2
    linarith
  linarith

end OR

/-! ## The classical bound for dominators, proved -/

section ClassicalDominators

variable {X Y : Type*}

/-- The bits of the hidden pairs. All else in the matrix is fixed. -/
def orQ : (Bool ⊕ (X ⊕ Y)) × (Bool ⊕ (X ⊕ Y)) → (X × Y) ⊕ Bool
  | (.inl false, .inl true) => .inr true
  | (.inl false, .inr (.inl _)) => .inr true
  | (.inl true, .inr (.inr _)) => .inr true
  | (.inr (.inl a), .inr (.inr b)) => .inl (a, b)
  | _ => .inr false

theorem gr_orQ (x : X × Y → Bool) : gr (pull orQ x) = orGraph (fun a b => x (a, b)) := by
  funext u v
  apply propext
  rcases u with (_ | _) | a | a <;> rcases v with (_ | _) | b | b <;> simp [gr, pull, orQ, bitVal, orGraph]

open Classical in
/-- Some `y` has immediate dominator `r`. -/
noncomputable def orDec (o : Bool ⊕ (X ⊕ Y) → Option (Bool ⊕ (X ⊕ Y))) : Bool :=
  decide (∃ b : Y, o (orV b) = some orR)

theorem orDec_spec (x : X × Y → Bool) (o : Bool ⊕ (X ⊕ Y) → Option (Bool ⊕ (X ⊕ Y)))
    (h : IdomAnswer orR (pull orQ x) o) : OrAnswer x (orDec o) := by
  unfold IdomAnswer at h
  rw [gr_orQ] at h
  have := or_of_output h
  unfold OrAnswer orDec
  simp only [decide_eq_true_eq]
  rw [← this]
  simp

/-- **Dominators need `Ω(n²)` randomized queries, with no hypothesis.** An algorithm that outputs the immediate
dominators of every digraph on `Bool ⊕ (X ⊕ Y)`, with `|X| + |Y| + 2` vertices, makes at least `|X| |Y| / 3`
queries. -/
theorem classical_dominators_lower_bound [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]
    {Ω : Type*} [Fintype Ω] (T : ℕ)
    (A : RandAlg ((Bool ⊕ (X ⊕ Y)) × (Bool ⊕ (X ⊕ Y))) (Bool ⊕ (X ⊕ Y) → Option (Bool ⊕ (X ⊕ Y))) Ω)
    (hA : A.Solves T (IdomAnswer orR)) :
    (Fintype.card X : ℝ) * Fintype.card Y ≤ 3 * T := by
  have h := or_lower_bound (A.sim orQ orDec) T (A.sim_solves orQ orDec hA orDec_spec)
  simpa [Fintype.card_prod] using h

end ClassicalDominators

end Dominators
