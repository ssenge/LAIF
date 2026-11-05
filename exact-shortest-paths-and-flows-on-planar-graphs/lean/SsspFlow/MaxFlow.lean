import SsspFlow.ExactSssp
import SsspFlow.Flood
import SsspFlow.HostSim

/-!
# Negative weights and maximum flow in the message model

* `negSsspBound_of_reduction`: exact shortest paths and the reduction `NegReduction τ` give
  `NegSsspBound τ`.
* `not_negReduction_zero`: given exact shortest paths, `NegReduction` fails with the factor `0`.
* `maxFlowBound_of_neg`: `NegSsspBound τ` gives `MaxFlowBound τ'`, if `τ` at `5 n ^ 2 + 2` is at most a
  constant times `τ'` at `n + 2`. The hosts of a network with `n` nodes simulate an algorithm for negative
  weights on the dual network with `5 n ^ 2` identifiers, and a binary search over the value of the flow
  uses it.
* `maxFlowBound_polylog`, `maxFlowBound_subpoly`: the two instances.
* `negFlow_polylog`, `negFlow_subpoly`: both bounds from `LabelHypothesis`, `AggBox`, `SmoothingBox` and
  `NegReduction`.
-/

set_option autoImplicit false

open Cslib.Congest

namespace SsspFlow.Congest

open Kind

/-! ### One test of a flow value -/

/-- The input of a host for one test of a flow value: its rotation list, the costs of its darts, whether
it is the source, and the private strings of its identifiers. -/
structure HostIn (n : ℕ) (ρ' : Type) where
  /-- The rotation list. -/
  nbrs : List (Fin n)
  /-- The costs of the darts. -/
  cost : Fin n → ℤ
  /-- Whether the host is the source. -/
  isSource : Bool
  /-- The private strings of the identifiers. -/
  str : Fin n × Kind → ρ'

section Search

variable {n n' : ℕ} (e : Fin n × Fin n × Kind ≃ Fin n') {ρ' σ' : Type} {B' : ℕ}
  (P' : Algorithm (Fin n') (NegIn (Fin n') × ρ') σ' B') (out' : Fin n' → σ' → Option (Option ℤ))
  (T'' : ℕ)

/-- The input of an identifier, as its host computes it. -/
noncomputable def vIn (v : Fin n) (h : HostIn n ρ') (a : Fin n') : NegIn (Fin n') × ρ' :=
  (vNegIn e v h.nbrs h.cost h.isSource a, h.str ((e.symm a).2.1, (e.symm a).2.2))

/-- The hosts run the algorithm for negative weights on the dual network, and stop it after `T''`
rounds. -/
noncomputable def hostAlg :
    Algorithm (Fin n) (HostIn n ρ') (HostIn n ρ' × (Fin n' → ℕ × σ')) (B' + B') :=
  Algorithm.simulate (P'.stopAt T'') (fun a => (e.symm a).1)
    (fun v h b a => a ∈ vRot e v h.nbrs (e.symm b).2.1 (e.symm b).2.2) (crossId e) (vIn e)

variable (N : Net (Fin n)) (capL : Fin n → Fin n → ℕ) (σ : Fin n → Fin n → ℤ) (s t : Fin n)
  (r : Fin n → Fin n × Kind → ρ')

/-- The input of the identifiers for the flow value `β`. -/
noncomputable def virtInp (β : ℤ) (a : Fin n') : NegIn (Fin n') × ρ' :=
  ((dualNet N e).negIn (dualW e (flowCost capL σ β)) (e (s, (N.rotList s).headD s, corner)) a,
    r (e.symm a).1 ((e.symm a).2.1, (e.symm a).2.2))

/-- The answer of an identifier for the flow value `β`. -/
noncomputable def virtAns (β : ℤ) (a : Fin n') : Option (Option ℤ) :=
  out' a (P'.run (dualNet N e).G (virtInp e N capL σ s r β) T'' a)

/-- The input of the hosts for the flow value `β`. -/
def hostOf (β : ℤ) (v : Fin n) : HostIn n ρ' :=
  ⟨N.rotList v, flowCost capL σ β v, decide (v = s), r v⟩

/-- **The hosts simulate the dual network.** -/
theorem run_hostAlg (β : ℤ) (v i : Fin n) :
    out' (e (v, i, corner)) (((hostAlg e P' T'').run N.G (hostOf N capL σ s r β) (T'' + 1) v).2
      (e (v, i, corner))).2 = virtAns e P' out' T'' N capL σ s r β (e (v, i, corner)) := by
  have hsim : ((hostAlg e P' T'').run N.G (hostOf N capL σ s r β) (T'' + 1) v).2 (e (v, i, corner)) =
      (P'.stopAt T'').run (dualNet N e).G (virtInp e N capL σ s r β) (T'' + 1) (e (v, i, corner)) := by
    refine (Algorithm.run_simulate (P'.stopAt T'') (fun a => (e.symm a).1)
      (fun v h b a => a ∈ vRot e v h.nbrs (e.symm b).2.1 (e.symm b).2.2) (crossId e) (vIn e) N.G
      (dualNet N e).G (hostOf N capL σ s r β) (virtInp e N capL σ s r β) ?_ ?_ ?_ (T'' + 1) v).2
      (e (v, i, corner)) (by simp)
    · intro a
      show (_, _) = (vNegIn e _ _ _ _ a, _)
      rw [negIn_eq s rfl]
      rfl
    · intro b a hba
      show a ∈ vRot e (e.symm a).1 (N.rotList (e.symm a).1) (e.symm b).2.1 (e.symm b).2.2 ↔ _
      rw [← hba, ← dualNet_rotList (N := N) (e := e)]
      have : e ((e.symm b).1, (e.symm b).2.1, (e.symm b).2.2) = b := by simp
      rw [this]
      exact (dualNet N e).mem_rotList _ _
    · intro b a hba
      exact dual_adj_cross hba
  rw [hsim, Algorithm.run_stopAt]
  simp only [virtAns]
  rw [min_eq_right (by omega : T'' ≤ T'' + 1)]

end Search

/-! ### The binary search -/

/-- The data of a host during the search. -/
structure SearchData (n : ℕ) (ρ' : Type) where
  /-- The rotation list. -/
  nbrs : List (Fin n)
  /-- The capacities of the darts. -/
  capOut : Fin n → ℕ
  /-- The unit of flow on the edges. -/
  unit : Fin n → ℤ
  /-- Whether the host is the source. -/
  isSource : Bool
  /-- The private strings of the identifiers. -/
  str : Fin n × Kind → ρ'
  /-- The largest value known to be feasible. -/
  lo : ℕ
  /-- The smallest value known to be infeasible. -/
  hi : ℕ
  /-- A flow of value `lo`, on the edges at the host. -/
  flow : Fin n → ℤ

namespace SearchData

variable {n n' : ℕ} {ρ' σ' : Type}

/-- The value to test. -/
def mid (j : SearchData n ρ') : ℕ := j.lo + (j.hi - j.lo) / 2

/-- The input of the test. -/
def toHost (j : SearchData n ρ') : HostIn n ρ' :=
  ⟨j.nbrs, fun u => (j.capOut u : ℤ) - j.unit u * (j.mid : ℤ), j.isSource, j.str⟩

/-- The new data after a test. -/
noncomputable def update (e : Fin n × Fin n × Kind ≃ Fin n') (out' : Fin n' → σ' → Option (Option ℤ))
    (v : Fin n) (j : SearchData n ρ') (st : HostIn n ρ' × (Fin n' → ℕ × σ')) : SearchData n ρ' :=
  if out' (e (v, v, corner)) (st.2 (e (v, v, corner))).2 = none then { j with hi := j.mid }
  else
    { j with
      lo := j.mid
      flow := fun u => readZ (out' (e (v, j.nbrs.formPerm.symm u, corner))
          (st.2 (e (v, j.nbrs.formPerm.symm u, corner))).2) -
        readZ (out' (e (v, u, corner)) (st.2 (e (v, u, corner))).2) + j.unit u * (j.mid : ℤ) }

end SearchData

section Inv

variable {n n' : ℕ} (e : Fin n × Fin n × Kind ≃ Fin n') {ρ' σ' : Type} {B' : ℕ}
  (P' : Algorithm (Fin n') (NegIn (Fin n') × ρ') σ' B') (out' : Fin n' → σ' → Option (Option ℤ))
  (T'' : ℕ)

/-- The search as an algorithm. -/
noncomputable def searchAlg : Algorithm (Fin n) (SearchData n ρ')
    (SearchData n ρ' × ℕ × (HostIn n ρ' × (Fin n' → ℕ × σ'))) (B' + B') :=
  (hostAlg e P' T'').iter (T'' + 1) (fun _ j => j.toHost) (SearchData.update e out')

variable (N : Net (Fin n)) (capL : Fin n → Fin n → ℕ) (σ : Fin n → Fin n → ℤ) (s t : Fin n)
  (r : Fin n → Fin n × Kind → ρ') (hi₀ : ℕ)

/-- The data at the start of the search. -/
def searchStart (v : Fin n) : SearchData n ρ' :=
  ⟨N.rotList v, capL v, σ v, decide (v = s), r v, 0, hi₀, fun _ => 0⟩

variable {N capL σ s t r hi₀}

/-- **The invariant of the search.** -/
theorem search_inv {j₁ : ℕ} (hst : s ≠ t) (hP : N.toRot.Planar) (hc : N.toRot.Connected)
    (hσ : UnitFlow N s t σ) {x₀ : N.G.Dart}
    (hx₀ : e (s, (N.rotList s).headD s, corner) = idx N e corner x₀)
    (hgood : ∀ β : ℕ, β ≤ hi₀ → (dualNet N e).NegSpec (dualW e (flowCost capL σ β))
      (e (s, (N.rotList s).headD s, corner)) (virtAns e P' out' T'' N capL σ s r β))
    (hbase : (dualNet N e).HasNegCycle (dualW e (flowCost capL σ hi₀))) (h0 : 0 < hi₀)
    (hj : hi₀ ≤ 2 ^ j₁) (k : ℕ) :
    ∃ (lo hi : ℕ) (f : Fin n → Fin n → ℤ),
      (∀ v, Algorithm.iterData (hostAlg e P' T'') (T'' + 1) (fun _ j => j.toHost)
          (SearchData.update e out') N.G (searchStart N capL σ s r hi₀) k v =
        ⟨N.rotList v, capL v, σ v, decide (v = s), r v, lo, hi, f v⟩) ∧
      lo < hi ∧ hi ≤ hi₀ ∧ N.IsFlow capL s t f lo ∧
      (dualNet N e).HasNegCycle (dualW e (flowCost capL σ hi)) ∧ hi - lo ≤ 2 ^ (j₁ - k) := by
  induction k with
  | zero =>
    refine ⟨0, hi₀, fun _ _ => 0, fun v => rfl, h0, le_rfl, ⟨?_, ?_, ?_, ?_⟩, hbase, by simpa using hj⟩
    · simp
    · simp
    · simp
    · simp
  | succ k ih =>
    obtain ⟨lo, hi, f, hd, h1, h2, h3, h4, h5⟩ := ih
    set β : ℕ := lo + (hi - lo) / 2 with hβ
    have hlt : β < hi := by omega
    have hhost : (fun v => (fun (_ : Fin n) (j : SearchData n ρ') => j.toHost) v
        (Algorithm.iterData (hostAlg e P' T'') (T'' + 1) (fun _ j => j.toHost)
          (SearchData.update e out') N.G (searchStart N capL σ s r hi₀) k v)) =
        hostOf N capL σ s r (β : ℤ) := by
      funext v
      rw [hd v]
      rfl
    have hans : ∀ v i, out' (e (v, i, corner))
        (((hostAlg e P' T'').run N.G (hostOf N capL σ s r (β : ℤ)) (T'' + 1) v).2
          (e (v, i, corner))).2 = virtAns e P' out' T'' N capL σ s r β (e (v, i, corner)) :=
      fun v i => run_hostAlg e P' out' T'' N capL σ s r β v i
    have hstep : ∀ v, Algorithm.iterData (hostAlg e P' T'') (T'' + 1) (fun _ j => j.toHost)
        (SearchData.update e out') N.G (searchStart N capL σ s r hi₀) (k + 1) v =
        SearchData.update e out' v ⟨N.rotList v, capL v, σ v, decide (v = s), r v, lo, hi, f v⟩
          ((hostAlg e P' T'').run N.G (hostOf N capL σ s r (β : ℤ)) (T'' + 1) v) := by
      intro v
      show SearchData.update e out' v _ ((hostAlg e P' T'').run N.G _ (T'' + 1) v) = _
      rw [hhost, hd v]
    have hS := hgood β (by omega)
    rcases hS with ⟨hneg, hnone⟩ | ⟨hneg, hall⟩
    · -- a negative cycle: the value is too large
      have hlo : lo < β := by
        rcases Nat.lt_or_ge lo β with h | h
        · exact h
        · exfalso
          have : β = lo := by omega
          rw [this] at hneg
          exact no_negCycle_of_flow hP hc hst hσ h3 hneg
      refine ⟨lo, β, f, fun v => ?_, hlo, by omega, h3, hneg, ?_⟩
      · rw [hstep v]
        unfold SearchData.update
        rw [hans v v, hnone, ite_eq_left rfl]
        rfl
      · have hk : j₁ - k = j₁ - (k + 1) + 1 ∨ j₁ - k = 0 := by omega
        rcases hk with hk | hk
        · rw [hk, pow_succ] at h5
          omega
        · have hk' : j₁ - (k + 1) = 0 := by omega
          rw [hk, pow_zero] at h5
          rw [hk', pow_zero]
          omega
    · -- no negative cycle: the value is feasible
      have hne : ∀ a, virtAns e P' out' T'' N capL σ s r β a ≠ none := by
        intro a
        rcases hall a with ⟨h, -⟩ | ⟨d, h, -⟩ <;> simp [h]
      have hflow : N.IsFlow capL s t _ (β : ℤ) := isFlow_of_spec (e := e) hc hst hσ (x₀ := x₀)
        (r := virtAns e P' out' T'' N capL σ s r β) (a₀ := e (s, s, corner))
        (by rw [← hx₀]; exact Or.inr ⟨hneg, hall⟩) (hne _)
      refine ⟨β, hi, _, fun v => ?_, hlt, h2, hflow, h4, ?_⟩
      · rw [hstep v]
        unfold SearchData.update
        rw [hans v v, ite_eq_right (hne _)]
        simp only [hans]
        rfl
      · have hk : j₁ - k = j₁ - (k + 1) + 1 ∨ j₁ - k = 0 := by omega
        rcases hk with hk | hk
        · rw [hk, pow_succ] at h5
          omega
        · have hk' : j₁ - (k + 1) = 0 := by omega
          rw [hk, pow_zero] at h5
          rw [hk', pow_zero]
          omega

end Inv

/-! ### The value of the search -/

section Top

variable {n n' : ℕ} {e : Fin n × Fin n × Kind ≃ Fin n'} {N : Net (Fin n)}
  {capL : Fin n → Fin n → ℕ} {σ : Fin n → Fin n → ℤ} {s t : Fin n}

/-- A value above all flows has a negative cycle. -/
theorem hasNegCycle_top {U hi₀ : ℕ} (hc : N.toRot.Connected) (hst : s ≠ t) (hσ : UnitFlow N s t σ)
    {x₀ : N.G.Dart} (hcap : ∀ a b, N.G.Adj a b → capL a b ≤ U) (hhi : n * U < hi₀)
    {R : Fin n' → Option (Option ℤ)}
    (hS : (dualNet N e).NegSpec (dualW e (flowCost capL σ hi₀)) (idx N e corner x₀) R) :
    (dualNet N e).HasNegCycle (dualW e (flowCost capL σ hi₀)) := by
  rcases hS with ⟨h, -⟩ | ⟨h, hall⟩
  · exact h
  · exfalso
    have hne : R (e (s, s, corner)) ≠ none := by
      rcases hall (e (s, s, corner)) with ⟨h1, -⟩ | ⟨d, h1, -⟩ <;> simp [h1]
    have hflow := isFlow_of_spec (e := e) hc hst hσ (x₀ := x₀) (Or.inr ⟨h, hall⟩) hne
    have hval := hflow.val
    have hle : ∑ u ∈ N.G.neighborFinset s, (readZ (R (e (s, (N.rotList s).formPerm.symm u, corner))) -
        readZ (R (e (s, u, corner))) + σ s u * (hi₀ : ℤ)) ≤ ∑ _u ∈ N.G.neighborFinset s, (U : ℤ) := by
      refine Finset.sum_le_sum fun u hu => ?_
      have hadj := (SimpleGraph.mem_neighborFinset _ _ _).1 hu
      have h1 := hflow.cap s u hadj
      have h2 : (capL s u : ℤ) ≤ U := by exact_mod_cast hcap s u hadj
      exact h1.trans h2
    rw [hval, Finset.sum_const, nsmul_eq_mul] at hle
    have hcard : ((N.G.neighborFinset s).card : ℤ) ≤ n := by
      have := Finset.card_le_univ (N.G.neighborFinset s)
      rw [Fintype.card_fin] at this
      exact_mod_cast this
    have : (hi₀ : ℤ) ≤ (n : ℤ) * U :=
      hle.trans (mul_le_mul_of_nonneg_right hcard (by positivity))
    have h3 : (n * U : ℤ) < hi₀ := by exact_mod_cast hhi
    omega

end Top

theorem Net.isFlow_congr {V : Type} [Fintype V] [DecidableEq V] {N : Net V} {c c' : V → V → ℕ}
    {s t : V} {f : V → V → ℤ} {β : ℤ} (h : ∀ a b, N.G.Adj a b → c a b = c' a b)
    (hf : N.IsFlow c s t f β) : N.IsFlow c' s t f β :=
  ⟨hf.skew, fun a b hab => by rw [← h a b hab]; exact hf.cap a b hab, hf.cons, hf.val⟩

/-! ### The whole algorithm -/

/-- The input of the algorithm for maximum flow. -/
abbrev WholeIn (n : ℕ) (ρ' : Type) : Type := FlowIn (Fin n) × (Fin n × Kind → ρ')

/-- The state of a flood. -/
abbrev FloodSt (n : ℕ) : Type := (Fin n → Bool) × Option (Option (Fin n))

section Whole

variable {n n' : ℕ} (e : Fin n × Fin n × Kind ≃ Fin n') {ρ' σ' : Type} {B' : ℕ}
  (P' : Algorithm (Fin n') (NegIn (Fin n') × ρ') σ' B') (out' : Fin n' → σ' → Option (Option ℤ))
  (T'' hi₀ D : ℕ) {B : ℕ} (hw : 1 ≤ B) (hw' : B' + B' ≤ B)

/-- The first flood. -/
noncomputable def phase1 : Algorithm (Fin n) (WholeIn n ρ') (WholeIn n ρ' × FloodSt n) B :=
  ((floodAlg (Fin n)).widen hw).keep fun _ i => (i.1.isSource, fun _ => true)

/-- The second flood. -/
noncomputable def phase2 : Algorithm (Fin n) (WholeIn n ρ' × Option (Fin n))
    ((WholeIn n ρ' × Option (Fin n)) × FloodSt n) B :=
  ((floodAlg (Fin n)).widen hw).keep fun _ j => (j.1.1.isSink, fun w => decide (j.2 = some w))

/-- The data at the start of the search, from the two floods. -/
def startOf (_v : Fin n) (st : (WholeIn n ρ' × Option (Fin n)) × FloodSt n) : SearchData n ρ' :=
  ⟨st.1.1.1.nbrs, st.1.1.1.capOut, unitOf st.1.2 st.2.2, st.1.1.1.isSource, st.1.1.2, 0, hi₀,
    fun _ => 0⟩

/-- Two floods, then the search. -/
noncomputable def wholeAlg : Algorithm (Fin n) (WholeIn n ρ')
    ((ℕ × (WholeIn n ρ' × FloodSt n)) ⊕ ((ℕ × ((WholeIn n ρ' × Option (Fin n)) × FloodSt n)) ⊕
      (SearchData n ρ' × ℕ × (HostIn n ρ' × (Fin n' → ℕ × σ'))))) B :=
  (phase1 hw).seq D (fun _ st => (st.1, st.2.2.join))
    ((phase2 hw).seq D (startOf hi₀) ((searchAlg e P' out' T'').widen hw'))

/-- The result of a node. -/
def wholeOut {X Y : Type} (_v : Fin n) (st : ℕ × (X ⊕ (Y ⊕ (SearchData n ρ' × ℕ ×
    (HostIn n ρ' × (Fin n' → ℕ × σ')))))) : ℕ × (Fin n → ℤ) :=
  match st.2 with
  | .inr (.inr x) => (x.1.lo, x.1.flow)
  | _ => (0, fun _ => 0)

variable {e P' out' T'' hi₀ D hw hw'}
variable {N : Net (Fin n)} {cap : Fin n → Fin n → ℕ} {s t : Fin n}
  {r : Fin n → Fin n × Kind → ρ'}

/-- The capacities of a network as its nodes see them. -/
def capOf (N : Net (Fin n)) (cap : Fin n → Fin n → ℕ) (s t v : Fin n) : Fin n → ℕ :=
  (N.flowIn cap s t v).capOut

/-- The unit of flow of a network as its nodes compute it. -/
noncomputable def unitOfNet (N : Net (Fin n)) (s t : Fin n) (D : ℕ) (v u : Fin n) : ℤ :=
  unitOf (floodPar N s D v) (tokenSt N (floodPar N s D) t D v) u

/-- **The run of the whole algorithm.** -/
theorem run_whole (J : ℕ) (v : Fin n) :
    ∃ x, (wholeAlg e P' out' T'' hi₀ D hw hw').run N.G (fun u => (N.flowIn cap s t u, r u))
        (D + (D + (J * (T'' + 1) + 0))) v =
      .inr (.inr (Algorithm.iterData (hostAlg e P' T'') (T'' + 1) (fun _ j => j.toHost)
        (SearchData.update e out') N.G
        (searchStart N (capOf N cap s t) (unitOfNet N s t D) s r hi₀) J v, x)) := by
  have h1 : (phase1 hw).run N.G (fun u => (N.flowIn cap s t u, r u)) D = fun v =>
      ((N.flowIn cap s t v, r v), (floodAlg (Fin n)).run N.G (parentIn s) D v) := by
    unfold phase1
    rw [Algorithm.run_keep, Algorithm.run_widen]
    rfl
  have h2 : (phase2 hw).run N.G (fun v => ((N.flowIn cap s t v, r v), floodPar N s D v)) D = fun v =>
      (((N.flowIn cap s t v, r v), floodPar N s D v),
        (floodAlg (Fin n)).run N.G (tokenIn (floodPar N s D) t) D v) := by
    unfold phase2
    rw [Algorithm.run_keep, Algorithm.run_widen]
    rfl
  have h3 : (fun v => (fun (_ : Fin n) (st : WholeIn n ρ' × FloodSt n) => (st.1, st.2.2.join)) v
      ((phase1 hw).run N.G (fun u => (N.flowIn cap s t u, r u)) D v)) =
      fun v => ((N.flowIn cap s t v, r v), floodPar N s D v) := by
    rw [h1]
    rfl
  have h4 : (fun v => startOf hi₀ v ((phase2 hw).run N.G
      (fun v => ((N.flowIn cap s t v, r v), floodPar N s D v)) D v)) =
      searchStart N (capOf N cap s t) (unitOfNet N s t D) s r hi₀ := by
    rw [h2]
    rfl
  unfold wholeAlg
  rw [Algorithm.run_seq]
  simp only
  rw [h3, Algorithm.run_seq]
  simp only
  rw [h4, Algorithm.run_widen]
  unfold searchAlg
  rw [Algorithm.run_iter _ _ _ _ _ (Nat.succ_pos T'') J 0 (Nat.succ_pos T'')]
  exact ⟨_, rfl⟩

/-- The result after enough rounds. -/
theorem out_whole {J Ttot Tbig : ℕ} (hT : Ttot = D + (D + (J * (T'' + 1) + 0))) (hb : Ttot ≤ Tbig)
    (v : Fin n) :
    wholeOut (X := ℕ × (WholeIn n ρ' × FloodSt n))
      (Y := ℕ × ((WholeIn n ρ' × Option (Fin n)) × FloodSt n)) v
      (((wholeAlg e P' out' T'' hi₀ D hw hw').stopAt Ttot).run N.G
        (fun u => (N.flowIn cap s t u, r u)) Tbig v) =
    (let j := Algorithm.iterData (hostAlg e P' T'') (T'' + 1) (fun _ j => j.toHost)
        (SearchData.update e out') N.G
        (searchStart N (capOf N cap s t) (unitOfNet N s t D) s r hi₀) J v
     (j.lo, j.flow)) := by
  rw [Algorithm.run_stopAt, min_eq_right hb]
  obtain ⟨x, hx⟩ := run_whole (e := e) (P' := P') (out' := out') (T'' := T'') (hi₀ := hi₀) (D := D)
    (hw := hw) (hw' := hw') (N := N) (cap := cap) (s := s) (t := t) (r := r) J v
  rw [hT]
  simp only [wholeOut]
  rw [hx]

end Whole

/-! ### Counting the strings -/

section Count

/-- The strings of the identifiers from the strings of the hosts. -/
def strEquiv {n n' : ℕ} (e : Fin n × Fin n × Kind ≃ Fin n') (ρ' : Type) :
    (Fin n → Fin n × Kind → ρ') ≃ (Fin n' → ρ') where
  toFun r a := r (e.symm a).1 ((e.symm a).2.1, (e.symm a).2.2)
  invFun r' v p := r' (e (v, p.1, p.2))
  left_inv r := by
    funext v p
    simp
  right_inv r' := by
    funext a
    simp

/-- A union bound over a map of strings. -/
theorem strCount_le_of_map {V₁ V₂ ρ₁ ρ₂ : Type} [Fintype V₁] [DecidableEq V₁] [Fintype V₂]
    [DecidableEq V₂] [Fintype ρ₁] [Fintype ρ₂] (Φ : (V₁ → ρ₁) ≃ (V₂ → ρ₂)) (bad : (V₁ → ρ₁) → Prop)
    (bad' : ℕ → (V₂ → ρ₂) → Prop) (m X : ℕ) (hsub : ∀ r, bad r → ∃ β, β ≤ m ∧ bad' β (Φ r))
    (hX : ∀ β, β ≤ m → strCount (bad' β) * X ≤ Fintype.card (V₂ → ρ₂)) :
    strCount bad * X ≤ (m + 1) * Fintype.card (V₁ → ρ₁) := by
  classical
  have h1 : strCount bad ≤ ∑ β ∈ Finset.range (m + 1), strCount (bad' β) := by
    have hsubset : (Finset.univ.filter bad).map Φ.toEmbedding ⊆
        (Finset.range (m + 1)).biUnion fun β => Finset.univ.filter (bad' β) := by
      intro y hy
      obtain ⟨r, hr, rfl⟩ := Finset.mem_map.1 hy
      obtain ⟨β, hβ, hb⟩ := hsub r (Finset.mem_filter.1 hr).2
      exact Finset.mem_biUnion.2 ⟨β, Finset.mem_range.2 (by omega), Finset.mem_filter.2 ⟨Finset.mem_univ _, hb⟩⟩
    have h2 := Finset.card_le_card hsubset
    rw [Finset.card_map] at h2
    have h3 := h2.trans Finset.card_biUnion_le
    unfold strCount
    convert h3
  calc strCount bad * X ≤ (∑ β ∈ Finset.range (m + 1), strCount (bad' β)) * X :=
        Nat.mul_le_mul_right _ h1
    _ = ∑ β ∈ Finset.range (m + 1), strCount (bad' β) * X := Finset.sum_mul _ _ _
    _ ≤ ∑ _β ∈ Finset.range (m + 1), Fintype.card (V₂ → ρ₂) :=
        Finset.sum_le_sum fun β hβ => hX β (by have := Finset.mem_range.1 hβ; omega)
    _ = (m + 1) * Fintype.card (V₁ → ρ₁) := by
        rw [Finset.sum_const, Finset.card_range, smul_eq_mul, Fintype.card_congr Φ]

end Count

/-! ### Correctness -/

section Correct

theorem noIso_of_diam {V : Type} [Fintype V] [DecidableEq V] {N : Net V} {D : ℕ} (hD : N.DiamLE D)
    {s t : V} (hst : s ≠ t) (x : V) : ∃ y, N.G.Adj x y := by
  obtain ⟨y, hy⟩ : ∃ y, x ≠ y := by
    by_cases h : x = s
    · exact ⟨t, h ▸ hst⟩
    · exact ⟨s, h⟩
  obtain ⟨p, -⟩ := hD x y
  cases p with
  | nil => exact absurd rfl hy
  | cons h _ => exact ⟨_, h⟩

theorem connected_of_diam {V : Type} [Fintype V] [DecidableEq V] {N : Net V} {D : ℕ}
    (hD : N.DiamLE D) {s t : V} (hst : s ≠ t) : N.toRot.Connected := by
  obtain ⟨y, hy⟩ := noIso_of_diam hD hst s
  have hne : Nonempty V := ⟨s⟩
  have hG : N.G.Connected :=
    { preconnected := fun u v => by
        obtain ⟨p, -⟩ := hD u v
        exact ⟨p⟩ }
  exact N.toRot_connected hG ⟨(s, y), hy⟩

variable {n n' : ℕ} {e : Fin n × Fin n × Kind ≃ Fin n'} {ρ' σ' : Type} {B' : ℕ}
  {P' : Algorithm (Fin n') (NegIn (Fin n') × ρ') σ' B'} {out' : Fin n' → σ' → Option (Option ℤ)}
  {T'' D : ℕ} {B : ℕ} {hw : 1 ≤ B} {hw' : B' + B' ≤ B}
  {N : Net (Fin n)} {cap : Fin n → Fin n → ℕ} {s t : Fin n} {r : Fin n → Fin n × Kind → ρ'}

/-- **If all tests are correct, the result is a maximum flow.** -/
theorem whole_correct {K J Ttot Tbig : ℕ} (hP : N.toRot.Planar) (hD : N.DiamLE D)
    (hcap : ∀ a b, N.G.Adj a b → cap a b ≤ (n + 2) ^ K) (hst : s ≠ t)
    (hJ : J = Nat.log 2 (n * (n + 2) ^ K + 1) + 1) (hT : Ttot = D + (D + (J * (T'' + 1) + 0)))
    (hb : Ttot ≤ Tbig)
    (hgood : ∀ β : ℕ, β ≤ n * (n + 2) ^ K + 1 → (dualNet N e).NegSpec
      (dualW e (flowCost (capOf N cap s t) (unitOfNet N s t D) β))
      (e (s, (N.rotList s).headD s, corner))
      (virtAns e P' out' T'' N (capOf N cap s t) (unitOfNet N s t D) s r β)) :
    N.FlowSpec cap s t (fun v => wholeOut (X := ℕ × (WholeIn n ρ' × FloodSt n))
      (Y := ℕ × ((WholeIn n ρ' × Option (Fin n)) × FloodSt n)) v
      (((wholeAlg e P' out' T'' (n * (n + 2) ^ K + 1) D hw hw').stopAt Ttot).run N.G
        (fun u => (N.flowIn cap s t u, r u)) Tbig v)) := by
  have hN := noIso_of_diam hD hst
  have hc := connected_of_diam hD hst
  have hσ : UnitFlow N s t (unitOfNet N s t D) := unitFlow_of_floods N hD hst
  obtain ⟨x₀, hx₀⟩ : ∃ x₀ : N.G.Dart, e (s, (N.rotList s).headD s, corner) = idx N e corner x₀ := by
    obtain ⟨y, hy⟩ := hN s
    have hy' := (N.mem_rotList _ _).2 hy
    cases hL : N.rotList s with
    | nil =>
      rw [hL] at hy'
      simp at hy'
    | cons z l =>
      have hz : N.G.Adj s z := (N.mem_rotList _ _).1 (by rw [hL]; simp)
      exact ⟨⟨(s, z), hz⟩, rfl⟩
  have hcapL : ∀ a b, N.G.Adj a b → capOf N cap s t a b = cap a b := fun a b hab => by
    simp [capOf, Net.flowIn, hab]
  have hbase := hasNegCycle_top (U := (n + 2) ^ K) (hi₀ := n * (n + 2) ^ K + 1) (e := e)
    (capL := capOf N cap s t) hc hst hσ (x₀ := x₀)
    (fun a b hab => by rw [hcapL a b hab]; exact hcap a b hab) (by omega)
    (R := virtAns e P' out' T'' N (capOf N cap s t) (unitOfNet N s t D) s r
      ((n * (n + 2) ^ K + 1 : ℕ) : ℤ))
    (by rw [← hx₀]; exact hgood _ le_rfl)
  have hj : n * (n + 2) ^ K + 1 ≤ 2 ^ J := by
    rw [hJ]
    exact (Nat.lt_pow_succ_log_self (by norm_num) _).le
  obtain ⟨lo, hi, f, hd, h1, h2, h3, h4, h5⟩ := search_inv e P' out' T'' hst hP hc hσ hx₀ hgood hbase
    (by omega) hj J
  have hv : ∀ v, wholeOut (X := ℕ × (WholeIn n ρ' × FloodSt n))
      (Y := ℕ × ((WholeIn n ρ' × Option (Fin n)) × FloodSt n)) v
      (((wholeAlg e P' out' T'' (n * (n + 2) ^ K + 1) D hw hw').stopAt Ttot).run N.G
        (fun u => (N.flowIn cap s t u, r u)) Tbig v) = (lo, f v) := fun v => by
    rw [out_whole hT hb v, hd v]
  refine ⟨lo, fun v => congrArg Prod.fst (hv v), ?_, ?_⟩
  · have hfun : (fun v u => (wholeOut (X := ℕ × (WholeIn n ρ' × FloodSt n))
        (Y := ℕ × ((WholeIn n ρ' × Option (Fin n)) × FloodSt n)) v
        (((wholeAlg e P' out' T'' (n * (n + 2) ^ K + 1) D hw hw').stopAt Ttot).run N.G
          (fun u => (N.flowIn cap s t u, r u)) Tbig v)).2 u) = f := by
      funext v u
      rw [hv v]
    simp only at hfun ⊢
    rw [hfun]
    exact Net.isFlow_congr hcapL h3
  · intro f' β' hf'
    by_contra hlt
    have hlt' : (lo : ℤ) < β' := not_le.1 hlt
    have hf'' := Net.isFlow_congr (fun a b hab => (hcapL a b hab).symm) hf'
    refine no_negCycle_of_flow (e := e) hP hc hst hσ hf''
      (hasNegCycle_mono (β := hi) (by positivity) ?_ h4)
    rw [hJ, Nat.sub_self, pow_zero] at h5
    omega

/-- **The bad strings.** If the algorithm for negative weights is wrong on a fraction at most
`1 / (n' + 1) ^ (k + K + 1)` of its strings, then the search is wrong on a fraction at most
`1 / (n + 1) ^ k`, by a union bound over the flow values. -/
theorem maxFlow_count {K k J Ttot Tbig : ℕ} [Fintype ρ'] (hn' : n' = n * (n * 5))
    (hP' : ∀ (N : Net (Fin n')) (w : Fin n' → Fin n' → Option ℤ) (s : Fin n'),
      N.toRot.Planar → N.DiamLE (5 * D + 6) → N.NegValid ((n' + 2) ^ (K + 1)) w →
      strCount (fun r : Fin n' → ρ' => ¬ N.NegSpec w s (fun v =>
        out' v (P'.run N.G (fun u => (N.negIn w s u, r u)) T'' v))) * (n' + 1) ^ (k + K + 1) ≤
      Fintype.card (Fin n' → ρ'))
    (hJ : J = Nat.log 2 (n * (n + 2) ^ K + 1) + 1) (hT : Ttot = D + (D + (J * (T'' + 1) + 0)))
    (hb : Ttot ≤ Tbig) (hP : N.toRot.Planar) (hD : N.DiamLE D)
    (hcap : ∀ a b, N.G.Adj a b → cap a b ≤ (n + 2) ^ K) (hst : s ≠ t) :
    strCount (fun r : Fin n → Fin n × Kind → ρ' => ¬ N.FlowSpec cap s t (fun v =>
      wholeOut (X := ℕ × (WholeIn n ρ' × FloodSt n))
        (Y := ℕ × ((WholeIn n ρ' × Option (Fin n)) × FloodSt n)) v
        (((wholeAlg e P' out' T'' (n * (n + 2) ^ K + 1) D hw hw').stopAt Ttot).run N.G
          (fun u => (N.flowIn cap s t u, r u)) Tbig v))) * (n + 1) ^ k ≤
    Fintype.card (Fin n → Fin n × Kind → ρ') := by
  have hN := noIso_of_diam hD hst
  have hc := connected_of_diam hD hst
  have hσ : UnitFlow N s t (unitOfNet N s t D) := unitFlow_of_floods N hD hst
  have hn2 : 2 ≤ n := by
    have h1 := s.2
    have h2 := t.2
    have h3 : (s : ℕ) ≠ t := fun h => hst (Fin.ext h)
    omega
  have hU : 1 ≤ (n + 2) ^ K := Nat.one_le_pow _ _ (by omega)
  have hnn : n + 2 ≤ n' + 1 := by
    subst hn'
    nlinarith
  have hcapL : ∀ a b, N.G.Adj a b → capOf N cap s t a b = cap a b := fun a b hab => by
    simp [capOf, Net.flowIn, hab]
  have hmain := strCount_le_of_map (strEquiv e ρ')
    (fun r : Fin n → Fin n × Kind → ρ' => ¬ N.FlowSpec cap s t (fun v =>
      wholeOut (X := ℕ × (WholeIn n ρ' × FloodSt n))
        (Y := ℕ × ((WholeIn n ρ' × Option (Fin n)) × FloodSt n)) v
        (((wholeAlg e P' out' T'' (n * (n + 2) ^ K + 1) D hw hw').stopAt Ttot).run N.G
          (fun u => (N.flowIn cap s t u, r u)) Tbig v)))
    (fun (β : ℕ) (r' : Fin n' → ρ') => ¬ (dualNet N e).NegSpec
      (dualW e (flowCost (capOf N cap s t) (unitOfNet N s t D) β))
      (e (s, (N.rotList s).headD s, corner)) (fun v =>
        out' v (P'.run (dualNet N e).G (fun u => ((dualNet N e).negIn
          (dualW e (flowCost (capOf N cap s t) (unitOfNet N s t D) β))
          (e (s, (N.rotList s).headD s, corner)) u, r' u)) T'' v)))
    (n * (n + 2) ^ K + 1) ((n' + 1) ^ (k + K + 1)) ?_ ?_
  · have hnum : (n * (n + 2) ^ K + 1 + 1) * (n + 1) ^ k ≤ (n' + 1) ^ (k + K + 1) := by
      have h1 : n * (n + 2) ^ K + 1 + 1 ≤ (n + 2) ^ (K + 1) := by
        rw [pow_succ]
        nlinarith
      have h2 : (n + 2) ^ (K + 1) ≤ (n' + 1) ^ (K + 1) := Nat.pow_le_pow_left hnn _
      have h3 : (n + 1) ^ k ≤ (n' + 1) ^ k := Nat.pow_le_pow_left (by omega) _
      calc (n * (n + 2) ^ K + 1 + 1) * (n + 1) ^ k ≤ (n' + 1) ^ (K + 1) * (n' + 1) ^ k :=
            Nat.mul_le_mul (h1.trans h2) h3
        _ = (n' + 1) ^ (k + K + 1) := by
            rw [← pow_add]
            congr 1
            omega
    have hpos : 0 < n * (n + 2) ^ K + 1 + 1 := by omega
    refine Nat.le_of_mul_le_mul_left ?_ hpos
    calc _ = _ * ((n * (n + 2) ^ K + 1 + 1) * (n + 1) ^ k) := by ring
      _ ≤ _ * (n' + 1) ^ (k + K + 1) := Nat.mul_le_mul_left _ hnum
      _ ≤ _ := hmain
  · intro r hbad
    by_contra hall
    apply hbad
    refine whole_correct hP hD hcap hst hJ hT hb fun β hβ => ?_
    by_contra hS
    exact hall ⟨β, hβ, hS⟩
  · intro β hβ
    refine hP' (dualNet N e) _ _ (dualNet_planar hP hN hD hc) (dualNet_diam hD)
      (dualW_valid fun a b hab => ?_)
    have h1 : |((capOf N cap s t a b : ℕ) : ℤ)| ≤ (n + 2) ^ K := by
      rw [hcapL a b hab, Nat.abs_cast]
      exact_mod_cast hcap a b hab
    have h2 : |unitOfNet N s t D a b * (β : ℤ)| ≤ n * (n + 2) ^ K + 1 := by
      rw [abs_mul, Nat.abs_cast]
      have h3 := hσ.bound a b hab
      have h4 : (β : ℤ) ≤ ((n * (n + 2) ^ K + 1 : ℕ) : ℤ) := by exact_mod_cast hβ
      push_cast at h4
      nlinarith [abs_nonneg (unitOfNet N s t D a b), (Int.natCast_nonneg β)]
    have h3 : (((n + 2) ^ (K + 1) : ℕ) : ℤ) ≤ (((n' + 2) ^ (K + 1) : ℕ) : ℤ) := by
      exact_mod_cast Nat.pow_le_pow_left (by omega) _
    have h4 : (((n + 2) ^ K : ℕ) : ℤ) + ((n * (n + 2) ^ K + 1 : ℕ) : ℤ) ≤
        (((n + 2) ^ (K + 1) : ℕ) : ℤ) := by
      have : (n + 2) ^ K + (n * (n + 2) ^ K + 1) ≤ (n + 2) ^ (K + 1) := by
        rw [pow_succ]
        nlinarith
      exact_mod_cast this
    unfold flowCost
    refine (abs_sub _ _).trans (le_trans (add_le_add h1 h2) ?_)
    push_cast at h3 h4 ⊢
    linarith

end Correct

/-! ### The arithmetic of the bound -/

section Arith

theorem logN_dual (n : ℕ) : logN (n * (n * 5)) ≤ 4 * logN n := by
  unfold logN
  have h1 : n + 2 < 2 ^ (Nat.log 2 (n + 2) + 1) := Nat.lt_pow_succ_log_self (by norm_num) _
  have h2 : n * (n * 5) + 2 ≤ (n + 2) ^ 4 := by nlinarith [sq_nonneg (n * n), sq_nonneg n]
  have h3 : (n + 2) ^ 4 < (2 ^ (Nat.log 2 (n + 2) + 1)) ^ 4 := Nat.pow_lt_pow_left h1 (by norm_num)
  rw [← pow_mul] at h3
  have h4 := Nat.log_lt_of_lt_pow (by omega) (h2.trans_lt h3)
  omega

theorem search_rounds_le (n K : ℕ) : Nat.log 2 (n * (n + 2) ^ K + 1) + 1 ≤ (K + 1) * logN n := by
  have h1 : n + 2 < 2 ^ logN n := Nat.lt_pow_succ_log_self (by norm_num) _
  have h2 : n * (n + 2) ^ K + 1 ≤ (n + 2) ^ (K + 1) := by
    have : 1 ≤ (n + 2) ^ K := Nat.one_le_pow _ _ (by omega)
    rw [pow_succ]
    nlinarith
  have h3 : (n + 2) ^ (K + 1) < (2 ^ logN n) ^ (K + 1) := Nat.pow_lt_pow_left h1 (by omega)
  rw [← pow_mul] at h3
  have h4 := Nat.log_lt_of_lt_pow (by omega) (h2.trans_lt h3)
  rw [Nat.mul_comm (K + 1)]
  omega

theorem whole_rounds_le {C' Cτ c' K D L L' t t' J T'' : ℕ} (hL : 1 ≤ L) (hD : 1 ≤ D) (ht' : 1 ≤ t')
    (ht : t ≤ Cτ * t') (hL' : L' ≤ 4 * L) (hJ : J ≤ (K + 1) * L)
    (hT : T'' = C' * t * L' ^ c' * (5 * D + 6)) :
    D + (D + (J * (T'' + 1) + 0)) ≤
      (2 + (K + 1) * (C' * Cτ * 4 ^ c' * 11 + 1) + 2 * C' * 4 ^ c' + 1) * t' * L ^ (c' + 1) * D := by
  have hLp : 1 ≤ L ^ c' := Nat.one_le_pow _ _ hL
  set P := t' * L ^ c' * D with hP
  have hP1 : 1 ≤ P := Nat.mul_pos (Nat.mul_pos ht' hLp) hD
  set Q := C' * Cτ * 4 ^ c' * 11 with hQ
  have h1 : L' ^ c' ≤ 4 ^ c' * L ^ c' := by
    rw [← mul_pow]
    exact Nat.pow_le_pow_left hL' _
  have h2 : T'' ≤ Q * P := by
    rw [hT]
    calc C' * t * L' ^ c' * (5 * D + 6)
        ≤ C' * (Cτ * t') * (4 ^ c' * L ^ c') * (11 * D) := by
          refine Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul_left _ ht) h1) (by omega)
      _ = Q * P := by
          rw [hQ, hP]
          ring
  have h3 : T'' + 1 ≤ (Q + 1) * P := by nlinarith
  have h4 : J * (T'' + 1) ≤ (K + 1) * L * ((Q + 1) * P) := Nat.mul_le_mul hJ h3
  have hR : t' * L ^ (c' + 1) * D = L * P := by
    rw [hP, pow_succ]
    ring
  have hRD : D ≤ L * P := by
    rw [← hR]
    have : 1 ≤ t' * L ^ (c' + 1) := Nat.mul_pos ht' (Nat.pow_pos hL)
    nlinarith
  have h5 : (2 + (K + 1) * (Q + 1) + 2 * C' * 4 ^ c' + 1) * t' * L ^ (c' + 1) * D =
      (2 + (K + 1) * (Q + 1) + 2 * C' * 4 ^ c' + 1) * (L * P) := by
    rw [← hR]
    ring
  rw [h5]
  have h6 : (K + 1) * L * ((Q + 1) * P) = (K + 1) * (Q + 1) * (L * P) := by ring
  have h7 : (2 + (K + 1) * (Q + 1) + 2 * C' * 4 ^ c' + 1) * (L * P) =
      2 * (L * P) + (K + 1) * (Q + 1) * (L * P) + (2 * C' * 4 ^ c' + 1) * (L * P) := by ring
  rw [h7]
  have h8 : 0 ≤ (2 * C' * 4 ^ c' + 1) * (L * P) := Nat.zero_le _
  omega

theorem whole_width_le {C' Cτ c' K L L' : ℕ} (hL : 1 ≤ L) (hL' : L' ≤ 4 * L) :
    C' * L' ^ c' + C' * L' ^ c' ≤
      (2 + (K + 1) * (C' * Cτ * 4 ^ c' * 11 + 1) + 2 * C' * 4 ^ c' + 1) * L ^ (c' + 1) := by
  have h1 : L' ^ c' ≤ 4 ^ c' * L ^ c' := by
    rw [← mul_pow]
    exact Nat.pow_le_pow_left hL' _
  have h2 : L ^ c' ≤ L ^ (c' + 1) := Nat.pow_le_pow_right hL (by omega)
  have h3 : C' * L' ^ c' ≤ C' * 4 ^ c' * L ^ (c' + 1) := by
    calc C' * L' ^ c' ≤ C' * (4 ^ c' * L ^ c') := Nat.mul_le_mul_left _ h1
      _ = C' * 4 ^ c' * L ^ c' := by ring
      _ ≤ _ := Nat.mul_le_mul_left _ h2
  have h4 : (2 + (K + 1) * (C' * Cτ * 4 ^ c' * 11 + 1) + 2 * C' * 4 ^ c' + 1) * L ^ (c' + 1) =
      (2 + (K + 1) * (C' * Cτ * 4 ^ c' * 11 + 1) + 1) * L ^ (c' + 1) +
        2 * (C' * 4 ^ c' * L ^ (c' + 1)) := by ring
  rw [h4]
  omega

end Arith

/-! ### The bounds -/

/-- **Maximum flow from negative weights.** -/
theorem maxFlowBound_of_neg {τ τ' : ℕ → ℕ} (h1 : ∀ n, 1 ≤ τ' (n + 2))
    (h2 : ∃ Cτ, ∀ n, τ (n * (n * 5) + 2) ≤ Cτ * τ' (n + 2)) (hN : NegSsspBound τ) :
    MaxFlowBound τ' := by
  intro K k
  obtain ⟨Cτ, hτ⟩ := h2
  obtain ⟨C', c', hP⟩ := hN (K + 1) (k + K + 1)
  refine ⟨2 + (K + 1) * (C' * Cτ * 4 ^ c' * 11 + 1) + 2 * C' * 4 ^ c' + 1, c' + 1, fun n D hD1 => ?_⟩
  obtain ⟨ρ', i1, i2, σ', P', out', hP'⟩ := hP (n * (n * 5)) (5 * D + 6) (by omega)
  have hcard : Fintype.card (Fin n × Fin n × Kind) = n * (n * 5) := by
    simp [Fintype.card_prod, Kind.card_eq]
  have hL := one_le_logN n
  have hw : 1 ≤ (2 + (K + 1) * (C' * Cτ * 4 ^ c' * 11 + 1) + 2 * C' * 4 ^ c' + 1) *
      logN n ^ (c' + 1) := Nat.mul_pos (by omega) (Nat.pow_pos hL)
  have hw' := whole_width_le (C' := C') (Cτ := Cτ) (c' := c') (K := K) hL (logN_dual n)
  have hb := whole_rounds_le (C' := C') (Cτ := Cτ) (c' := c') (K := K) (t' := τ' (n + 2))
    (J := Nat.log 2 (n * (n + 2) ^ K + 1) + 1) hL hD1 (h1 n) (hτ n) (logN_dual n)
    (search_rounds_le n K) rfl
  exact ⟨Fin n × Kind → ρ', inferInstance, inferInstance, _,
    (wholeAlg (Fintype.equivFinOfCardEq hcard) P' out'
      (C' * τ (n * (n * 5) + 2) * logN (n * (n * 5)) ^ c' * (5 * D + 6)) (n * (n + 2) ^ K + 1) D hw
      hw').stopAt _,
    fun v st => wholeOut (X := ℕ × (WholeIn n ρ' × FloodSt n))
      (Y := ℕ × ((WholeIn n ρ' × Option (Fin n)) × FloodSt n)) v st,
    fun N cap s t hPl hDN hcap hst =>
      maxFlow_count rfl hP' rfl rfl hb hPl hDN hcap hst⟩

/-- **Negative weights from exact shortest paths and the reduction.** -/
theorem negSsspBound_of_reduction {τ : ℕ → ℕ} (hE : ExactSsspBound) (hR : NegReduction τ) :
    NegSsspBound τ := by
  intro K k
  obtain ⟨C₁, c₁, hR'⟩ := hR K k
  obtain ⟨C₂, c₂, hE'⟩ := hE C₁
  refine ⟨C₁ * (C₁ + C₂) + C₁ + C₂, c₁ + c₂, fun n D hD => ?_⟩
  obtain ⟨σ, A, out, hA⟩ := hE' n D hD
  have hOK : ExactOracleOK n ((n + 2) ^ C₁) D (C₂ * logN n ^ c₂ * D) A (fun v s => (out v s).1) :=
    fun N ℓ φ hP hDN hV v => (hA N ℓ φ hP hDN hV).dist_eq v
  obtain ⟨ρ, i1, i2, σ', P, out', hP⟩ := hR' n D _ _ hD σ A _ hOK
  have hL := one_le_logN n
  have h1 : logN n ^ c₁ ≤ logN n ^ (c₁ + c₂) := Nat.pow_le_pow_right hL (by omega)
  have h2 : logN n ^ c₂ ≤ logN n ^ (c₁ + c₂) := Nat.pow_le_pow_right hL (by omega)
  have hw : C₂ * logN n ^ c₂ + C₁ * logN n ^ c₁ ≤
      (C₁ * (C₁ + C₂) + C₁ + C₂) * logN n ^ (c₁ + c₂) := by
    have h3 : C₂ * logN n ^ c₂ ≤ C₂ * logN n ^ (c₁ + c₂) := Nat.mul_le_mul_left _ h2
    have h4 : C₁ * logN n ^ c₁ ≤ C₁ * logN n ^ (c₁ + c₂) := Nat.mul_le_mul_left _ h1
    nlinarith [Nat.zero_le (C₁ * (C₁ + C₂) * logN n ^ (c₁ + c₂))]
  have hT : C₁ * τ (n + 2) * (C₂ * logN n ^ c₂ * D + C₁ * logN n ^ c₁ * D) ≤
      (C₁ * (C₁ + C₂) + C₁ + C₂) * τ (n + 2) * logN n ^ (c₁ + c₂) * D := by
    have h3 : C₂ * logN n ^ c₂ * D + C₁ * logN n ^ c₁ * D ≤ (C₁ + C₂) * (logN n ^ (c₁ + c₂) * D) := by
      have h5 : C₂ * logN n ^ c₂ * D ≤ C₂ * (logN n ^ (c₁ + c₂) * D) := by
        rw [mul_assoc]
        exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ h2)
      have h6 : C₁ * logN n ^ c₁ * D ≤ C₁ * (logN n ^ (c₁ + c₂) * D) := by
        rw [mul_assoc]
        exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ h1)
      nlinarith
    calc C₁ * τ (n + 2) * (C₂ * logN n ^ c₂ * D + C₁ * logN n ^ c₁ * D)
        ≤ C₁ * τ (n + 2) * ((C₁ + C₂) * (logN n ^ (c₁ + c₂) * D)) := Nat.mul_le_mul_left _ h3
      _ = C₁ * (C₁ + C₂) * τ (n + 2) * logN n ^ (c₁ + c₂) * D := by ring
      _ ≤ _ := by
          refine Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ ?_))
          omega
  refine ⟨ρ, i1, i2, _, (P.widen hw).stopAt
    (C₁ * τ (n + 2) * (C₂ * logN n ^ c₂ * D + C₁ * logN n ^ c₁ * D)),
    fun v st => out' v st.2, fun N w s hPl hDN hV => ?_⟩
  have hrun : ∀ inp v, (((P.widen hw).stopAt
      (C₁ * τ (n + 2) * (C₂ * logN n ^ c₂ * D + C₁ * logN n ^ c₁ * D))).run N.G inp
      ((C₁ * (C₁ + C₂) + C₁ + C₂) * τ (n + 2) * logN n ^ (c₁ + c₂) * D) v).2 =
      P.run N.G inp (C₁ * τ (n + 2) * (C₂ * logN n ^ c₂ * D + C₁ * logN n ^ c₁ * D)) v := by
    intro inp v
    rw [Algorithm.run_stopAt, min_eq_right hT, Algorithm.run_widen]
  simp only [hrun]
  exact hP N w s hPl hDN hV

/-- Given exact shortest paths, the reduction fails with the factor `0`, so it is not vacuous. -/
theorem not_negReduction_zero (hE : ExactSsspBound) : ¬ NegReduction (fun _ => 0) :=
  fun hR => not_negSsspBound_zero (negSsspBound_of_reduction hE hR)

/-- The instance with a polylogarithmic factor. -/
theorem maxFlowBound_polylog (c : ℕ) (h : NegSsspBound (tauPolylog c)) :
    MaxFlowBound (tauPolylog c) := by
  refine maxFlowBound_of_neg (fun n => Nat.one_le_pow _ _ (by omega)) ⟨4 ^ c, fun n => ?_⟩ h
  show (Nat.log 2 (n * (n * 5) + 2) + 1) ^ c ≤ 4 ^ c * (Nat.log 2 (n + 2) + 1) ^ c
  rw [← mul_pow]
  exact Nat.pow_le_pow_left (logN_dual n) _

/-- The instance with the factor `(log n)^(C √log n)`. -/
theorem maxFlowBound_subpoly (C : ℕ) (h : NegSsspBound (tauSubpoly C)) :
    MaxFlowBound (tauSubpoly (12 * C)) := by
  refine maxFlowBound_of_neg (fun n => Nat.one_le_pow _ _ (by omega)) ⟨1, fun n => ?_⟩ h
  rw [one_mul]
  show (Nat.log 2 (n * (n * 5) + 2) + 1) ^ (C * (Nat.sqrt (Nat.log 2 (n * (n * 5) + 2)) + 1)) ≤
    (Nat.log 2 (n + 2) + 1) ^ (12 * C * (Nat.sqrt (Nat.log 2 (n + 2)) + 1))
  have hd := logN_dual n
  unfold logN at hd
  set l' := Nat.log 2 (n * (n * 5) + 2) with hl'
  set l := Nat.log 2 (n + 2) with hl
  have hl1 : 1 ≤ l := Nat.log_pos (by norm_num) (by omega)
  have h1 : l' + 1 ≤ (l + 1) ^ 3 := by
    have h0 : 4 ≤ (l + 1) ^ 2 := by nlinarith
    calc l' + 1 ≤ 4 * (l + 1) := hd
      _ ≤ (l + 1) ^ 2 * (l + 1) := Nat.mul_le_mul_right _ h0
      _ = (l + 1) ^ 3 := by ring
  have h2 : Nat.sqrt l' ≤ 3 * (Nat.sqrt l + 1) := by
    have h3 : l < (Nat.sqrt l + 1) * (Nat.sqrt l + 1) := Nat.sqrt_lt.1 (Nat.lt_succ_self _)
    have h4 : l' < (3 * (Nat.sqrt l + 1) + 1) * (3 * (Nat.sqrt l + 1) + 1) := by nlinarith
    exact Nat.lt_succ_iff.1 (Nat.sqrt_lt.2 h4)
  calc (l' + 1) ^ (C * (Nat.sqrt l' + 1)) ≤ ((l + 1) ^ 3) ^ (C * (Nat.sqrt l' + 1)) :=
        Nat.pow_le_pow_left h1 _
    _ = (l + 1) ^ (3 * (C * (Nat.sqrt l' + 1))) := (pow_mul _ _ _).symm
    _ ≤ (l + 1) ^ (12 * C * (Nat.sqrt l + 1)) := by
        refine Nat.pow_le_pow_right (by omega) ?_
        nlinarith

/-- **Negative weights and maximum flow from the labels, with the factor `(log n)^c`.** -/
theorem negFlow_polylog (c : ℕ) (hL : LabelHypothesis) (hA : AggBox) (hS : SmoothingBox)
    (hR : NegReduction (tauPolylog c)) :
    NegSsspBound (tauPolylog c) ∧ MaxFlowBound (tauPolylog c) :=
  have h := negSsspBound_of_reduction (exactSsspBound hL hA hS) hR
  ⟨h, maxFlowBound_polylog c h⟩

/-- **Negative weights and maximum flow from the labels, with the factor `(log n)^(C √log n)`.** -/
theorem negFlow_subpoly (C : ℕ) (hL : LabelHypothesis) (hA : AggBox) (hS : SmoothingBox)
    (hR : NegReduction (tauSubpoly C)) :
    NegSsspBound (tauSubpoly C) ∧ MaxFlowBound (tauSubpoly (12 * C)) :=
  have h := negSsspBound_of_reduction (exactSsspBound hL hA hS) hR
  ⟨h, maxFlowBound_subpoly C h⟩

end SsspFlow.Congest
