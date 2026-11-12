import QuantumBranching.Levels
import QuantumBranching.Semantics

/-!
# What is taken as hypothesis

This file does not define a circuit model. `Primitives` records, for instances of size `n`, the
running time and the probabilities of the quantum primitives, as real functions. The named hypotheses
below bound them. They are not proved. They are `Prop`s passed as arguments, not axioms.

- `WalkBound`: the walk on a computation tree. For every `T' ≥ T`, where `T` is the sum of the squared
  step counts, it takes at most `κ n * √(T' * D)` steps, and it accepts with probability at least `1/2`
  if a marked leaf exists and at most `1/4` otherwise.
- `ErrorReduction`: alternating projections, `r` rounds on one register, at most `r` new bits, and
  error at most `exp (-r / 32)` against the threshold `3/8`.
- `AmplitudeError`: a step with error probability `err` is within amplitude `√(2 * err)` of the exact
  step.
- `Pebbling`: a classical run of time `τ` is made reversible by pebbling, in time
  `η n * τ ^ 1.585 * (1 + log τ) ^ d`.

`Setting` holds an abstract procedure with its measure and its constants, and `Conditions` the model
of the procedure and the conditions (M1), (M2) and (M3). (M1) quantifies over the antichains of the
OR-tree of the root and of every target of a value call. (M3) bounds the weight `fullWeight`, the sum
over the full call tree, along the OR, tail and value edges, of one for each node plus `B a` for each
Box node `a`.

`QBound` says that a power `N ^ q` dominates all the polynomial constants.

`hypotheses_satisfiable` and `setting_satisfiable` show that these hypotheses are consistent, for
every value of the measure, so including instances above the base. `M3_box_gap` shows why (M3) must
count Box nodes: (M1), (M2) and a bound for the nodes without a Box below them do not bound the run on
a node with a Box below it.
-/

open Real

namespace QuantumBranching

/-- `f` is bounded by a polynomial in `n`. -/
def IsPoly (f : ℕ → ℝ) : Prop := ∃ (C : ℝ) (k : ℕ), 0 ≤ C ∧ ∀ n, |f n| ≤ C * ((n : ℝ) + 1) ^ k

/-- The running times and the probabilities of the primitives, for instances of size `n`. -/
structure Primitives where
  /-- The time of the walk with parameter `T'` on a tree of depth at most `D`. -/
  walkTime : ℕ → ℝ → ℝ → ℝ
  /-- The acceptance probability of the walk, for a tree of sum `T`, with parameter `T'`, of depth at
  most `D`, with or without a marked leaf. -/
  walkAccept : ℕ → ℝ → ℝ → ℝ → Bool → ℝ
  /-- The error after `r` rounds of alternating projections. -/
  boostError : ℕ → ℕ → ℝ
  /-- The new bits of `r` rounds of alternating projections. -/
  boostBits : ℕ → ℕ → ℝ
  /-- The amplitude distance of a step with error probability `err` from the exact step. -/
  stepDefect : ℕ → ℝ → ℝ
  /-- The time of the reversible form of a classical run of time `τ`. -/
  pebble : ℕ → ℝ → ℝ
  walkTime_nonneg : ∀ n T D, 0 ≤ walkTime n T D
  pebble_nonneg : ∀ n τ, 0 ≤ pebble n τ

/-- **The walk on a computation tree.** -/
def WalkBound (G : Primitives) (κ : ℕ → ℝ) : Prop :=
  ∀ n T T' D, 0 ≤ T → T ≤ T' → 1 ≤ T' → 1 ≤ D →
    G.walkTime n T' D ≤ κ n * √(T' * D) ∧
      1 / 2 ≤ G.walkAccept n T T' D true ∧ G.walkAccept n T T' D false ≤ 1 / 4

/-- **Error reduction in place.** -/
def ErrorReduction (G : Primitives) : Prop :=
  ∀ n r, G.boostError n r ≤ exp (-(r : ℝ) / 32) ∧ G.boostBits n r ≤ r

/-- **The amplitude error of a step.** -/
def AmplitudeError (G : Primitives) : Prop :=
  ∀ n err, 0 ≤ err → G.stepDefect n err ≤ √(2 * err)

/-- **Pebbling.** A classical run of time `τ ≥ 1` has a reversible form of size
`η n * τ ^ 1.585 * (1 + log τ) ^ d`. The exponent is above `log₂ 3`. -/
def Pebbling (G : Primitives) (η : ℕ → ℝ) (d : ℕ) : Prop :=
  ∀ n τ, 1 ≤ τ → G.pebble n τ ≤ η n * τ ^ ((1585 : ℝ) / 1000) * (1 + log τ) ^ d

/-- The hypotheses on `Primitives` are jointly satisfiable. -/
theorem hypotheses_satisfiable :
    ∃ (G : Primitives) (κ η : ℕ → ℝ) (d : ℕ), IsPoly κ ∧ IsPoly η ∧ (∀ n, 1 ≤ η n) ∧
      WalkBound G κ ∧ ErrorReduction G ∧ AmplitudeError G ∧ Pebbling G η d := by
  refine ⟨⟨fun _ _ _ => 0, fun _ _ _ _ b => if b then 1 else 0, fun _ _ => 0, fun _ _ => 0,
    fun _ _ => 0, fun _ _ => 0, fun _ _ _ => le_rfl, fun _ _ => le_rfl⟩,
    fun _ => 0, fun _ => 1, 0, ⟨0, 0, le_rfl, by simp⟩,
    ⟨1, 0, zero_le_one, by simp⟩, fun _ => le_rfl, ?_, ?_, ?_, ?_⟩
  · intro n T T' D _ _ _ _
    norm_num
  · intro n r
    exact ⟨(exp_pos _).le, Nat.cast_nonneg _⟩
  · intro n err _
    exact Real.sqrt_nonneg _
  · intro n τ hτ
    have : 0 ≤ τ ^ ((1585 : ℝ) / 1000) := Real.rpow_nonneg (by linarith) _
    simpa using this

namespace Proc

variable {I : Type*} (P : Proc I)

/-- Whether a node runs a Box. -/
def boxFlag (a : I) : Bool :=
  match P.step a with
  | .box _ => true
  | _ => false

/-- The children of a node in the OR-tree, as a list of instances. -/
def children (x : I) : List I :=
  match P.outcome x with
  | .inl _ => []
  | .inr cs => cs

theorem rank_children {x c : I} (h : c ∈ P.children x) : P.rank c < P.rank x := by
  unfold children at h
  cases ho : P.outcome x with
  | inl b => simp [ho] at h
  | inr cs =>
    simp only [ho] at h
    exact P.rank_child ho h

/-- The sum of the weight `w` over the full call tree of `x`, along OR, tail and value edges, with
repetition. The rank tests always succeed. -/
noncomputable def callSum (w : I → ℝ) (x : I) : ℝ :=
  w x + ((P.calls x).map fun y => if P.rank y < P.rank x then callSum w y else 0).sum +
    ((P.children x).map fun c => if P.rank c < P.rank x then callSum w c else 0).sum
termination_by P.rank x
decreasing_by all_goals assumption

theorem callSum_eq (w : I → ℝ) (x : I) :
    P.callSum w x = w x + ((P.calls x).map (P.callSum w)).sum +
      ((P.children x).map (P.callSum w)).sum := by
  have h1 : ((P.calls x).map fun y => if P.rank y < P.rank x then P.callSum w y else 0) =
      (P.calls x).map (P.callSum w) :=
    List.map_congr_left fun y hy => by simp [P.rank_call hy]
  have h2 : ((P.children x).map fun c => if P.rank c < P.rank x then P.callSum w c else 0) =
      (P.children x).map (P.callSum w) :=
    List.map_congr_left fun c hc => by simp [P.rank_children hc]
  rw [callSum, h1, h2]

/-- The sum over the full call tree is monotone, up to a constant factor. -/
theorem callSum_le {w w' : I → ℝ} {C : ℝ} (hle : ∀ a, w a ≤ C * w' a) (x : I) :
    P.callSum w x ≤ C * P.callSum w' x := by
  induction hk : P.rank x using Nat.strong_induction_on generalizing x with
  | _ k ih =>
    rw [P.callSum_eq w x, P.callSum_eq w' x]
    have h1 : ((P.calls x).map (P.callSum w)).sum ≤ C * ((P.calls x).map (P.callSum w')).sum := by
      rw [← List.sum_map_mul_left]
      exact list_map_sum_le fun y hy => ih _ (hk ▸ P.rank_call hy) y rfl
    have h2 : ((P.children x).map (P.callSum w)).sum ≤
        C * ((P.children x).map (P.callSum w')).sum := by
      rw [← List.sum_map_mul_left]
      exact list_map_sum_le fun c hc => ih _ (hk ▸ P.rank_children hc) c rfl
    have h3 := hle x
    nlinarith

end Proc

/-- A procedure with its measure and its constants. -/
structure Setting (I : Type*) where
  /-- The procedure. -/
  proc : Proc I
  /-- The measure. -/
  B : I → ℝ
  /-- The time of the Box at a Box node. -/
  boxTime : I → ℝ
  /-- The bound on the depth. -/
  D : ℕ
  /-- The bound on the number of children. -/
  t : ℕ
  /-- The bound on the number of value calls at a node. -/
  s : ℕ
  /-- The constant of (M1) and (M3). -/
  K : ℝ
  /-- The constant of (M2). -/
  c : ℝ
  /-- The polynomial factor in the time of a Box. -/
  ρ : ℝ
  /-- The local work at a node. -/
  loc : ℝ
  /-- The number of rounds of error reduction. -/
  r : ℕ
  /-- The instance of the whole search. -/
  root : I

namespace Setting

variable {I : Type*} (S : Setting I)

/-- The instances that are searched: the root and every target of a value call. -/
def Searched (x : I) : Prop := x = S.root ∨ ∃ v, x ∈ S.proc.calls v

/-- The weight of (M3): one for each node, plus `B a` for a Box node. -/
noncomputable def m3Weight (a : I) : ℝ := 1 + if S.proc.boxFlag a then S.B a else 0

/-- The quantity bounded by (M3). -/
noncomputable def fullWeight (x : I) : ℝ := S.proc.callSum S.m3Weight x

/-- The time of a Box, with its error reduced, at a Box node, and zero elsewhere. -/
noncomputable def boxCost (a : I) : ℝ := if S.proc.boxFlag a then (S.r : ℝ) * S.boxTime a else 0

/-- The time of the classical run: the local work at each node of the full call tree, plus each Box. -/
noncomputable def runTime (x : I) : ℝ := S.proc.callSum (fun a => S.loc + S.boxCost a) x

/-- The model of the procedure and the conditions (M1), (M2) and (M3). -/
structure Conditions : Prop where
  B_ge : ∀ x, 2 ≤ S.B x
  /-- The depth is bounded. -/
  rank_le : ∀ x, S.proc.rank x ≤ S.D
  /-- The number of children is bounded. -/
  width_le : ∀ x, (S.proc.children x).length ≤ S.t
  /-- The number of value calls is bounded. -/
  calls_le : ∀ x, (S.proc.calls x).length ≤ S.s
  /-- The time of a Box. -/
  box_time : ∀ a, S.proc.boxFlag a = true → 0 ≤ S.boxTime a ∧ S.boxTime a ≤ S.ρ * √(S.B a)
  ρ_nonneg : 0 ≤ S.ρ
  loc_ge : 1 ≤ S.loc
  /-- (M1). -/
  M1 : ∀ x, S.Searched x → ∀ l, (S.proc.orTree x).IsAntichain l → (l.map S.B).sum ≤ S.K * S.B x
  /-- (M2). -/
  M2 : ∀ v, ∀ y ∈ S.proc.calls v, log (S.B y) ≤ (3 / 4) * log (S.B v) + S.c
  /-- (M3). -/
  M3 : ∀ x, S.fullWeight x ≤ S.K * S.B x

/-- The power `N ^ q` dominates all the polynomial constants. `κ` is the overhead of the walk, and `η`
and `d` are those of pebbling. `base_sq` holds once `N` is large against `W q`, by a factor `N ^ (2 * d)`
that depends neither on `W` nor on `A`. -/
structure QBound (N : ℝ) (q : ℕ) (κ η : ℝ) (d : ℕ) : Prop where
  N_ge : 4 ≤ N
  q_pos : 1 ≤ q
  K_ge : 1 ≤ S.K
  η_nonneg : 0 ≤ η
  c_le : S.c ≤ q * log N
  /-- The constant of (M1), across depths. -/
  depth_le : ((S.D : ℝ) + 1) * S.K ≤ N ^ q
  t_le : (S.t : ℝ) + 1 ≤ N ^ q
  /-- The value calls in a step. -/
  calls_sq : 12 * (S.s : ℝ) ^ 2 ≤ N ^ (2 * q)
  /-- The walk, squared, with its error reduction. -/
  walk_sq : ((S.r : ℝ) * κ) ^ 2 * ((S.D : ℝ) + 1) ≤ N ^ (2 * q)
  /-- The local work in a step. -/
  loc_sq : 12 * S.loc ^ 2 ≤ N ^ q
  /-- A Box in a step. -/
  box_sq : 12 * ((S.r : ℝ) * S.ρ) ^ 2 ≤ N ^ q
  /-- The steps of the classical run, against `B x`. -/
  run_le : (S.loc + S.r * S.ρ) * S.K ≤ N ^ q
  /-- The overhead of pebbling at the base. -/
  base_sq : η ^ 2 * (1 + ((q + W q : ℕ) : ℝ) * log N) ^ (2 * d) ≤ N ^ q

end Setting

namespace Examples

/-- A one point procedure, with measure `b`. -/
noncomputable def pointSetting (b : ℝ) : Setting Unit where
  proc := ⟨fun _ => .leaf true, fun _ => 0, by simp, by simp⟩
  B := fun _ => b
  boxTime := fun _ => 0
  D := 0
  t := 1
  s := 0
  K := 1
  c := 0
  ρ := 1
  loc := 1
  r := 1
  root := ()

theorem point_outcome (b : ℝ) (x : Unit) :
    (pointSetting b).proc.outcome x = .inl true := rfl

theorem point_calls (b : ℝ) (x : Unit) : (pointSetting b).proc.calls x = [] := rfl

theorem point_children (b : ℝ) (x : Unit) : (pointSetting b).proc.children x = [] := rfl

theorem point_boxFlag (b : ℝ) (x : Unit) : (pointSetting b).proc.boxFlag x = false := rfl

/-- The only antichains of a node with one added leaf are the empty one and the root. -/
theorem antichain_of_mark {I : Type*} {a : I} {b : Bool} {l : List I}
    (h : (ORTree.node a [.mark b]).IsAntichain l) : l = [] ∨ l = [a] := by
  cases h with
  | nil => exact .inl rfl
  | root => exact .inr rfl
  | sub _ _ _ hl =>
    cases hl with
    | cons _ _ l₁ l₂ h₁ h₂ =>
      cases h₂ with
      | nil =>
        cases h₁ with
        | nil => exact .inl rfl

end Examples

/-- The conditions and the bound by powers of `N` are jointly satisfiable, for every value of the
measure, so also above the base. -/
theorem setting_satisfiable (b : ℝ) (hb : 2 ≤ b) :
    (Examples.pointSetting b).Conditions ∧ (Examples.pointSetting b).QBound 4 3 0 1 0 := by
  constructor
  · refine ⟨fun _ => hb, fun _ => le_rfl, fun x => ?_, fun x => ?_, fun a ha => ?_, zero_le_one,
      le_rfl, fun x _ l hl => ?_, fun v y hy => ?_, fun x => ?_⟩
    · rw [Examples.point_children]; simp [Examples.pointSetting]
    · rw [Examples.point_calls]; simp
    · rw [Examples.point_boxFlag] at ha; simp at ha
    · rw [(Examples.pointSetting b).proc.orTree_inl (Examples.point_outcome b x)] at hl
      rcases Examples.antichain_of_mark hl with rfl | rfl
      · have : (0 : ℝ) ≤ b := by linarith
        simpa [Examples.pointSetting] using this
      · simp [Examples.pointSetting]
    · rw [Examples.point_calls] at hy; simp at hy
    · unfold Setting.fullWeight
      rw [Proc.callSum_eq, Examples.point_calls, Examples.point_children]
      simp only [Setting.m3Weight, Examples.point_boxFlag]
      simp [Examples.pointSetting]
      linarith
  · have hlog : (0 : ℝ) ≤ log 4 := Real.log_nonneg (by norm_num)
    refine ⟨le_rfl, by norm_num, ?_, zero_le_one, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      norm_num [Examples.pointSetting, hlog]

namespace Examples

/-- Nested value calls of constant measure, with a Box at the bottom. -/
def nestedProc : Proc ℕ where
  step
    | 0 => .box false
    | d + 1 => .seq (.call d fun _ => .call d fun _ => .ret false)
  rank := id
  rank_or := by
    intro x cs h
    cases x <;> simp at h
  rank_seq := by
    intro x p h
    cases x with
    | zero => simp at h
    | succ d =>
      simp only [Case.seq.injEq] at h
      subst h
      simp [SeqProg.Below]

theorem nested_answer (d : ℕ) : nestedProc.answer d = false := by
  cases d with
  | zero => exact nestedProc.answer_box (b := false) rfl
  | succ d =>
    rw [nestedProc.answer_seq (p := .call d fun _ => .call d fun _ => .ret false) rfl]
    rfl

theorem nested_calls (d : ℕ) : nestedProc.calls (d + 1) = [d, d] := by
  show (SeqProg.call d fun _ => SeqProg.call d fun _ => SeqProg.ret false).calls nestedProc.answer
    = [d, d]
  simp [SeqProg.calls]

theorem nested_calls_zero : nestedProc.calls 0 = [] := rfl

theorem nested_outcome (d : ℕ) : nestedProc.outcome d = .inl false := by
  cases d with
  | zero => rfl
  | succ d => rfl

theorem nested_children (d : ℕ) : nestedProc.children d = [] := by
  unfold Proc.children
  rw [nested_outcome]

theorem nested_hasBox (d : ℕ) : nestedProc.HasBox d := by
  induction d with
  | zero => exact .here (b := false) rfl
  | succ d ih => exact .call (by rw [nested_calls]; simp) ih

/-- The size of the full call tree of a node of rank `d` is at least `2 ^ d`. -/
theorem nested_callSum (d : ℕ) : (2 : ℝ) ^ d ≤ nestedProc.callSum (fun _ => 1) d := by
  induction d with
  | zero =>
    rw [Proc.callSum_eq, nested_calls_zero, nested_children]
    simp
  | succ d ih =>
    rw [Proc.callSum_eq, nested_calls, nested_children]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, pow_succ]
    linarith

end Examples

/-- **Why (M3) counts the full call tree.** For the constant measure `2`, nested value calls with a Box at the bottom
satisfy (M1) and (M2), every node has a Box below it, so a bound on nodes without a Box below them says
nothing, and the full call tree of a node of rank `d` has at least `2 ^ d` nodes. -/
theorem M3_box_gap :
    (∀ x l, (Examples.nestedProc.orTree x).IsAntichain l →
      (l.map fun _ => (2 : ℝ)).sum ≤ 1 * 2) ∧
    (∀ v, ∀ y ∈ Examples.nestedProc.calls v, log (2 : ℝ) ≤ (3 / 4) * log 2 + 1) ∧
    (∀ x, Examples.nestedProc.HasBox x) ∧
    (∀ d, (2 : ℝ) ^ d ≤ Examples.nestedProc.callSum (fun _ => 1) d) := by
  refine ⟨fun x l hl => ?_, fun _ _ _ => ?_, Examples.nested_hasBox, Examples.nested_callSum⟩
  · rw [Examples.nestedProc.orTree_inl (Examples.nested_outcome x)] at hl
    rcases Examples.antichain_of_mark hl with rfl | rfl <;> norm_num
  · have h1 : log (2 : ℝ) ≤ 2 - 1 := Real.log_le_sub_one_of_pos (by norm_num)
    linarith

end QuantumBranching
