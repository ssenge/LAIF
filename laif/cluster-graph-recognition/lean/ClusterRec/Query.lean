import Mathlib

/-!
# The quantum query model, the OR lower bound, and the reduction from OR on a family of graphs

The definitions and the reduction are those of the `GraphClasses` library in the folder
`threshold-graph-recognition-queries` of this repository, restated in the namespace `ClusterRec`.

An input is a bit string `x : Q → Bool`. A query is a phase `(-1)^{x q}` on basis states that name a position `q`, and
is trivial on the others. A `T`-query algorithm alternates `T + 1` unitaries with `T` queries, and measures. The OR
lower bound is taken as the named hypothesis `ORLowerBound`.
-/

open Finset

namespace ClusterRec
/-- A `T`-query quantum algorithm on the basis `S` with outputs in `O`. -/
structure QAlg (Q : Type) (T : ℕ) (S : Type) [Fintype S] [DecidableEq S] (O : Type) where
  /-- The position queried on a basis state, if any. -/
  ix : S → Option Q
  U : Fin (T + 1) → Matrix.unitaryGroup S ℂ
  init : S
  out : S → O

variable {Q : Type} {S : Type} [Fintype S] [DecidableEq S] {O : Type} {T : ℕ}

/-- The phase of a query on a basis state. -/
def QAlg.phase (A : QAlg Q T S O) (x : Q → Bool) (b : S) : ℂ :=
  match A.ix b with
  | none => 1
  | some q => if x q then -1 else 1

/-- The state after `U_t O U_{t-1} ⋯ O U_0` applied to the initial basis state. -/
noncomputable def QAlg.state (A : QAlg Q T S O) (x : Q → Bool) : (t : ℕ) → t ≤ T → S → ℂ
  | 0, _ => (A.U ⟨0, Nat.succ_pos T⟩ : Matrix S S ℂ).mulVec (Pi.single A.init 1)
  | t + 1, h => (A.U ⟨t + 1, Nat.succ_lt_succ h⟩ : Matrix S S ℂ).mulVec
      fun b => A.phase x b * A.state x t (Nat.le_of_succ_le h) b

open Classical in
/-- The probability that the final measurement reports `o`. -/
noncomputable def QAlg.prob (A : QAlg Q T S O) (x : Q → Bool) (o : O) : ℝ :=
  ∑ b, if A.out b = o then Complex.normSq (A.state x T le_rfl b) else 0

/-- The bit string with a single `1`, at `i`. -/
def singleBit {N : ℕ} (i : Fin N) (j : Fin N) : Bool := decide (j = i)

/-- The OR lower bound with the constant `c`. -/
def ORBound (c : ℝ) : Prop :=
  ∀ (N T : ℕ) (S : Type) (_ : Fintype S) (_ : DecidableEq S) (A : QAlg (Fin N) T S Bool),
    2 / 3 ≤ A.prob (fun _ => false) false →
    (∀ i : Fin N, 2 / 3 ≤ A.prob (singleBit i) true) →
    c * Real.sqrt N ≤ T

/-- **The OR lower bound.** An algorithm that tells the zero string from
every string with a single `1`, with error at most `1/3`, needs `Ω(√N)` queries. -/
def ORLowerBound : Prop := ∃ c : ℝ, 0 < c ∧ ORBound c

section Sim

variable {Q : Type} {S : Type} [Fintype S] [DecidableEq S] {T N : ℕ}

/-- The hidden bit behind a query position, if any. -/
def bitOf (loc : Q → Option (Fin N)) (z : Fin N → Bool) (q : Q) : Bool :=
  match loc q with
  | none => false
  | some i => z i

/-- The input for the hidden string `z`: the known `base`, flipped where the hidden bit is `1`. -/
def familyInput (base : Q → Bool) (loc : Q → Option (Fin N)) (z : Fin N → Bool) (q : Q) : Bool :=
  xor (base q) (bitOf loc z q)

/-- The known sign of a query on a basis state. -/
def signOf (A : QAlg Q T S Bool) (base : Q → Bool) (b : S) : ℂ :=
  match A.ix b with
  | none => 1
  | some q => if base q then -1 else 1

theorem signOf_mem (A : QAlg Q T S Bool) (base : Q → Bool) :
    Matrix.diagonal (signOf A base) ∈ Matrix.unitaryGroup S ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose,
    Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext b
  simp only [Pi.star_apply, signOf]
  cases A.ix b with
  | none => simp
  | some q => cases h : base q <;> simp [h]

/-- The simulation: query the hidden bit, apply the known sign before the next unitary, and negate the output. -/
noncomputable def simAlg (A : QAlg Q T S Bool) (base : Q → Bool) (loc : Q → Option (Fin N)) :
    QAlg (Fin N) T S Bool where
  ix b := (A.ix b).bind loc
  U t := if t.val = 0 then A.U t else A.U t * ⟨Matrix.diagonal (signOf A base), signOf_mem A base⟩
  init := A.init
  out b := !A.out b

theorem sim_phase (A : QAlg Q T S Bool) (base : Q → Bool) (loc : Q → Option (Fin N)) (z : Fin N → Bool) (b : S) :
    A.phase (familyInput base loc z) b = signOf A base b * (simAlg A base loc).phase z b := by
  cases hb : A.ix b with
  | none => simp [QAlg.phase, signOf, simAlg, hb]
  | some q =>
    obtain hl | ⟨i, hl⟩ : loc q = none ∨ ∃ i, loc q = some i := by
      cases loc q <;> simp
    · have hbit : bitOf loc z q = false := by simp [bitOf, hl]
      simp only [QAlg.phase, signOf, simAlg, hb, Option.bind_some, familyInput, hbit, hl]
      cases h : base q <;> simp
    · have hbit : bitOf loc z q = z i := by simp [bitOf, hl]
      simp only [QAlg.phase, signOf, simAlg, hb, Option.bind_some, familyInput, hbit, hl]
      cases h : base q <;> cases h' : z i <;> simp

theorem sim_state (A : QAlg Q T S Bool) (base : Q → Bool) (loc : Q → Option (Fin N)) (z : Fin N → Bool) :
    ∀ (t : ℕ) (h : t ≤ T), (simAlg A base loc).state z t h = A.state (familyInput base loc z) t h := by
  intro t
  induction t with
  | zero =>
    intro h
    simp only [QAlg.state, simAlg, if_true]
  | succ t ih =>
    intro h
    simp only [QAlg.state]
    rw [ih]
    have hU : ((simAlg A base loc).U ⟨t + 1, Nat.succ_lt_succ h⟩ : Matrix S S ℂ) =
        (A.U ⟨t + 1, Nat.succ_lt_succ h⟩ : Matrix S S ℂ) * Matrix.diagonal (signOf A base) := by
      simp [simAlg]
    rw [hU, ← Matrix.mulVec_mulVec]
    congr 1
    funext b
    rw [Matrix.mulVec_diagonal, sim_phase]
    ring

theorem sim_prob (A : QAlg Q T S Bool) (base : Q → Bool) (loc : Q → Option (Fin N)) (z : Fin N → Bool) (o : Bool) :
    (simAlg A base loc).prob z o = A.prob (familyInput base loc z) (!o) := by
  simp only [QAlg.prob, sim_state]
  refine sum_congr rfl fun b _ => ?_
  have hout : (simAlg A base loc).out b = !A.out b := rfl
  rw [hout]
  cases A.out b <;> cases o <;> simp

/-- **The reduction.** An algorithm that accepts `base` and rejects each single flip gives OR on the hidden bits. -/
theorem family_lower_bound {c : ℝ} (hc : ORBound c) (A : QAlg Q T S Bool) (base : Q → Bool)
    (loc : Q → Option (Fin N)) (h0 : 2 / 3 ≤ A.prob (familyInput base loc fun _ => false) true)
    (h1 : ∀ i, 2 / 3 ≤ A.prob (familyInput base loc (singleBit i)) false) : c * Real.sqrt N ≤ T := by
  refine hc N T S inferInstance inferInstance (simAlg A base loc) ?_ fun i => ?_
  · rw [sim_prob]
    exact h0
  · rw [sim_prob]
    exact h1 i

end Sim

/-- The pairs of the hard family. -/
def hardPairs (n : ℕ) : Finset (Fin n × Fin n) :=
  univ.filter fun e => e.1.val % 2 = 0 ∧ e.2.val % 2 = 1 ∧ e.1.val + 3 ≤ e.2.val

/-- There are at most `n²` pairs. -/
theorem hardPairs_card_le (n : ℕ) : (hardPairs n).card ≤ n ^ 2 := by
  calc (hardPairs n).card ≤ (univ : Finset (Fin n × Fin n)).card := card_filter_le _ _
    _ = n ^ 2 := by simp [sq]

/-- There are at least `(n / 4)²` pairs: with `k = n / 4`, take `i = 2 s` and `j = 2 (k + t) + 1` for `s, t < k`. -/
theorem hardPairs_card_ge (n : ℕ) : (n / 4) ^ 2 ≤ (hardPairs n).card := by
  set k := n / 4 with hk
  have hk4 : 4 * k ≤ n := by omega
  let f : Fin k × Fin k → Fin n × Fin n := fun e =>
    (⟨2 * e.1.val, by have := e.1.isLt; omega⟩, ⟨2 * (k + e.2.val) + 1, by have := e.2.isLt; omega⟩)
  have hinj : Function.Injective f := by
    rintro ⟨a, b⟩ ⟨c, d⟩ h
    simp only [f, Prod.mk.injEq, Fin.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    have e1 : a = c := Fin.ext (by omega)
    have e2 : b = d := Fin.ext (by omega)
    rw [e1, e2]
  have hmaps : ∀ e ∈ (univ : Finset (Fin k × Fin k)), f e ∈ hardPairs n := by
    rintro ⟨a, b⟩ _
    simp only [hardPairs, mem_filter, mem_univ, true_and, f]
    have := a.isLt
    omega
  have := card_le_card_of_injOn f hmaps (hinj.injOn)
  simpa [sq] using this

/-- **The count.** `Θ(n²)`: for `n ≥ 4`, between `n² / 64` and `n²`. -/
theorem hardPairs_theta {n : ℕ} (hn : 4 ≤ n) : n ^ 2 ≤ 64 * (hardPairs n).card ∧ (hardPairs n).card ≤ n ^ 2 := by
  refine ⟨?_, hardPairs_card_le n⟩
  have h1 := hardPairs_card_ge n
  have h2 : n ≤ 8 * (n / 4) := by omega
  calc n ^ 2 ≤ (8 * (n / 4)) ^ 2 := Nat.pow_le_pow_left h2 2
    _ = 64 * (n / 4) ^ 2 := by ring
    _ ≤ _ := Nat.mul_le_mul_left _ h1

/-- The adjacency matrix as a function on ordered pairs. -/
def pairFn {V : Type*} (G : SimpleGraph V) [DecidableRel G.Adj] (e : V × V) : Bool := decide (G.Adj e.1 e.2)

/-- The count gives `√N ≥ n / 8`. -/
theorem sqrt_hardPairs {n : ℕ} (hn : 4 ≤ n) : (n : ℝ) / 8 ≤ Real.sqrt (hardPairs n).card := by
  apply Real.le_sqrt_of_sq_le
  have := (hardPairs_theta hn).1
  have h : ((n : ℝ)) ^ 2 ≤ 64 * ((hardPairs n).card : ℝ) := by exact_mod_cast this
  nlinarith

/-- The two orders of a pair of the hard family cannot both be pairs of the hard family. -/
private theorem swap_not_mem {n : ℕ} {q : Fin n × Fin n} (h : q ∈ hardPairs n) : q.swap ∉ hardPairs n := by
  intro h'
  have h1 := (mem_filter.1 h).2.2.2
  have h2 := (mem_filter.1 h').2.2.2
  simp only [Prod.fst_swap, Prod.snd_swap] at h2
  omega

/-! ## Graphs -/

/-- The hidden bit of a pair, in either order. -/
noncomputable def graphLoc (n : ℕ) (q : Fin n × Fin n) : Option (Fin (hardPairs n).card) :=
  if h : q ∈ hardPairs n then some ((hardPairs n).equivFin ⟨q, h⟩)
  else if h' : q.swap ∈ hardPairs n then some ((hardPairs n).equivFin ⟨q.swap, h'⟩)
  else none

theorem graphLoc_eq_some {n : ℕ} {q : Fin n × Fin n} {i : Fin (hardPairs n).card} :
    graphLoc n q = some i ↔
      q = ((hardPairs n).equivFin.symm i).1 ∨ q = ((hardPairs n).equivFin.symm i).1.swap := by
  set e := ((hardPairs n).equivFin.symm i) with he
  have hval : (hardPairs n).equivFin e = i := by simp [he]
  have he2 : e.1 ∈ hardPairs n := e.2
  constructor
  · intro h
    unfold graphLoc at h
    split_ifs at h with h1 h2
    · left
      have h3 := Option.some.inj h
      have h4 : (⟨q, h1⟩ : hardPairs n) = e := by
        rw [he, ← h3]
        simp
      exact congrArg Subtype.val h4
    · right
      have h3 := Option.some.inj h
      have h4 : (⟨q.swap, h2⟩ : hardPairs n) = e := by
        rw [he, ← h3]
        simp
      have h5 := congrArg Subtype.val h4
      simp only at h5
      rw [← h5, Prod.swap_swap]
  · rintro (h | h)
    · subst h
      unfold graphLoc
      rw [dif_pos he2]
      exact congrArg some hval
    · have hq : q ∉ hardPairs n := by
        rw [h]
        exact swap_not_mem he2
      have hsw : q.swap = e.1 := by
        rw [h, Prod.swap_swap]
      unfold graphLoc
      rw [dif_neg hq, dif_pos (hsw ▸ he2)]
      refine congrArg some ?_
      rw [← hval]
      congr 1
      exact Subtype.ext hsw

/-- The bit behind a pair, for a single `1`. -/
theorem bitOf_single_graph {n : ℕ} (i : Fin (hardPairs n).card) (q : Fin n × Fin n) :
    bitOf (graphLoc n) (singleBit i) q = true ↔ graphLoc n q = some i := by
  unfold bitOf
  cases h : graphLoc n q with
  | none => simp
  | some j => simp [singleBit]

/-- **The lower bound for a class of graphs containing `G₀`, and missing `G₀` minus any edge of the hard family.** -/
theorem graph_lower_bound {c : ℝ} (hc : ORBound c) {n T : ℕ} {S : Type} [Fintype S] [DecidableEq S]
    (A : QAlg (Fin n × Fin n) T S Bool) (Cl : SimpleGraph (Fin n) → Prop) (G₀ : SimpleGraph (Fin n))
    (hadj : ∀ e ∈ hardPairs n, G₀.Adj e.1 e.2) (h0 : Cl G₀)
    (h1 : ∀ e ∈ hardPairs n, ¬ Cl (G₀.deleteEdges {s(e.1, e.2)}))
    (hA : ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      (Cl G → 2 / 3 ≤ A.prob (pairFn G) true) ∧ (¬ Cl G → 2 / 3 ≤ A.prob (pairFn G) false)) :
    c * Real.sqrt (hardPairs n).card ≤ T := by
  classical
  refine family_lower_bound hc A (pairFn G₀) (graphLoc n) ?_ fun i => ?_
  · have : familyInput (pairFn G₀) (graphLoc n) (fun _ => false) = pairFn G₀ := by
      funext q
      simp only [familyInput, bitOf]
      cases graphLoc n q <;> simp
    rw [this]
    exact (hA G₀).1 h0
  · set e := ((hardPairs n).equivFin.symm i) with he
    have hmem : e.1 ∈ hardPairs n := e.2
    have : familyInput (pairFn G₀) (graphLoc n) (singleBit i) = pairFn (G₀.deleteEdges {s(e.1.1, e.1.2)}) := by
      funext q
      obtain ⟨u, v⟩ := q
      simp only [familyInput, pairFn, SimpleGraph.deleteEdges_adj, Set.mem_singleton_iff, Sym2.eq_iff]
      have hbit := @bitOf_single_graph n i (u, v)
      rw [graphLoc_eq_some, ← he] at hbit
      have hswap : e.1.swap = (e.1.2, e.1.1) := rfl
      by_cases hcase : (u = e.1.1 ∧ v = e.1.2) ∨ (u = e.1.2 ∧ v = e.1.1)
      · have hb : bitOf (graphLoc n) (singleBit i) (u, v) = true := by
          refine hbit.2 ?_
          rw [hswap]
          rcases hcase with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact Or.inl rfl
          · exact Or.inr rfl
        have hG : G₀.Adj u v := by
          rcases hcase with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact hadj _ hmem
          · exact (hadj _ hmem).symm
        rw [hb]
        simp [hG, hcase]
      · have hb : bitOf (graphLoc n) (singleBit i) (u, v) = false := by
          by_contra hne
          have hb' : bitOf (graphLoc n) (singleBit i) (u, v) = true := by simpa using hne
          rcases hbit.1 hb' with h | h
          · exact hcase (Or.inl ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩)
          · exact hcase (Or.inr ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩)
        rw [hb]
        simp [hcase]
    rw [this]
    exact (hA _).2 (h1 e.1 hmem)

/-- A quantum decider for a class of graphs: bounded error on the adjacency matrix, with queries on ordered pairs. -/
def DecidesGraphs {n T : ℕ} {S : Type} [Fintype S] [DecidableEq S] (A : QAlg (Fin n × Fin n) T S Bool)
    (Cl : SimpleGraph (Fin n) → Prop) : Prop :=
  ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
    (Cl G → 2 / 3 ≤ A.prob (pairFn G) true) ∧ (¬ Cl G → 2 / 3 ≤ A.prob (pairFn G) false)

end ClusterRec
