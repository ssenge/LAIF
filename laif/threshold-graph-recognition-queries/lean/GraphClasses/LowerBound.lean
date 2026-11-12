import GraphClasses.HardFamily
import GraphClasses.Model

/-!
# The quantum lower bounds, from the OR lower bound

A query to the input on the hard family is a query to the hidden bit, up to a known sign. So an algorithm for the class
gives an algorithm for OR on `N = Θ(n²)` bits with the same number of queries, on the same basis.
-/

open Finset

namespace GraphClasses

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

/-- **Theorem 3, the lower bound.** Given the OR lower bound, deciding threshold graphs needs `Ω(n)` quantum queries. -/
theorem threshold_lower_bound (hOR : ORLowerBound) :
    ∃ c : ℝ, 0 < c ∧ ∀ (n T : ℕ) (S : Type) [Fintype S] [DecidableEq S] (A : QAlg (Fin n × Fin n) T S Bool),
      4 ≤ n → DecidesGraphs A IsThreshold → c * n ≤ T := by
  classical
  obtain ⟨c, hc0, hc⟩ := hOR
  refine ⟨c / 8, by positivity, fun n T S _ _ A hn hA => ?_⟩
  have h := graph_lower_bound hc A IsThreshold (hardG n) ?_ (hardG_threshold n) ?_ hA
  · have h2 := mul_le_mul_of_nonneg_left (sqrt_hardPairs hn) hc0.le
    linarith [h2, h, show c / 8 * (n : ℝ) = c * ((n : ℝ) / 8) by ring]
  · intro e he
    obtain ⟨_, h1, h2, h3⟩ := mem_filter.1 he |>.imp_right id |> fun x => (⟨x.1, x.2.1, x.2.2.1, x.2.2.2⟩ : _ ∧ _ ∧ _ ∧ _)
    refine ⟨by omega, ?_⟩
    rw [max_eq_right (by omega)]
    exact h2
  · intro e he hT
    have h' := mem_filter.1 he
    have hcyc := hardDel_alt e.1 e.2 h'.2.1 h'.2.2.1 h'.2.2.2
    exact (threshold_iff_noAlt _).1 hT _ _ _ _ hcyc

/-- **Theorem 4, the lower bound.** Given the OR lower bound, deciding chain graphs needs `Ω(n)` quantum queries. -/
theorem chain_lower_bound (hOR : ORLowerBound) :
    ∃ c : ℝ, 0 < c ∧ ∀ (n T : ℕ) (S : Type) [Fintype S] [DecidableEq S] (A : QAlg (Fin n × Fin n) T S Bool),
      4 ≤ n → DecidesGraphs A IsChain → c * n ≤ T := by
  classical
  obtain ⟨c, hc0, hc⟩ := hOR
  refine ⟨c / 8, by positivity, fun n T S _ _ A hn hA => ?_⟩
  have h := graph_lower_bound hc A IsChain (hardChain n) ?_ (hardChain_isChain n) ?_ hA
  · have h2 := mul_le_mul_of_nonneg_left (sqrt_hardPairs hn) hc0.le
    linarith [h2, h, show c / 8 * (n : ℝ) = c * ((n : ℝ) / 8) by ring]
  · intro e he
    have h' := (mem_filter.1 he).2
    obtain ⟨h1, h2, h3⟩ := h'
    refine ⟨by omega, ?_⟩
    rw [max_eq_right (by omega)]
    exact h2
  · intro e he
    have h' := (mem_filter.1 he).2
    exact hardChain_del_not_chain e.1 e.2 h'.1 h'.2.1 h'.2.2

/-! ## Matrices -/

/-- The hidden bit of an entry. -/
noncomputable def matLoc (n : ℕ) (q : Fin n × Fin n) : Option (Fin (hardPairs n).card) :=
  if h : q ∈ hardPairs n then some ((hardPairs n).equivFin ⟨q, h⟩) else none

/-- A quantum decider for nestedness of the block of even rows and odd columns. -/
def DecidesNestedBlock {n T : ℕ} {S : Type} [Fintype S] [DecidableEq S] (A : QAlg (Fin n × Fin n) T S Bool) : Prop :=
  ∀ M : Fin n → Fin n → Bool,
    (NestedOn M (evens n) (odds n) → 2 / 3 ≤ A.prob (fun e => M e.1 e.2) true) ∧
    (¬ NestedOn M (evens n) (odds n) → 2 / 3 ≤ A.prob (fun e => M e.1 e.2) false)

/-- **Theorem 2, the lower bound.** Given the OR lower bound, deciding nestedness of the `Θ(n) × Θ(n)` block of even
rows and odd columns needs `Ω(n)` quantum queries. -/
theorem nested_lower_bound (hOR : ORLowerBound) :
    ∃ c : ℝ, 0 < c ∧ ∀ (n T : ℕ) (S : Type) [Fintype S] [DecidableEq S] (A : QAlg (Fin n × Fin n) T S Bool),
      4 ≤ n → DecidesNestedBlock A → c * n ≤ T := by
  classical
  obtain ⟨c, hc0, hc⟩ := hOR
  refine ⟨c / 8, by positivity, fun n T S _ _ A hn hA => ?_⟩
  have h : c * Real.sqrt (hardPairs n).card ≤ T := by
    refine family_lower_bound hc A (fun e => hardMat n e.1 e.2) (matLoc n) ?_ fun i => ?_
    · have : familyInput (fun e : Fin n × Fin n => hardMat n e.1 e.2) (matLoc n) (fun _ => false) =
          fun e => hardMat n e.1 e.2 := by
        funext q
        simp only [familyInput, bitOf]
        cases matLoc n q <;> simp
      rw [this]
      exact (hA _).1 (hardMat_nested n)
    · set e := ((hardPairs n).equivFin.symm i) with he
      have hmem : e.1 ∈ hardPairs n := e.2
      have hmem' := (mem_filter.1 hmem).2
      have : familyInput (fun e : Fin n × Fin n => hardMat n e.1 e.2) (matLoc n) (singleBit i) =
          fun q => hardMatDel n e.1.1 e.1.2 q.1 q.2 := by
        funext q
        simp only [familyInput, hardMatDel]
        by_cases hq : q = e.1
        · have hl : matLoc n q = some i := by
            unfold matLoc
            rw [dif_pos (hq ▸ hmem)]
            refine congrArg some ?_
            have : (⟨q, hq ▸ hmem⟩ : hardPairs n) = e := Subtype.ext hq
            rw [this, he]
            simp
          have hb : bitOf (matLoc n) (singleBit i) q = true := by
            simp [bitOf, hl, singleBit]
          rw [hb, hq]
          have hlt : hardMat n e.1.1 e.1.2 = true := by
            simp only [hardMat, decide_eq_true_eq]
            omega
          simp [hlt]
        · have hne : ¬ (q.1 = e.1.1 ∧ q.2 = e.1.2) := fun h => hq (Prod.ext h.1 h.2)
          have hb : bitOf (matLoc n) (singleBit i) q = false := by
            unfold bitOf
            cases hl : matLoc n q with
            | none => rfl
            | some j =>
              simp only [singleBit, decide_eq_false_iff_not]
              rintro rfl
              unfold matLoc at hl
              split_ifs at hl with h1
              apply hq
              have h3 := Option.some.inj hl
              have h4 : (⟨q, h1⟩ : hardPairs n) = e := by
                rw [he, ← h3]
                simp
              exact congrArg Subtype.val h4
          rw [hb]
          simp only [Bool.xor_false, Bool.and_not_self, Bool.and_eq_true, decide_eq_true_eq]
          have hdec : (decide (q.1 = e.1.1) && decide (q.2 = e.1.2)) = false := by
            simpa using fun h1 h2 => hne ⟨h1, h2⟩
          rw [hdec]
          simp
      rw [this]
      exact (hA _).2 (hardMatDel_not_nested e.1.1 e.1.2 hmem'.1 hmem'.2.1 hmem'.2.2)
  have h2 := mul_le_mul_of_nonneg_left (sqrt_hardPairs hn) hc0.le
  linarith [h2, h, show c / 8 * (n : ℝ) = c * ((n : ℝ) / 8) by ring]

end GraphClasses
