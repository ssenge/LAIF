import Mathlib

/-!
# Quantum query algorithms in the adjacency array model

A weighted graph is given by an array: one can query the degree of a vertex, and the name and weight of its `i`-th
neighbour. A query is a fixed unit phase for each pair of basis state and answer, which contains the standard oracle
after a change of basis on the answer register. The acceptance probability on a family of arrays in which every
query depends on at most one bit of `x` is a sum of functions that each depend on at most `2T` bits of `x`.
-/

open Finset

namespace MinCutArray

/-- A weighted graph without loops. Weight `0` means that there is no edge. -/
structure WGraph (V : Type) where
  w : V → V → ℕ
  symm : ∀ u v, w u v = w v u
  loopless : ∀ v, w v v = 0

section Cut

variable {V : Type} [Fintype V] [DecidableEq V]

/-- The weight of the cut with shore `X`. -/
def WGraph.cut (G : WGraph V) (X : Finset V) : ℕ := ∑ u ∈ X, ∑ v ∈ Xᶜ, G.w u v

/-- `m` is the weight of a minimum cut. -/
def WGraph.IsMinCut (G : WGraph V) (m : ℕ) : Prop :=
  (∃ X : Finset V, X.Nonempty ∧ Xᶜ.Nonempty ∧ G.cut X = m) ∧
    ∀ X : Finset V, X.Nonempty → Xᶜ.Nonempty → m ≤ G.cut X

end Cut

variable {V : Type}

/-- All edge weights lie between `1` and `τ`. -/
def WGraph.RatioAtMost (G : WGraph V) (τ : ℕ) : Prop :=
  ∀ u v, G.w u v = 0 ∨ (1 ≤ G.w u v ∧ G.w u v ≤ τ)

/-- An adjacency array: the degree of each vertex, and the name and weight of its `i`-th neighbour. -/
structure AdjArray (V : Type) where
  deg : V → ℕ
  nbr : V → ℕ → Option (V × ℕ)

/-- The array lists the neighbours of each vertex without repetition, in some order, with their weights. -/
def WGraph.Represents (G : WGraph V) (a : AdjArray V) : Prop :=
  ∀ v,
    (∀ i, i < a.deg v → ∃ u, a.nbr v i = some (u, G.w v u) ∧ 0 < G.w v u) ∧
    (∀ i, a.deg v ≤ i → a.nbr v i = none) ∧
    (∀ i j u c d, a.nbr v i = some (u, c) → a.nbr v j = some (u, d) → i = j) ∧
    (∀ u, 0 < G.w v u → ∃ i c, a.nbr v i = some (u, c))

/-- A query position: a degree, or an entry of a neighbour list. -/
abbrev QPos (V : Type) := V ⊕ (V × ℕ)

/-- A query answer. -/
abbrev Ans (V : Type) := ℕ ⊕ Option (V × ℕ)

/-- The answer at a position. -/
def AdjArray.entry (a : AdjArray V) : QPos V → Ans V
  | .inl v => .inl (a.deg v)
  | .inr p => .inr (a.nbr p.1 p.2)

/-- A `T`-query quantum algorithm on the basis `S`. Any workspace is allowed. The unitaries do not depend on the
input. The outcome of a measurement in the basis `S` is read as a natural number. -/
structure QAlg (V : Type) (T : ℕ) (S : Type) [Fintype S] [DecidableEq S] where
  pos : S → QPos V
  phase : S → Ans V → ℂ
  normSq_phase : ∀ s r, Complex.normSq (phase s r) = 1
  U : Fin (T + 1) → Matrix.unitaryGroup S ℂ
  init : S
  out : S → ℕ

variable {T : ℕ} {S : Type} [Fintype S] [DecidableEq S]

/-- The phase of one query. -/
noncomputable def QAlg.oracle (q : QAlg V T S) (a : AdjArray V) (s : S) : ℂ := q.phase s (a.entry (q.pos s))

/-- The state after `U_t O U_{t-1} ⋯ O U_0` applied to the initial basis state. -/
noncomputable def QAlg.state (q : QAlg V T S) (a : AdjArray V) : (t : ℕ) → t ≤ T → S → ℂ
  | 0, _ => (q.U ⟨0, Nat.succ_pos T⟩ : Matrix S S ℂ).mulVec (Pi.single q.init 1)
  | t + 1, h => (q.U ⟨t + 1, Nat.succ_lt_succ h⟩ : Matrix S S ℂ).mulVec
      fun s => q.oracle a s * q.state a t (Nat.le_of_succ_le h) s

/-- The probability that the outcome satisfies `P`. -/
noncomputable def QAlg.prob (q : QAlg V T S) (a : AdjArray V) (P : ℕ → Prop) [DecidablePred P] : ℝ :=
  ∑ s, if P (q.out s) then Complex.normSq (q.state a T le_rfl s) else 0

/-- The algorithm computes the weight of a minimum cut with probability at least `2/3` on all graphs with weights
between `1` and `τ`. -/
def QAlg.Computes [Fintype V] [DecidableEq V] (q : QAlg V T S) (τ : ℕ) : Prop :=
  ∀ (G : WGraph V) (a : AdjArray V) (m : ℕ), G.RatioAtMost τ → G.Represents a → G.IsMinCut m →
    2 / 3 ≤ q.prob a (· = m)

/-! ## Norm conservation -/

theorem sum_normSq_mulVec (U : Matrix.unitaryGroup S ℂ) (v : S → ℂ) :
    ∑ s, Complex.normSq ((U : Matrix S S ℂ).mulVec v s) = ∑ s, Complex.normSq (v s) := by
  have hstar : star (U : Matrix S S ℂ) * (U : Matrix S S ℂ) = 1 := Matrix.mem_unitaryGroup_iff'.mp U.2
  have h : star ((U : Matrix S S ℂ).mulVec v) ⬝ᵥ (U : Matrix S S ℂ).mulVec v = star v ⬝ᵥ v := by
    rw [Matrix.star_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, ← Matrix.star_eq_conjTranspose,
      hstar, Matrix.vecMul_one]
  have hconv : ∀ w : S → ℂ, star w ⬝ᵥ w = ((∑ s, Complex.normSq (w s) : ℝ) : ℂ) := by
    intro w
    simp only [dotProduct, Pi.star_apply, Complex.star_def, Complex.ofReal_sum]
    exact sum_congr rfl fun s _ => (Complex.normSq_eq_conj_mul_self).symm
  rw [hconv, hconv] at h
  exact_mod_cast h

theorem QAlg.sum_normSq_state (q : QAlg V T S) (a : AdjArray V) :
    ∀ (t : ℕ) (ht : t ≤ T), ∑ s, Complex.normSq (q.state a t ht s) = 1 := by
  intro t
  induction t with
  | zero =>
    intro ht
    simp only [QAlg.state]
    rw [sum_normSq_mulVec, sum_eq_single q.init]
    · simp
    · intro b _ hb
      simp [hb]
    · simp
  | succ t ih =>
    intro ht
    simp only [QAlg.state]
    rw [sum_normSq_mulVec, ← ih (Nat.le_of_succ_le ht)]
    refine sum_congr rfl fun s _ => ?_
    rw [map_mul, QAlg.oracle, q.normSq_phase, one_mul]

theorem QAlg.prob_nonneg (q : QAlg V T S) (a : AdjArray V) (P : ℕ → Prop) [DecidablePred P] : 0 ≤ q.prob a P := by
  unfold QAlg.prob
  refine sum_nonneg fun s _ => ?_
  split_ifs
  · exact Complex.normSq_nonneg _
  · exact le_rfl

theorem QAlg.prob_mono (q : QAlg V T S) (a : AdjArray V) (P Q : ℕ → Prop) [DecidablePred P] [DecidablePred Q]
    (h : ∀ m, P m → Q m) : q.prob a P ≤ q.prob a Q := by
  unfold QAlg.prob
  refine sum_le_sum fun s _ => ?_
  by_cases hP : P (q.out s)
  · simp [hP, h _ hP]
  · simp only [hP, ite_false]
    split_ifs
    · exact Complex.normSq_nonneg _
    · exact le_rfl

theorem QAlg.prob_add_le (q : QAlg V T S) (a : AdjArray V) (P Q : ℕ → Prop) [DecidablePred P] [DecidablePred Q]
    (h : ∀ m, P m → ¬ Q m) : q.prob a P + q.prob a Q ≤ 1 := by
  rw [← q.sum_normSq_state a T le_rfl]
  unfold QAlg.prob
  rw [← sum_add_distrib]
  refine sum_le_sum fun s _ => ?_
  by_cases hP : P (q.out s)
  · simp [hP, h _ hP]
  · simp only [hP, ite_false, zero_add]
    split_ifs
    · exact le_rfl
    · exact Complex.normSq_nonneg _

theorem QAlg.prob_le_one (q : QAlg V T S) (a : AdjArray V) (P : ℕ → Prop) [DecidablePred P] : q.prob a P ≤ 1 := by
  have h := q.prob_add_le a P (fun _ => False) (fun _ _ => not_false)
  have h0 := q.prob_nonneg a (fun _ => False)
  linarith

/-! ## The acceptance probability as a sum of juntas -/

/-- `R` is a sum of functions that each depend on at most `D` bits of `x`, which says exactly that `R` is a real
multilinear polynomial of degree at most `D` in the bits of `x`. -/
def IsJuntaSum {ι : Type} (D : ℕ) (R : (ι → Bool) → ℝ) : Prop :=
  ∃ (κ : Type) (_ : Fintype κ) (I : κ → Finset ι) (g : κ → (ι → Bool) → ℝ),
    (∀ k, (I k).card ≤ D ∧ ∀ x y : ι → Bool, (∀ i ∈ I k, x i = y i) → g k x = g k y) ∧
      ∀ x, R x = ∑ k, g k x

/-- The phase accumulated along a path. -/
noncomputable def QAlg.pathPhase (q : QAlg V T S) (a : AdjArray V) {t : ℕ} (p : Fin t → S) : ℂ :=
  ∏ i, q.oracle a (p i)

/-- The state is a sum over paths of an amplitude independent of the input times the phase of the path. -/
theorem QAlg.exists_path_expansion (q : QAlg V T S) :
    ∀ (t : ℕ) (ht : t ≤ T), ∃ amp : (Fin t → S) → S → ℂ, ∀ (a : AdjArray V) (s : S),
      q.state a t ht s = ∑ p, amp p s * q.pathPhase a p := by
  intro t
  induction t with
  | zero =>
    intro ht
    refine ⟨fun _ s => (q.U ⟨0, Nat.succ_pos T⟩ : Matrix S S ℂ).mulVec (Pi.single q.init 1) s, ?_⟩
    intro a s
    simp [QAlg.state, QAlg.pathPhase]
  | succ t ih =>
    intro ht
    obtain ⟨amp, hamp⟩ := ih (Nat.le_of_succ_le ht)
    refine ⟨fun p s => (q.U ⟨t + 1, Nat.succ_lt_succ ht⟩ : Matrix S S ℂ) s (p (Fin.last t))
      * amp (Fin.init p) (p (Fin.last t)), ?_⟩
    intro a s
    have hL : q.state a (t + 1) ht s = ∑ s', (q.U ⟨t + 1, Nat.succ_lt_succ ht⟩ : Matrix S S ℂ) s s'
        * (q.oracle a s' * q.state a t (Nat.le_of_succ_le ht) s') := rfl
    rw [hL, ← (Fin.snocEquiv fun _ : Fin (t + 1) => S).sum_comp, Fintype.sum_prod_type]
    refine sum_congr rfl fun s' _ => ?_
    rw [hamp a s', mul_sum, mul_sum]
    refine sum_congr rfl fun p₀ _ => ?_
    have hphase : q.pathPhase a ((Fin.snocEquiv fun _ : Fin (t + 1) => S) (s', p₀))
        = q.pathPhase a p₀ * q.oracle a s' := by
      simp [QAlg.pathPhase, Fin.prod_univ_castSucc, Fin.snocEquiv]
    have hinit : Fin.init ((Fin.snocEquiv fun _ : Fin (t + 1) => S) (s', p₀)) = p₀ := by
      simp [Fin.snocEquiv]
    have hlast : ((Fin.snocEquiv fun _ : Fin (t + 1) => S) (s', p₀)) (Fin.last t) = s' := by
      simp [Fin.snocEquiv]
    simp only [hphase, hinit, hlast]
    ring

/-- If every query depends on at most one bit of `x`, the probability of any event is a sum of functions that each
depend on at most `2T` bits of `x`. -/
theorem QAlg.isJuntaSum_prob (q : QAlg V T S) {ι : Type} [DecidableEq ι] (a : (ι → Bool) → AdjArray V)
    (loc : QPos V → Option ι)
    (hloc : ∀ (p : QPos V) (x y : ι → Bool), (∀ i, loc p = some i → x i = y i) → (a x).entry p = (a y).entry p)
    (P : ℕ → Prop) [DecidablePred P] :
    IsJuntaSum (2 * T) fun x => q.prob (a x) P := by
  classical
  obtain ⟨amp, hamp⟩ := q.exists_path_expansion T le_rfl
  let J : (Fin T → S) → Finset ι := fun p => univ.biUnion fun i => (loc (q.pos (p i))).toFinset
  have hJ : ∀ p, (J p).card ≤ T := by
    intro p
    calc (J p).card ≤ ∑ i : Fin T, (loc (q.pos (p i))).toFinset.card := card_biUnion_le
      _ ≤ ∑ _i : Fin T, 1 := by
        refine sum_le_sum fun i _ => ?_
        cases loc (q.pos (p i)) <;> simp
      _ = T := by simp
  have hpath : ∀ (p : Fin T → S) (x y : ι → Bool), (∀ i ∈ J p, x i = y i) →
      q.pathPhase (a x) p = q.pathPhase (a y) p := by
    intro p x y h
    refine prod_congr rfl fun i _ => ?_
    unfold QAlg.oracle
    rw [hloc (q.pos (p i)) x y]
    intro l hl
    refine h l (mem_biUnion.2 ⟨i, mem_univ _, ?_⟩)
    simp [hl]
  refine ⟨S × (Fin T → S) × (Fin T → S), inferInstance, fun k => J k.2.1 ∪ J k.2.2,
    fun k x => if P (q.out k.1) then
      (amp k.2.1 k.1 * q.pathPhase (a x) k.2.1
        * (starRingEnd ℂ) (amp k.2.2 k.1 * q.pathPhase (a x) k.2.2)).re else 0, ?_, ?_⟩
  · intro k
    refine ⟨?_, ?_⟩
    · calc _ ≤ _ := card_union_le _ _
        _ ≤ T + T := add_le_add (hJ _) (hJ _)
        _ = 2 * T := by ring
    · intro x y h
      dsimp only
      rw [hpath k.2.1 x y fun i hi => h i (mem_union_left _ hi),
        hpath k.2.2 x y fun i hi => h i (mem_union_right _ hi)]
  · intro x
    unfold QAlg.prob
    rw [Fintype.sum_prod_type]
    refine sum_congr rfl fun s _ => ?_
    by_cases hs : P (q.out s)
    · simp only [hs, ite_true]
      rw [Fintype.sum_prod_type]
      have h1 : ((Complex.normSq (q.state (a x) T le_rfl s) : ℝ) : ℂ)
          = q.state (a x) T le_rfl s * (starRingEnd ℂ) (q.state (a x) T le_rfl s) := (Complex.mul_conj _).symm
      have h2 : Complex.normSq (q.state (a x) T le_rfl s)
          = (q.state (a x) T le_rfl s * (starRingEnd ℂ) (q.state (a x) T le_rfl s)).re := by
        rw [← h1, Complex.ofReal_re]
      rw [h2, hamp (a x) s, map_sum, sum_mul_sum, Complex.re_sum]
      refine sum_congr rfl fun p _ => ?_
      rw [Complex.re_sum]
    · simp [hs]

end MinCutArray
