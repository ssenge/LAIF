import Mathlib

/-!
# Quantum query algorithms for matrix product verification over `F₂`, and the classical degree bound

The input is three `n × n` matrices over `ZMod 2`. A query is the phase oracle `|p, z⟩ ↦ (-1)^{z X_p} |p, z⟩`,
which is the standard oracle up to Hadamards on the bit `z`. The only hypothesis of the main theorem is the
polynomial degree bound for element distinctness, `EDDegree`.
-/

open Finset

namespace MatVerify

/-- The sign character of `ZMod 2`. -/
noncomputable def sg (x : ZMod 2) : ℝ := if x = 0 then 1 else -1

theorem zmod2_cases (x : ZMod 2) : x = 0 ∨ x = 1 := by
  revert x; decide

theorem sg_zero : sg 0 = 1 := by simp [sg]

theorem sg_one : sg 1 = -1 := by simp [sg]

theorem sg_add (x y : ZMod 2) : sg (x + y) = sg x * sg y := by
  have h11 : (1 : ZMod 2) + 1 = 0 := by decide
  rcases zmod2_cases x with rfl | rfl <;> rcases zmod2_cases y with rfl | rfl <;>
    simp [sg_zero, sg_one, h11]

theorem sg_sum {ι : Type*} (s : Finset ι) (g : ι → ZMod 2) : sg (∑ i ∈ s, g i) = ∏ i ∈ s, sg (g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [sg_zero]
  | insert a s ha ih => rw [sum_insert ha, prod_insert ha, sg_add, ih]

theorem sg_mul_self (x : ZMod 2) : sg x * sg x = 1 := by
  rcases zmod2_cases x with rfl | rfl <;> simp [sg_zero, sg_one]

theorem abs_sg (x : ZMod 2) : |sg x| = 1 := by
  rcases zmod2_cases x with rfl | rfl <;> simp [sg_zero, sg_one]

variable {n : ℕ}

/-- A query position: which matrix, and which entry. -/
abbrev Pos (n : ℕ) := Fin 3 × Fin n × Fin n

/-- An input. -/
structure Input (n : ℕ) where
  A : Matrix (Fin n) (Fin n) (ZMod 2)
  B : Matrix (Fin n) (Fin n) (ZMod 2)
  C : Matrix (Fin n) (Fin n) (ZMod 2)

/-- The entry at a position. -/
def Input.entry (X : Input n) (p : Pos n) : ZMod 2 :=
  if p.1 = 0 then X.A p.2.1 p.2.2 else if p.1 = 1 then X.B p.2.1 p.2.2 else X.C p.2.1 p.2.2

/-- A `T`-query quantum algorithm on the basis `S`. Any workspace is allowed. The unitaries do not depend on the
input. -/
structure QAlg (n T : ℕ) (S : Type*) [Fintype S] [DecidableEq S] where
  pos : S → Pos n
  z : S → ZMod 2
  U : Fin (T + 1) → Matrix.unitaryGroup S ℂ
  init : S
  out : S → Bool

variable {T : ℕ} {S : Type} [Fintype S] [DecidableEq S]

/-- The sign of one query. -/
noncomputable def QAlg.phase (q : QAlg n T S) (X : Input n) (s : S) : ℝ := sg (q.z s * X.entry (q.pos s))

/-- The state after `U_t O U_{t-1} ⋯ O U_0` applied to the initial basis state. -/
noncomputable def QAlg.state (q : QAlg n T S) (X : Input n) : (t : ℕ) → t ≤ T → S → ℂ
  | 0, _ => (q.U ⟨0, Nat.succ_pos T⟩ : Matrix S S ℂ).mulVec (Pi.single q.init 1)
  | t + 1, h => (q.U ⟨t + 1, Nat.succ_lt_succ h⟩ : Matrix S S ℂ).mulVec
      fun s => (q.phase X s : ℂ) * q.state X t (Nat.le_of_succ_le h) s

/-- The acceptance probability. -/
noncomputable def QAlg.accept (q : QAlg n T S) (X : Input n) : ℝ :=
  ∑ s, if q.out s then Complex.normSq (q.state X T le_rfl s) else 0

/-- The algorithm decides `AB = C` with error at most `1/3`. -/
def QAlg.Decides (q : QAlg n T S) : Prop :=
  ∀ X : Input n, (X.A * X.B = X.C → 2 / 3 ≤ q.accept X) ∧ (X.A * X.B ≠ X.C → q.accept X ≤ 1 / 3)

/-! ## The classical theorem taken as a hypothesis -/

/-- `R` is a sum of functions of `f` that each depend on at most `D` coordinates of `f`. On functions
`f : [N] → [N]` this says exactly that `R` is a polynomial of degree at most `D` in the indicators
`y_ih = [f(i) = h]`: a monomial depends on the coordinates it names, and a function of the coordinates in `I` is a
sum of monomials `∏_{i ∈ I} y_{i, h_i}`. -/
def IsJuntaSum (N D : ℕ) (R : (Fin N → Fin N) → ℝ) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (I : ι → Finset (Fin N)) (g : ι → (Fin N → Fin N) → ℝ),
    (∀ k, (I k).card ≤ D ∧ ∀ f f' : Fin N → Fin N, (∀ i ∈ I k, f i = f' i) → g k f = g k f') ∧
      ∀ f, R f = ∑ k, g k f

/-- The polynomial degree of element distinctness on functions `[N] → [N]` is `Ω(N^{2/3})`. -/
def EDDegree : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ (N D : ℕ) (R : (Fin N → Fin N) → ℝ), 2 ≤ N → IsJuntaSum N D R →
    (∀ f, 0 ≤ R f ∧ R f ≤ 1) →
    (∀ f, Function.Injective f → 2 / 3 ≤ R f) →
    (∀ f, ¬ Function.Injective f → R f ≤ 1 / 3) →
    c * (N : ℝ) ^ ((2 : ℝ) / 3) ≤ D

/-! ## Expansion of the acceptance probability in characters -/

/-- The linear form with coefficient vector `w`. -/
def dotP (w : Pos n → ZMod 2) (X : Input n) : ZMod 2 := ∑ p, w p * X.entry p

/-- The sign accumulated along a path. -/
noncomputable def QAlg.pathSg (q : QAlg n T S) (X : Input n) {t : ℕ} (p : Fin t → S) : ℝ :=
  ∏ i, q.phase X (p i)

/-- The state is a sum over paths of an amplitude independent of the input times the sign of the path. -/
theorem QAlg.exists_path_expansion (q : QAlg n T S) :
    ∀ (t : ℕ) (ht : t ≤ T), ∃ amp : (Fin t → S) → S → ℂ, ∀ (X : Input n) (s : S),
      q.state X t ht s = ∑ p, amp p s * (q.pathSg X p : ℂ) := by
  intro t
  induction t with
  | zero =>
    intro ht
    refine ⟨fun _ s => (q.U ⟨0, Nat.succ_pos T⟩ : Matrix S S ℂ).mulVec (Pi.single q.init 1) s, ?_⟩
    intro X s
    simp [QAlg.state, QAlg.pathSg]
  | succ t ih =>
    intro ht
    obtain ⟨amp, hamp⟩ := ih (Nat.le_of_succ_le ht)
    refine ⟨fun p s => (q.U ⟨t + 1, Nat.succ_lt_succ ht⟩ : Matrix S S ℂ) s (p (Fin.last t))
      * amp (Fin.init p) (p (Fin.last t)), ?_⟩
    intro X s
    have hL : q.state X (t + 1) ht s = ∑ s', (q.U ⟨t + 1, Nat.succ_lt_succ ht⟩ : Matrix S S ℂ) s s'
        * ((q.phase X s' : ℂ) * q.state X t (Nat.le_of_succ_le ht) s') := rfl
    rw [hL, ← (Fin.snocEquiv fun _ : Fin (t + 1) => S).sum_comp, Fintype.sum_prod_type]
    refine sum_congr rfl fun s' _ => ?_
    rw [hamp X s', mul_sum, mul_sum]
    refine sum_congr rfl fun p₀ _ => ?_
    have hphase : q.pathSg X ((Fin.snocEquiv fun _ : Fin (t + 1) => S) (s', p₀))
        = q.pathSg X p₀ * q.phase X s' := by
      simp [QAlg.pathSg, Fin.prod_univ_castSucc, Fin.snocEquiv]
    have hinit : Fin.init ((Fin.snocEquiv fun _ : Fin (t + 1) => S) (s', p₀)) = p₀ := by
      simp [Fin.snocEquiv]
    have hlast : ((Fin.snocEquiv fun _ : Fin (t + 1) => S) (s', p₀)) (Fin.last t) = s' := by
      simp [Fin.snocEquiv]
    simp only [hphase, hinit, hlast]
    push_cast
    ring

/-- The coefficient vector of a path. -/
def QAlg.pathW (q : QAlg n T S) {t : ℕ} (p : Fin t → S) (r : Pos n) : ZMod 2 :=
  ∑ i, if q.pos (p i) = r then q.z (p i) else 0

theorem QAlg.pathSg_eq (q : QAlg n T S) (X : Input n) {t : ℕ} (p : Fin t → S) :
    q.pathSg X p = sg (dotP (q.pathW p) X) := by
  have h : dotP (q.pathW p) X = ∑ i, q.z (p i) * X.entry (q.pos (p i)) := by
    unfold dotP QAlg.pathW
    simp only [sum_mul]
    rw [sum_comm]
    refine sum_congr rfl fun i _ => ?_
    rw [sum_eq_single (q.pos (p i))]
    · simp
    · intro r _ hr
      simp [Ne.symm hr]
    · simp
  rw [h, sg_sum]
  rfl

theorem QAlg.card_support_pathW (q : QAlg n T S) {t : ℕ} (p : Fin t → S) :
    (univ.filter fun r => q.pathW p r ≠ 0).card ≤ t := by
  have hsub : (univ.filter fun r => q.pathW p r ≠ 0) ⊆ univ.image fun i => q.pos (p i) := by
    intro r hr
    simp only [mem_filter, mem_univ, true_and] at hr
    by_contra hni
    apply hr
    unfold QAlg.pathW
    refine sum_eq_zero fun i _ => ?_
    simp only [ite_eq_right_iff]
    exact fun hi => absurd (mem_image.2 ⟨i, mem_univ _, hi⟩) hni
  calc _ ≤ _ := card_le_card hsub
    _ ≤ (univ : Finset (Fin t)).card := card_image_le
    _ = t := by simp

theorem dotP_add (w w' : Pos n → ZMod 2) (X : Input n) : dotP (w + w') X = dotP w X + dotP w' X := by
  simp [dotP, add_mul, sum_add_distrib]

/-- The acceptance probability is a real combination of characters of weight at most `2T`. -/
theorem QAlg.exists_accept_expansion (q : QAlg n T S) :
    ∃ (ι : Type) (_ : Fintype ι) (c : ι → ℝ) (w : ι → Pos n → ZMod 2),
      (∀ k, (univ.filter fun r => w k r ≠ 0).card ≤ 2 * T) ∧
        ∀ X : Input n, q.accept X = ∑ k, c k * sg (dotP (w k) X) := by
  classical
  obtain ⟨amp, hamp⟩ := q.exists_path_expansion T le_rfl
  refine ⟨(Fin T → S) × (Fin T → S), inferInstance,
    fun k => ∑ s, if q.out s then (amp k.1 s * (starRingEnd ℂ) (amp k.2 s)).re else 0,
    fun k => q.pathW k.1 + q.pathW k.2, ?_, ?_⟩
  · intro k
    have hsub : (univ.filter fun r => (q.pathW k.1 + q.pathW k.2) r ≠ 0)
        ⊆ (univ.filter fun r => q.pathW k.1 r ≠ 0) ∪ (univ.filter fun r => q.pathW k.2 r ≠ 0) := by
      intro r hr
      simp only [mem_filter, mem_univ, true_and, mem_union, Pi.add_apply] at hr ⊢
      by_contra hcon
      push Not at hcon
      exact hr (by rw [hcon.1, hcon.2, add_zero])
    calc _ ≤ _ := card_le_card hsub
      _ ≤ _ := card_union_le _ _
      _ ≤ T + T := add_le_add (q.card_support_pathW _) (q.card_support_pathW _)
      _ = 2 * T := by ring
  · intro X
    have hns : ∀ s, Complex.normSq (q.state X T le_rfl s)
        = ∑ k : (Fin T → S) × (Fin T → S), (amp k.1 s * (starRingEnd ℂ) (amp k.2 s)).re
            * sg (dotP (q.pathW k.1 + q.pathW k.2) X) := by
      intro s
      have h1 : ((Complex.normSq (q.state X T le_rfl s) : ℝ) : ℂ)
          = q.state X T le_rfl s * (starRingEnd ℂ) (q.state X T le_rfl s) := (Complex.mul_conj _).symm
      have h2 : Complex.normSq (q.state X T le_rfl s)
          = (q.state X T le_rfl s * (starRingEnd ℂ) (q.state X T le_rfl s)).re := by
        rw [← h1, Complex.ofReal_re]
      rw [h2, hamp X s, map_sum, sum_mul_sum, Fintype.sum_prod_type, Complex.re_sum]
      refine sum_congr rfl fun p _ => ?_
      rw [Complex.re_sum]
      refine sum_congr rfl fun p' _ => ?_
      rw [dotP_add, sg_add, ← q.pathSg_eq, ← q.pathSg_eq, map_mul, Complex.conj_ofReal]
      have : amp p s * (q.pathSg X p : ℂ) * ((starRingEnd ℂ) (amp p' s) * (q.pathSg X p' : ℂ))
          = (amp p s * (starRingEnd ℂ) (amp p' s)) * ((q.pathSg X p * q.pathSg X p' : ℝ) : ℂ) := by
        push_cast; ring
      rw [this, Complex.re_mul_ofReal]
    unfold QAlg.accept
    simp only [sum_mul]
    rw [sum_comm]
    refine sum_congr rfl fun s _ => ?_
    by_cases hs : q.out s
    · simp only [hs, ↓reduceIte]
      rw [hns s]
    · simp [hs]

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

theorem QAlg.sum_normSq_state (q : QAlg n T S) (X : Input n) :
    ∀ (t : ℕ) (ht : t ≤ T), ∑ s, Complex.normSq (q.state X t ht s) = 1 := by
  intro t
  induction t with
  | zero =>
    intro ht
    simp only [QAlg.state]
    rw [sum_normSq_mulVec]
    rw [sum_eq_single q.init]
    · simp
    · intro b _ hb
      simp [hb]
    · simp
  | succ t ih =>
    intro ht
    simp only [QAlg.state]
    rw [sum_normSq_mulVec, ← ih (Nat.le_of_succ_le ht)]
    refine sum_congr rfl fun s _ => ?_
    rw [map_mul, Complex.normSq_ofReal]
    have hsq : q.phase X s * q.phase X s = 1 := sg_mul_self _
    rw [hsq, one_mul]

theorem QAlg.accept_nonneg (q : QAlg n T S) (X : Input n) : 0 ≤ q.accept X := by
  unfold QAlg.accept
  refine sum_nonneg fun s _ => ?_
  split_ifs
  · exact Complex.normSq_nonneg _
  · exact le_rfl

theorem QAlg.accept_le_one (q : QAlg n T S) (X : Input n) : q.accept X ≤ 1 := by
  rw [← q.sum_normSq_state X T le_rfl]
  unfold QAlg.accept
  refine sum_le_sum fun s _ => ?_
  split_ifs
  · exact le_rfl
  · exact Complex.normSq_nonneg _

end MatVerify
