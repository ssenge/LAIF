import LPType.Theorem1
import LPType.Model
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.SpecificFunctions.Pow

/-!
# The query count

Plain arithmetic: `T (δ √n + √(n log n))` with `T = ⌈12 δ ln n⌉` is at most
`14 (δ² √n log n + δ √n log^{3/2} n)`. The cost of search enters only through `GroverFindAll` and
`GroverFindOne` of `LPType.Model`. The size of the samples enters through hypotheses
(`hR`, `hS` in `expected_queries_le`): the bound on `E[|S_t|]` needs the lower tail of `W̃`, which is
not proved here. The unconditional part, `E[|S|] ≤ s W / Z` for a fixed `Z > 0`, is `sum_inclProb_le`.
-/

open Finset

namespace LPType

/-! ## Concavity -/

/-- **Concavity of the square root**: `E[√a] ≤ √E[a]`, on a finite probability space. -/
theorem sum_mul_sqrt_le {Ω : Type*} [Fintype Ω] {ρ a : Ω → ℝ} (hρ : ∀ u, 0 ≤ ρ u)
    (hsum : ∑ u, ρ u = 1) (ha : ∀ u, 0 ≤ a u) :
    ∑ u, ρ u * √(a u) ≤ √(∑ u, ρ u * a u) := by
  have := Real.strictConcaveOn_sqrt.concaveOn.le_map_sum (t := univ) (w := ρ) (p := a)
    (fun u _ => hρ u) hsum (fun u _ => ha u)
  simpa [smul_eq_mul] using this

/-- `E[√(n |S|)] ≤ √(n E[|S|])` for a product measure. -/
theorem prodExp_sqrt_card_le {H : Type*} [DecidableEq H] [Fintype H] {p : H → ℝ} (hp : IsProb p)
    (n : ℝ) (hn : 0 ≤ n) :
    prodExp p (fun S => √(n * #S)) ≤ √(n * ∑ h, p h) := by
  have h := sum_mul_sqrt_le (ρ := prodWeight p) (a := fun S => n * #S)
    (prodWeight_nonneg hp) (prodWeight_sum p) (fun S => by positivity)
  have h2 : ∑ S, prodWeight p S * (n * (#S : ℝ)) = n * ∑ h, p h := by
    rw [← prodExp_card p, prodExp, mul_sum]
    exact sum_congr rfl fun S _ => by ring
  rwa [h2] at h

/-- The expected sample size is at most `s W / Z` for a fixed `Z > 0`. -/
theorem sum_inclProb_le {H : Type*} [Fintype H] {s Z : ℝ} {w : H → ℝ} (hZ : 0 < Z) :
    ∑ h, inclProb s w Z h ≤ s * (∑ h, w h) / Z := by
  rw [mul_sum, sum_div]
  exact sum_le_sum fun h _ => inclProb_le_div hZ h

/-! ## the cost of quantum search, in expectation over the marks -/

/-- From `GroverFindAll`: when the marks depend on a random seed `u`, drawn independently of the
input, the expected cost of finding all marked elements is at most
`κ (√(n E[k]) + √(n log n))`, by concavity. This is the round cost of the README. -/
theorem findAll_expected_cost_le {κ : ℝ} (hκ : 0 ≤ κ) (hG : GroverFindAll κ) {n k : ℕ} (hn : 2 ≤ n)
    {Ω : Type*} [Fintype Ω] {ρ : Ω → ℝ} (hρ : ∀ u, 0 ≤ ρ u) (hsum : ∑ u, ρ u = 1)
    (m : Ω → Fin n → Fin k → Bool) (x : Fin n → Fin k) :
    ∃ A : Ω → AdaptiveAlg (Fin n) k (Finset (Fin n)),
      (∀ u, (A u).failProb x (· = markedSet (m u) x) ≤ 1 / (n : ℝ) ^ 3) ∧
      ∑ u, ρ u * (A u).expCost x
        ≤ κ * (√((n : ℝ) * ∑ u, ρ u * #(markedSet (m u) x)) + √((n : ℝ) * Real.log n)) := by
  choose A hA using fun u => hG n k (m u) hn
  refine ⟨A, fun u => (hA u x).1, ?_⟩
  have hJ := sum_mul_sqrt_le (ρ := ρ) (a := fun u => (n : ℝ) * #(markedSet (m u) x)) hρ hsum
    (fun u => by positivity)
  have hJ' : ∑ u, ρ u * ((n : ℝ) * #(markedSet (m u) x))
      = (n : ℝ) * ∑ u, ρ u * #(markedSet (m u) x) := by
    rw [mul_sum]
    exact sum_congr rfl fun u _ => by ring
  rw [hJ'] at hJ
  calc ∑ u, ρ u * (A u).expCost x
      ≤ ∑ u, ρ u * (κ * (√((n : ℝ) * #(markedSet (m u) x)) + √((n : ℝ) * Real.log n))) :=
        sum_le_sum fun u _ => mul_le_mul_of_nonneg_left (hA u x).2 (hρ u)
    _ = κ * (∑ u, ρ u * √((n : ℝ) * #(markedSet (m u) x)) + √((n : ℝ) * Real.log n)) := by
        have h : ∀ u, ρ u * (κ * (√((n : ℝ) * #(markedSet (m u) x)) + √((n : ℝ) * Real.log n)))
            = κ * (ρ u * √((n : ℝ) * #(markedSet (m u) x)))
              + ρ u * (κ * √((n : ℝ) * Real.log n)) := fun u => by ring
        simp only [h, sum_add_distrib, ← mul_sum, ← sum_mul, hsum]
        ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) hκ

/-! ## The arithmetic -/

/-- The cost of one round when the samples have sizes `r` and `k`: find all of `R` and read them,
find all of `S` and read them, search for a violator. -/
noncomputable def roundCost (κ n L r k : ℝ) : ℝ :=
  κ * (√(n * r) + √(n * L)) + r + (κ * (√(n * k) + √(n * L)) + k) + κ * √(n * L)

/-- Reading a sample of size `k ≤ n` costs at most `√(n k)`. -/
theorem le_sqrt_mul_self {n k : ℝ} (hk : 0 ≤ k) (hkn : k ≤ n) : k ≤ √(n * k) := by
  apply Real.le_sqrt_of_sq_le
  nlinarith

/-- A round costs at most `(κ + 1)(√(n r) + √(n k)) + 3 κ √(n L)`. -/
theorem roundCost_le {κ n L r k : ℝ} (hr : 0 ≤ r) (hrn : r ≤ n) (hk : 0 ≤ k) (hkn : k ≤ n) :
    roundCost κ n L r k ≤ (κ + 1) * (√(n * r) + √(n * k)) + 3 * κ * √(n * L) := by
  have h1 := le_sqrt_mul_self hr hrn
  have h2 := le_sqrt_mul_self hk hkn
  unfold roundCost
  nlinarith

/-- `√(a + b) ≤ √a + √b`. -/
theorem sqrt_add_le_sqrt_add_sqrt {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) : √(a + b) ≤ √a + √b := by
  apply Real.sqrt_le_iff.2
  constructor
  · positivity
  · have h1 := Real.sq_sqrt ha
    have h2 := Real.sq_sqrt hb
    have h3 := mul_nonneg (Real.sqrt_nonneg a) (Real.sqrt_nonneg b)
    nlinarith

/-- `√(n c (2 δ² + L)) ≤ 2 √c (δ √n + √(n L))`: this is where `√(n s)` becomes `δ √n`. -/
theorem sqrt_sample_le {n c δ L : ℝ} (hn : 0 ≤ n) (hc : 0 ≤ c) (hδ : 0 ≤ δ) (hL : 0 ≤ L) :
    √(n * (c * (2 * δ ^ 2 + L))) ≤ 2 * √c * (δ * √n + √(n * L)) := by
  have e : n * (c * (2 * δ ^ 2 + L)) = c * (2 * (δ ^ 2 * n) + n * L) := by ring
  rw [e, Real.sqrt_mul hc]
  have h1 : √(2 * (δ ^ 2 * n) + n * L) ≤ √(2 * (δ ^ 2 * n)) + √(n * L) :=
    sqrt_add_le_sqrt_add_sqrt (by positivity) (by positivity)
  have h2 : √(2 * (δ ^ 2 * n)) ≤ 2 * (δ * √n) := by
    apply Real.sqrt_le_iff.2
    constructor
    · positivity
    · have := Real.sq_sqrt hn
      have h3 : 0 ≤ δ ^ 2 * n := by positivity
      nlinarith
  have h3 : 0 ≤ √(n * L) := Real.sqrt_nonneg _
  have h4 : √(2 * (δ ^ 2 * n) + n * L) ≤ 2 * (δ * √n + √(n * L)) := by linarith
  calc √c * √(2 * (δ ^ 2 * n) + n * L)
      ≤ √c * (2 * (δ * √n + √(n * L))) :=
        mul_le_mul_of_nonneg_left h4 (Real.sqrt_nonneg c)
    _ = _ := by ring

/-- The constant of a round. -/
noncomputable def roundConst (κ c : ℝ) : ℝ := 4 * (κ + 1) * √c + 3 * κ

/-- **One round, in expectation.** If both samples have mean size at most `c (2 δ² + L)`, the bound
after using concavity is at most `C (δ √n + √(n L))`. -/
theorem round_bound_le {κ n c δ L K K' : ℝ} (hκ : 0 ≤ κ) (hn : 0 ≤ n) (hc : 0 ≤ c) (hδ : 0 ≤ δ)
    (hL : 0 ≤ L) (hK : K ≤ c * (2 * δ ^ 2 + L)) (hK' : K' ≤ c * (2 * δ ^ 2 + L)) :
    (κ + 1) * (√(n * K') + √(n * K)) + 3 * κ * √(n * L)
      ≤ roundConst κ c * (δ * √n + √(n * L)) := by
  have hm : ∀ {x : ℝ}, x ≤ c * (2 * δ ^ 2 + L) → √(n * x) ≤ 2 * √c * (δ * √n + √(n * L)) := by
    intro x hx
    refine le_trans (Real.sqrt_le_sqrt ?_) (sqrt_sample_le hn hc hδ hL)
    exact mul_le_mul_of_nonneg_left hx hn
  have h1 := hm hK
  have h2 := hm hK'
  have h3 : 0 ≤ δ * √n := by positivity
  have h4 : 0 ≤ √(n * L) := Real.sqrt_nonneg _
  have h5 : √(n * K') + √(n * K) ≤ 4 * √c * (δ * √n + √(n * L)) := by linarith
  have h6 : 3 * κ * √(n * L) ≤ 3 * κ * (δ * √n + √(n * L)) :=
    mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  unfold roundConst
  have h7 := mul_le_mul_of_nonneg_left h5 (by linarith : 0 ≤ κ + 1)
  nlinarith

/-- The query count of the README: `T (δ √n + √(n log n))`. -/
noncomputable def queryCount (T δ n : ℕ) : ℝ :=
  T * (δ * √(n : ℝ) + √((n : ℝ) * Real.log n))

/-- **`T (δ √n + √(n log n)) ≤ 14 (δ² √n log n + δ √n log^{3/2} n)`** for `T = ⌈12 δ ln n⌉`, `n ≥ 2`,
`δ ≥ 1`. -/
theorem queryCount_le {n δ T : ℕ} (hn : 2 ≤ n) (hδ : 1 ≤ δ)
    (hT : T = ⌈12 * (δ : ℝ) * Real.log n⌉₊) :
    queryCount T δ n ≤ 14 * ((δ : ℝ) ^ 2 * √(n : ℝ) * Real.log n
      + δ * √(n : ℝ) * (Real.log n * √(Real.log n))) := by
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hδ1 : (1 : ℝ) ≤ δ := by exact_mod_cast hδ
  have hL : (0.69 : ℝ) ≤ Real.log n := by
    have h1 := Real.log_two_gt_d9
    have h2 := Real.log_le_log (by norm_num) hn2
    linarith
  set L := Real.log n with hLdef
  have hL0 : 0 ≤ L := by linarith
  -- `T ≤ 12 δ L + 1 ≤ 14 δ L`
  have hTle : (T : ℝ) ≤ 14 * δ * L := by
    have h1 : (T : ℝ) < 12 * δ * L + 1 := by
      rw [hT]
      exact Nat.ceil_lt_add_one (by positivity)
    have h2 : (1 : ℝ) ≤ 2 * δ * L := by nlinarith
    linarith
  have hsq : √((n : ℝ) * L) = √(n : ℝ) * √L := Real.sqrt_mul (by positivity) L
  have hnn : 0 ≤ √(n : ℝ) := Real.sqrt_nonneg _
  have hLs : 0 ≤ √L := Real.sqrt_nonneg _
  unfold queryCount
  rw [hsq]
  have hB : 0 ≤ (δ : ℝ) * √(n : ℝ) + √(n : ℝ) * √L := by positivity
  calc (T : ℝ) * ((δ : ℝ) * √(n : ℝ) + √(n : ℝ) * √L)
      ≤ (14 * δ * L) * ((δ : ℝ) * √(n : ℝ) + √(n : ℝ) * √L) :=
        mul_le_mul_of_nonneg_right hTle hB
    _ = _ := by ring

/-! ## The total, over the process -/

namespace Kernel

variable {State Step : Type*} [Fintype Step] (K : Kernel State Step)

theorem expect_add (T : ℕ) (σ : State) (φ ψ : List Step → ℝ) :
    K.expect T σ (fun l => φ l + ψ l) = K.expect T σ φ + K.expect T σ ψ := by
  simp only [K.expect_eq_sum_paths, mul_add, sum_add_distrib]

theorem expect_sum {ι : Type*} (s : Finset ι) (T : ℕ) (σ : State) (φ : ι → List Step → ℝ) :
    K.expect T σ (fun l => ∑ t ∈ s, φ t l) = ∑ t ∈ s, K.expect T σ (φ t) := by
  simp only [K.expect_eq_sum_paths, mul_sum]
  rw [sum_comm]

/-- **Concavity over the whole run**: `E[√φ] ≤ √E[φ]`. -/
theorem expect_sqrt_le (T : ℕ) (σ : State) {φ : List Step → ℝ} (hφ : ∀ l, 0 ≤ φ l) :
    K.expect T σ (fun l => √(φ l)) ≤ √(K.expect T σ φ) := by
  have := Real.strictConcaveOn_sqrt.concaveOn.le_map_sum (t := paths (Step := Step) T)
    (w := K.pathWeight σ) (p := φ) (fun l _ => K.pathWeight_nonneg σ l) (K.pathWeight_sum T σ)
    (fun l _ => hφ l)
  simpa [smul_eq_mul, K.expect_eq_sum_paths] using this

/-- A sum along a path is a sum over the rounds. -/
theorem sum_map_eq_sum_range {α : Type*} (c : α → ℝ) (d : α) (l : List α) :
    (l.map c).sum = ∑ t ∈ range l.length, c (l.getD t d) := by
  induction l with
  | nil => simp
  | cons x l ih =>
    rw [List.length_cons, sum_range_succ', List.map_cons, List.sum_cons, ih]
    simp [add_comm]

end Kernel

/-! ## the cost of quantum search as a round cost -/

/-- What `GroverFindAll` and `GroverFindOne` give for one round: the three searches have error at most
`1/n³` each, and for fixed marks and input the expected queries, with the samples read, are at most
`roundCost`, with `r` and `k` the sizes of the samples. -/
theorem search_cost_le_roundCost {κ : ℝ} (hA : GroverFindAll κ) (hO : GroverFindOne κ) {n k : ℕ}
    (hn : 2 ≤ n) (mR mS mV : Fin n → Fin k → Bool) (x : Fin n → Fin k) :
    ∃ (AR AS : AdaptiveAlg (Fin n) k (Finset (Fin n))) (AV : AdaptiveAlg (Fin n) k (Option (Fin n))),
      AR.failProb x (· = markedSet mR x) ≤ 1 / (n : ℝ) ^ 3 ∧
      AS.failProb x (· = markedSet mS x) ≤ 1 / (n : ℝ) ^ 3 ∧
      AV.failProb x (fun e => match e with
        | some j => j ∈ markedSet mV x
        | none => markedSet mV x = ∅) ≤ 1 / (n : ℝ) ^ 3 ∧
      AR.expCost x + #(markedSet mR x) + (AS.expCost x + #(markedSet mS x)) + AV.expCost x
        ≤ roundCost κ n (Real.log n) #(markedSet mR x) #(markedSet mS x) := by
  obtain ⟨AR, hR⟩ := hA n k mR hn
  obtain ⟨AS, hS⟩ := hA n k mS hn
  obtain ⟨AV, hV⟩ := hO n k mV hn
  refine ⟨AR, AS, AV, (hR x).1, (hS x).1, (hV x).1, ?_⟩
  unfold roundCost
  linarith [(hR x).2, (hS x).2, (hV x).2]

variable {H R : Type*} [DecidableEq H] [Fintype H] [PartialOrder R] (P : Problem H R)

namespace Problem

/-- **The expected query count over the process.** Let `K` be the process, with or without redraw.
Suppose each round's samples have mean size at most `c (2 δ² + ln n)`, over the whole run: `hR` and `hS`.
These are the hypotheses that the README obtains from the lower tail of `W̃`, not proved here. If a round
with samples of sizes `r` and `k` costs `roundCost`, as `search_cost_le_roundCost` says, then `T` rounds
cost in expectation at most `C · T (δ √n + √(n log n))`, with `C = roundConst κ c`. The hypotheses are
means over the whole run because a bound from every reachable state is false: see `Theorem1.lean`. -/
theorem expected_queries_le {State : Type*} (K : Kernel State (Finset H × Finset H)) {κ c : ℝ}
    (hκ : 0 ≤ κ) (hc : 0 ≤ c) (hn : 1 ≤ Fintype.card H) (T : ℕ) (σ : State)
    (hR : ∀ t < T, K.expect T σ (fun l => (#(l.getD t (∅, ∅)).1 : ℝ))
      ≤ c * (2 * (P.combDim : ℝ) ^ 2 + Real.log (Fintype.card H)))
    (hS : ∀ t < T, K.expect T σ (fun l => (#(l.getD t (∅, ∅)).2 : ℝ))
      ≤ c * (2 * (P.combDim : ℝ) ^ 2 + Real.log (Fintype.card H))) :
    K.expect T σ (fun l => (l.map fun x =>
        roundCost κ (Fintype.card H) (Real.log (Fintype.card H)) #x.1 #x.2).sum)
      ≤ roundConst κ c * queryCount T P.combDim (Fintype.card H) := by
  set n : ℝ := (Fintype.card H : ℝ) with hndef
  set L := Real.log (Fintype.card H) with hLdef
  have hn0 : 0 ≤ n := Nat.cast_nonneg _
  have hL0 : 0 ≤ L := Real.log_nonneg (by exact_mod_cast hn)
  have hδ0 : (0 : ℝ) ≤ P.combDim := Nat.cast_nonneg _
  have hκ1 : 0 ≤ κ + 1 := by linarith
  have hcard : ∀ A : Finset H, (#A : ℝ) ≤ n := fun A => by
    rw [hndef]
    exact_mod_cast card_le_univ A
  -- the bound on a path, round by round
  set d : Finset H × Finset H := (∅, ∅)
  set rt : ℕ → List (Finset H × Finset H) → ℝ := fun t l => (#(l.getD t d).1 : ℝ)
  set kt : ℕ → List (Finset H × Finset H) → ℝ := fun t l => (#(l.getD t d).2 : ℝ)
  have hpath : ∀ l : List (Finset H × Finset H), l.length = T →
      (l.map fun x => roundCost κ n L #x.1 #x.2).sum
        ≤ ∑ t ∈ range T, ((κ + 1) * (√(n * rt t l) + √(n * kt t l)) + 3 * κ * √(n * L)) := by
    intro l hl
    rw [Kernel.sum_map_eq_sum_range _ d, hl]
    exact sum_le_sum fun t _ =>
      roundCost_le (by positivity) (hcard _) (by positivity) (hcard _)
  have hround : ∀ t ∈ range T,
      K.expect T σ (fun l => (κ + 1) * (√(n * rt t l) + √(n * kt t l)) + 3 * κ * √(n * L))
        ≤ roundConst κ c * (P.combDim * √n + √(n * L)) := by
    intro t ht
    have ht' := mem_range.1 ht
    have hjr : K.expect T σ (fun l => √(n * rt t l)) ≤ √(n * K.expect T σ (rt t)) := by
      have := K.expect_sqrt_le T σ (φ := fun l => n * rt t l) (fun l => by positivity)
      rwa [K.expect_const_mul] at this
    have hjk : K.expect T σ (fun l => √(n * kt t l)) ≤ √(n * K.expect T σ (kt t)) := by
      have := K.expect_sqrt_le T σ (φ := fun l => n * kt t l) (fun l => by positivity)
      rwa [K.expect_const_mul] at this
    have hb := round_bound_le (n := n) (L := L) hκ hn0 hc hδ0 hL0 (hS t ht') (hR t ht')
    have he : K.expect T σ (fun l => (κ + 1) * (√(n * rt t l) + √(n * kt t l)) + 3 * κ * √(n * L))
        = (κ + 1) * (K.expect T σ (fun l => √(n * rt t l)) + K.expect T σ (fun l => √(n * kt t l)))
          + 3 * κ * √(n * L) := by
      rw [K.expect_add T σ (fun l => (κ + 1) * (√(n * rt t l) + √(n * kt t l)))
        (fun _ => 3 * κ * √(n * L)), K.expect_const, K.expect_const_mul,
        K.expect_add T σ (fun l => √(n * rt t l)) (fun l => √(n * kt t l))]
    rw [he]
    refine le_trans ?_ hb
    have := mul_le_mul_of_nonneg_left (add_le_add hjr hjk) hκ1
    linarith
  calc K.expect T σ (fun l => (l.map fun x => roundCost κ n L #x.1 #x.2).sum)
      ≤ K.expect T σ (fun l => ∑ t ∈ range T,
          ((κ + 1) * (√(n * rt t l) + √(n * kt t l)) + 3 * κ * √(n * L))) := K.expect_mono hpath
    _ = ∑ t ∈ range T, K.expect T σ (fun l =>
          (κ + 1) * (√(n * rt t l) + √(n * kt t l)) + 3 * κ * √(n * L)) := K.expect_sum _ _ _ _
    _ ≤ ∑ _t ∈ range T, roundConst κ c * (P.combDim * √n + √(n * L)) := sum_le_sum hround
    _ = roundConst κ c * queryCount T P.combDim (Fintype.card H) := by
        simp only [sum_const, card_range, nsmul_eq_mul, queryCount]
        ring

/-- **The bound of Theorem 1**: with `T = ⌈12 δ ln n⌉`, the expected queries are
`O(δ² √n log n + δ √n log^{3/2} n)`, under the hypotheses of `expected_queries_le`. -/
theorem expected_queries_le_log {State : Type*} (K : Kernel State (Finset H × Finset H)) {κ c : ℝ}
    (hκ : 0 ≤ κ) (hc : 0 ≤ c) (hn : 2 ≤ Fintype.card H) (hδ : 1 ≤ P.combDim) (σ : State)
    {T : ℕ} (hT : T = ⌈12 * (P.combDim : ℝ) * Real.log (Fintype.card H)⌉₊)
    (hR : ∀ t < T, K.expect T σ (fun l => (#(l.getD t (∅, ∅)).1 : ℝ))
      ≤ c * (2 * (P.combDim : ℝ) ^ 2 + Real.log (Fintype.card H)))
    (hS : ∀ t < T, K.expect T σ (fun l => (#(l.getD t (∅, ∅)).2 : ℝ))
      ≤ c * (2 * (P.combDim : ℝ) ^ 2 + Real.log (Fintype.card H))) :
    K.expect T σ (fun l => (l.map fun x =>
        roundCost κ (Fintype.card H) (Real.log (Fintype.card H)) #x.1 #x.2).sum)
      ≤ roundConst κ c * (14 * ((P.combDim : ℝ) ^ 2 * √(Fintype.card H : ℝ) * Real.log (Fintype.card H)
          + P.combDim * √(Fintype.card H : ℝ)
            * (Real.log (Fintype.card H) * √(Real.log (Fintype.card H))))) := by
  have hC : 0 ≤ roundConst κ c := by
    unfold roundConst
    have := Real.sqrt_nonneg c
    positivity
  exact (P.expected_queries_le K hκ hc (by omega) T σ hR hS).trans
    (mul_le_mul_of_nonneg_left (queryCount_le hn hδ hT) hC)

end Problem

end LPType
