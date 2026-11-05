import QuantumBranching.Model
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# The composition

Fix a setting `S`, with the conditions (M1), (M2) and (M3), and the primitives. The search is
parametrized by a real level `m`, and runs on instances with `log (B x) ≤ m`.

- At a level `m ≤ W q * log N`, it is the classical run on the full call tree, made reversible by
  pebbling. Its budget is `baseBudget`.
- At a level above, it is the walk on the OR-tree of `x` with the parameter `tPrime m = exp m * coef`,
  which is computed from `m` alone. A value call at `v` is the search at level `padLevel N q (B v)`, and
  it is padded to the budget `levelTime` of that level.

`levelTime` is therefore a closed formula in `m`, and `time_bound` follows from it, from the walk
bound and from `QBound` alone. What uses (M1), (M2) and (M3) is that this formula is the time of the
search, which is the statement of `search_valid`, for `log (B x) ≤ m`, with `x` the root or a target of a value call.

- The base run fits the budget. This uses (M3).
- Above the base, the true sum `treeSq x` of the squared step counts, over the whole OR-tree of `x`, is
  at most `tPrime m`. This is the precondition of the walk, and it uses (M1) across depths, through
  antichains, and the bound on the squares of the budgets of lower levels.
- The walk then accepts as it should, with the marked leaves of `answer_iff_marked`.
- Every value call `y` at a node `v` has `log (B y) ≤ padLevel N q (B v)`, by (M2), so it is an instance
  of the search at that level.
- The level drops by at least `log N`, from `log (B v) ≤ m + q * log N`, which follows from (M1).

`time_bound` is the theorem for the time: `levelTime (log (B x)) ≤ N ^ (A q / 2) * √(B x)`, and
`theorem1` is the form with polynomials, with an exponent that does not depend on `n`.

`quadratic_bound_setting` is the recursion for a budget that is not given by a formula: any `Q` with
the base, and with the bound of the walk for every upper bound on the sums over the instances of level
`m`, has `Q m ^ 2 ≤ N ^ A q * exp m`. It applies `quadratic_bound`, by induction on the levels.

`qubits_levels` and `qubits_polynomial` are the arithmetic of the space recursion, `amplitude_budget`
the sum of the amplitude errors, and `reduction_error` the number of rounds of error reduction.
-/

open Real

namespace QuantumBranching

/-- The square of a sum of three terms. -/
theorem sq_three (a b c : ℝ) : (2 * (a + b + c)) ^ 2 ≤ 12 * (a ^ 2 + b ^ 2 + c ^ 2) := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (a - c)]

/-- The sum over the nodes of an OR-tree, by depth. -/
theorem list_flatMap_sum {α β : Type*} (L : List α) (g : α → List β) (f : β → ℝ) :
    ((L.flatMap g).map f).sum = (L.map fun t => ((g t).map f).sum).sum := by
  induction L with
  | nil => simp
  | cons a L ih => simp [List.flatMap_cons, ih]

theorem range_sum_list {α : Type*} (L : List α) (H : ℕ) (h : ℕ → α → ℝ) :
    ∑ ℓ ∈ Finset.range H, (L.map (h ℓ)).sum = (L.map fun t => ∑ ℓ ∈ Finset.range H, h ℓ t).sum := by
  induction L with
  | nil => simp
  | cons a L ih => simp [Finset.sum_add_distrib, ih]

namespace Proc

variable {I : Type*} (P : Proc I)

/-- The sum over the nodes of the OR-tree is at most the sum over the depths up to the rank. -/
theorem nodes_sum_le_levels (f : I → ℝ) (x : I) :
    ∀ H, P.rank x < H → (((P.orTree x).nodes).map f).sum ≤
      ∑ ℓ ∈ Finset.range H, (((P.orTree x).levelNodes ℓ).map f).sum := by
  induction hk : P.rank x using Nat.strong_induction_on generalizing x with
  | _ k ih =>
    intro H hH
    obtain ⟨H', rfl⟩ : ∃ H', H = H' + 1 := ⟨H - 1, by omega⟩
    rw [Finset.sum_range_succ']
    cases ho : P.outcome x with
    | inl b =>
      rw [P.orTree_inl ho, ORTree.nodes_node]
      have h0 : ∀ ℓ, (((ORTree.node x [ORTree.mark b]).levelNodes (ℓ + 1)).map f).sum = 0 := by
        intro ℓ
        rw [ORTree.levelNodes_succ]
        simp
      simp [h0]
    | inr cs =>
      rw [P.orTree_inr ho, ORTree.nodes_node]
      simp only [ORTree.levelNodes_succ, ORTree.levelNodes_zero, List.map_cons, List.map_nil,
        List.sum_cons, List.sum_nil, add_zero]
      rw [add_comm]
      refine add_le_add_left ?_ (f x)
      simp only [list_flatMap_sum]
      rw [range_sum_list]
      simp only [List.map_map]
      refine list_map_sum_le fun c hc => ?_
      have hr := P.rank_child ho hc
      exact ih _ (hk ▸ hr) c rfl H' (by omega)

end Proc

namespace Setting

variable {I : Type*} (S : Setting I)

/-- The nodes of the tree of `x`. -/
def treeNodes (x : I) : List I := (S.proc.orTree x).nodes

/-- The number of children charged at a node. A node with no children is charged one. -/
def width (v : I) : ℕ := max 1 (S.proc.children v).length

section

variable (G : Primitives) (n : ℕ) (N : ℝ) (q : ℕ) (η : ℝ) (d : ℕ)

/-- The parameter of the walk at level `m`, computed from `m` alone. -/
noncomputable def tPrime (m : ℝ) : ℝ := exp m * coef N q

/-- The bound on the steps of the classical run at level `m`. -/
noncomputable def runBound (m : ℝ) : ℝ := (S.loc + S.r * S.ρ) * S.K * exp m

/-- The budget of the reversible classical run at level `m`. -/
noncomputable def baseBudget (m : ℝ) : ℝ :=
  η * S.runBound m ^ ((1585 : ℝ) / 1000) * (1 + log (S.runBound m)) ^ d

open Classical in
/-- The time of the search at level `m`. -/
noncomputable def levelTime (m : ℝ) : ℝ :=
  if m ≤ (W q : ℝ) * log N then S.baseBudget η d m
  else (S.r : ℝ) * G.walkTime n (tPrime N q m) ((S.D : ℝ) + 1)

/-- The number of steps to a child of `v`, for a budget `Q` of the levels: the local work, the value
calls padded to their budget, and the Box. A child is computed and uncomputed. -/
noncomputable def stepOf (Q : ℝ → ℝ) (v : I) : ℝ :=
  2 * (S.loc + ((S.proc.calls v).length : ℝ) * Q (padLevel N q (S.B v)) + S.boxCost v)

/-- The sum of the squared step counts over the whole OR-tree of `x`, for a budget `Q`. -/
noncomputable def treeSqOf (Q : ℝ → ℝ) (x : I) : ℝ :=
  ((S.treeNodes x).map fun v => (S.width v : ℝ) * S.stepOf N q Q v ^ 2).sum

/-- The number of steps to a child of `v`, for the budget `levelTime`. -/
noncomputable def stepTime (v : I) : ℝ := S.stepOf N q (S.levelTime G n N q η d) v

/-- The sum of the squared step counts over the whole OR-tree of `x`, for the budget `levelTime`. -/
noncomputable def treeSq (x : I) : ℝ := S.treeSqOf N q (S.levelTime G n N q η d) x

/-- The squared step counts of the children of `v`, as a list. -/
noncomputable def kidsOf (Q : ℝ → ℝ) (v : I) : List ℝ :=
  List.replicate (S.width v) (S.stepOf N q Q v ^ 2)

theorem treeSqOf_eq (Q : ℝ → ℝ) (x : I) :
    S.treeSqOf N q Q x = ((S.treeNodes x).map fun v => (S.kidsOf N q Q v).sum).sum := by
  unfold Setting.treeSqOf
  congr 1
  refine List.map_congr_left fun v _ => ?_
  simp [Setting.kidsOf, List.sum_replicate, nsmul_eq_mul]

end

variable {S}

section Conds

variable (h : S.Conditions)
include h

theorem B_pos (x : I) : 0 < S.B x := by linarith [h.B_ge x]

theorem one_le_B (x : I) : 1 ≤ S.B x := by linarith [h.B_ge x]

theorem log_B_pos (x : I) : 0 < log (S.B x) := Real.log_pos (by linarith [h.B_ge x])

/-- (M1) across depths. -/
theorem sum_nodes_le {x : I} (hx : S.Searched x) :
    ((S.treeNodes x).map S.B).sum ≤ ((S.D : ℝ) + 1) * S.K * S.B x := by
  have h1 := S.proc.nodes_sum_le_levels S.B x (S.D + 1)
    (Nat.lt_succ_of_le (h.rank_le x))
  refine h1.trans ?_
  have h2 : ∀ ℓ ∈ Finset.range (S.D + 1),
      (((S.proc.orTree x).levelNodes ℓ).map S.B).sum ≤ S.K * S.B x := fun ℓ _ =>
    h.M1 x hx _ (ORTree.isAntichain_levelNodes _ ℓ)
  refine (Finset.sum_le_sum h2).trans (le_of_eq ?_)
  simp [Finset.sum_const, nsmul_eq_mul]
  ring

/-- The running time of the classical run, from (M3). -/
theorem runTime_le (x : I) : S.runTime x ≤ (S.loc + S.r * S.ρ) * (S.K * S.B x) := by
  have hρ := h.ρ_nonneg
  have hloc := h.loc_ge
  have hr : (0 : ℝ) ≤ (S.r : ℝ) := Nat.cast_nonneg _
  have hC : 0 ≤ S.loc + S.r * S.ρ := by positivity
  have hw : ∀ a, S.loc + S.boxCost a ≤ (S.loc + S.r * S.ρ) * S.m3Weight a := by
    intro a
    unfold Setting.boxCost Setting.m3Weight
    cases hb : S.proc.boxFlag a with
    | false =>
      simp only [Bool.false_eq_true, ite_false, add_zero, mul_one]
      have : 0 ≤ S.r * S.ρ := by positivity
      linarith
    | true =>
      simp only [ite_true]
      obtain ⟨_, h2⟩ := h.box_time a hb
      have hB1 := one_le_B h a
      have hsq : √(S.B a) ≤ S.B a := by
        rw [Real.sqrt_le_left (by linarith)]
        nlinarith
      have h3 : S.boxTime a ≤ S.ρ * S.B a := h2.trans (mul_le_mul_of_nonneg_left hsq hρ)
      have h4 : (S.r : ℝ) * S.boxTime a ≤ S.r * (S.ρ * S.B a) := mul_le_mul_of_nonneg_left h3 hr
      have h5 : 0 ≤ S.loc * S.B a := by positivity
      have h6 : 0 ≤ S.r * S.ρ := by positivity
      nlinarith
  have h7 := S.proc.callSum_le (w := fun a => S.loc + S.boxCost a) (w' := S.m3Weight) hw x
  exact h7.trans (mul_le_mul_of_nonneg_left (h.M3 x) hC)

theorem one_le_runTime (x : I) : 1 ≤ S.runTime x := by
  have hzero : ∀ a, (1 : ℝ) ≤ S.loc + S.boxCost a := by
    intro a
    have hloc := h.loc_ge
    have hc : 0 ≤ S.boxCost a := by
      unfold Setting.boxCost
      cases hb : S.proc.boxFlag a with
      | false => simp
      | true =>
        simp only [ite_true]
        exact mul_nonneg (Nat.cast_nonneg _) (h.box_time a hb).1
    linarith
  unfold Setting.runTime
  induction hk : S.proc.rank x using Nat.strong_induction_on generalizing x with
  | _ k ih =>
    rw [S.proc.callSum_eq]
    have h1 : 0 ≤ ((S.proc.calls x).map (S.proc.callSum fun a => S.loc + S.boxCost a)).sum :=
      list_map_sum_nonneg fun y hy => by
        have := ih _ (hk ▸ S.proc.rank_call hy) y rfl
        linarith
    have h2 : 0 ≤ ((S.proc.children x).map (S.proc.callSum fun a => S.loc + S.boxCost a)).sum :=
      list_map_sum_nonneg fun c hc => by
        have := ih _ (hk ▸ S.proc.rank_children hc) c rfl
        linarith
    have h3 := hzero x
    linarith

end Conds

section Valid

variable {G : Primitives} {n : ℕ} {N : ℝ} {q : ℕ} {κ η : ℕ → ℝ} {d : ℕ}

variable (hC : S.Conditions) {κn ηn : ℝ} (hQ : S.QBound N q κn ηn d)
include hC hQ

/-- (M1) across depths, in powers of `N`. -/
theorem sum_nodes_le_pow {x : I} (hx : S.Searched x) :
    ((S.treeNodes x).map S.B).sum ≤ N ^ q * S.B x := by
  refine (sum_nodes_le hC hx).trans ?_
  exact mul_le_mul_of_nonneg_right hQ.depth_le (B_pos hC x).le

/-- The bound on `B v` for a node `v` of the tree of `x`, from (M1). -/
theorem log_node_le {x v : I} (hR : S.Searched x) (hv : v ∈ S.treeNodes x) :
    log (S.B v) ≤ log (S.B x) + q * log N := by
  have hN0 := N_pos hQ.N_ge
  have hnn : ∀ a ∈ (S.treeNodes x).map S.B, 0 ≤ a := by
    intro a ha
    obtain ⟨b, _, rfl⟩ := List.mem_map.mp ha
    exact (B_pos hC b).le
  have h1 : S.B v ≤ N ^ q * S.B x :=
    (List.single_le_sum hnn _ (List.mem_map_of_mem hv)).trans (sum_nodes_le_pow hC hQ hR)
  have h2 := Real.log_le_log (B_pos hC v) h1
  rw [Real.log_mul (by positivity) (B_pos hC x).ne', Real.log_pow] at h2
  linarith

/-- **The level drops.** -/
theorem level_drop {x v : I} {m : ℝ} (hR : S.Searched x) (hx : log (S.B x) ≤ m) (hm : (W q : ℝ) * log N < m)
    (hv : v ∈ S.treeNodes x) : padLevel N q (S.B v) ≤ m - log N :=
  padLevel_drop hQ.N_ge hQ.q_pos hm ((log_node_le hC hQ hR hv).trans (by linarith))

/-- **A value call is an instance of the search at the level of its node.** This is (M2). -/
theorem call_level {v y : I} (hy : y ∈ S.proc.calls v) :
    log (S.B y) ≤ padLevel N q (S.B v) := by
  have h1 := hC.M2 v y hy
  have h2 := hQ.c_le
  unfold padLevel
  linarith

omit hC hQ in
/-- The arithmetic of the base: `3.17 * (q + W) ≤ 4 * W`, which is `3.17 * q ≤ 0.83 * W`. -/
theorem base_exponent (hl : 0 < log N) :
    (2 * ((1585 : ℝ) / 1000)) * (((q + W q : ℕ) : ℝ) * log N) ≤ ((4 * W q : ℕ) : ℝ) * log N := by
  have hW : ((W q : ℕ) : ℝ) = 22 * q + 3 := by simp only [W]; push_cast; ring
  have hq : (0 : ℝ) ≤ q * log N := mul_nonneg (Nat.cast_nonneg _) hl.le
  push_cast
  rw [hW]
  nlinarith

/-- The base budget, squared. -/
theorem baseBudget_sq {m : ℝ} (hm0 : 0 ≤ m) (hm : m ≤ (W q : ℝ) * log N) :
    S.baseBudget ηn d m ^ 2 ≤ N ^ (q + 4 * W q) := by
  have hN := hQ.N_ge
  have hN0 := N_pos hN
  have hl := log_N_pos hN
  set τb := S.runBound m with hτb
  set a : ℝ := ((q + W q : ℕ) : ℝ) * log N with ha
  have hK := hQ.K_ge
  have hloc := hC.loc_ge
  have hρ := hC.ρ_nonneg
  have hr : (0 : ℝ) ≤ (S.r : ℝ) := Nat.cast_nonneg _
  have hC1 : 1 ≤ (S.loc + S.r * S.ρ) * S.K := by
    have : 0 ≤ (S.r : ℝ) * S.ρ := by positivity
    nlinarith
  have he1 := Real.one_le_exp hm0
  have hτ1 : 1 ≤ τb := by
    simp only [hτb, Setting.runBound]
    nlinarith
  have hτle : τb ≤ exp a := by
    have h1 : exp m ≤ N ^ W q := by
      rw [pow_eq_exp hN]
      exact Real.exp_le_exp.mpr hm
    have h2 : τb ≤ N ^ q * N ^ W q := by
      simp only [hτb, Setting.runBound]
      exact mul_le_mul hQ.run_le h1 (Real.exp_pos _).le (by positivity)
    rw [← pow_add, pow_eq_exp hN] at h2
    exact h2
  have hτ0 : 0 ≤ τb := by linarith
  have hlog0 : 0 ≤ log τb := Real.log_nonneg hτ1
  have hlogle : log τb ≤ a := by
    rw [Real.log_le_iff_le_exp (by linarith)]
    exact hτle
  have hpw : τb ^ ((1585 : ℝ) / 1000) ≤ exp (a * ((1585 : ℝ) / 1000)) := by
    rw [Real.exp_mul]
    exact Real.rpow_le_rpow hτ0 hτle (by norm_num)
  have hpw0 : 0 ≤ τb ^ ((1585 : ℝ) / 1000) := Real.rpow_nonneg hτ0 _
  have hpw2 : (τb ^ ((1585 : ℝ) / 1000)) ^ 2 ≤ N ^ (4 * W q) := by
    have h1 := pow_le_pow_left₀ hpw0 hpw 2
    refine h1.trans ?_
    rw [← Real.exp_nat_mul, pow_eq_exp hN]
    apply Real.exp_le_exp.mpr
    have := base_exponent (q := q) hl
    push_cast at this ⊢
    simp only [ha]
    push_cast
    linarith
  have hL : (1 + log τb) ^ d ≤ (1 + a) ^ d := pow_le_pow_left₀ (by linarith) (by linarith) d
  have hL0 : 0 ≤ (1 + log τb) ^ d := by positivity
  have hL2 : ((1 + log τb) ^ d) ^ 2 ≤ (1 + a) ^ (2 * d) := by
    calc ((1 + log τb) ^ d) ^ 2 ≤ ((1 + a) ^ d) ^ 2 := pow_le_pow_left₀ hL0 hL 2
      _ = (1 + a) ^ (2 * d) := by rw [← pow_mul, mul_comm d 2]
  have hη2 : ηn ^ 2 * ((1 + log τb) ^ d) ^ 2 ≤ N ^ q :=
    (mul_le_mul_of_nonneg_left hL2 (sq_nonneg _)).trans hQ.base_sq
  have hsq0 : 0 ≤ (τb ^ ((1585 : ℝ) / 1000)) ^ 2 := sq_nonneg _
  have hNq : 0 < N ^ q := pow_pos hN0 q
  unfold Setting.baseBudget
  rw [← hτb, pow_add]
  calc (ηn * τb ^ ((1585 : ℝ) / 1000) * (1 + log τb) ^ d) ^ 2
      = (ηn ^ 2 * ((1 + log τb) ^ d) ^ 2) * (τb ^ ((1585 : ℝ) / 1000)) ^ 2 := by ring
    _ ≤ N ^ q * (τb ^ ((1585 : ℝ) / 1000)) ^ 2 := mul_le_mul_of_nonneg_right hη2 hsq0
    _ ≤ N ^ q * N ^ (4 * W q) := mul_le_mul_of_nonneg_left hpw2 hNq.le

omit hC in
/-- The time of the level above the base, squared, from the bound of the walk. -/
theorem walk_sq {m : ℝ} (hwalk : WalkBound G κ) (hκ : κ n = κn) (hm : (W q : ℝ) * log N < m) :
    ((S.r : ℝ) * G.walkTime n (tPrime N q m) ((S.D : ℝ) + 1)) ^ 2 ≤ N ^ A q * exp m := by
  have hN := hQ.N_ge
  have hN0 := N_pos hN
  have hl := log_N_pos hN
  have hm0 : 0 < m := lt_of_le_of_lt (by positivity) hm
  have hT1 : 1 ≤ tPrime N q m := by
    unfold tPrime
    have h1 := one_le_coef (q := q) hN
    have h2 := Real.one_le_exp hm0.le
    nlinarith
  have hD1 : (1 : ℝ) ≤ (S.D : ℝ) + 1 := by
    have : (0 : ℝ) ≤ (S.D : ℝ) := Nat.cast_nonneg _
    linarith
  have hT0 : 0 ≤ tPrime N q m := by linarith
  obtain ⟨h1, _, _⟩ := hwalk n (tPrime N q m) (tPrime N q m) ((S.D : ℝ) + 1) hT0 le_rfl hT1 hD1
  have hnn := G.walkTime_nonneg n (tPrime N q m) ((S.D : ℝ) + 1)
  have hs : 0 ≤ tPrime N q m * ((S.D : ℝ) + 1) := by positivity
  rw [hκ] at h1
  have hsq : G.walkTime n (tPrime N q m) ((S.D : ℝ) + 1) ^ 2 ≤
      κn ^ 2 * (tPrime N q m * ((S.D : ℝ) + 1)) := by
    have := pow_le_pow_left₀ hnn h1 2
    rwa [mul_pow, Real.sq_sqrt hs] at this
  have hr2 : (0 : ℝ) ≤ (S.r : ℝ) ^ 2 := by positivity
  calc ((S.r : ℝ) * G.walkTime n (tPrime N q m) ((S.D : ℝ) + 1)) ^ 2
      = (S.r : ℝ) ^ 2 * G.walkTime n (tPrime N q m) ((S.D : ℝ) + 1) ^ 2 := by ring
    _ ≤ (S.r : ℝ) ^ 2 * (κn ^ 2 * (tPrime N q m * ((S.D : ℝ) + 1))) :=
        mul_le_mul_of_nonneg_left hsq hr2
    _ = (((S.r : ℝ) * κn) ^ 2 * ((S.D : ℝ) + 1)) * tPrime N q m := by ring
    _ ≤ N ^ (2 * q) * tPrime N q m := mul_le_mul_of_nonneg_right hQ.walk_sq hT0
    _ = (N ^ (2 * q) * coef N q) * exp m := by unfold tPrime; ring
    _ ≤ N ^ A q * exp m := mul_le_mul_of_nonneg_right (four_terms hN) (Real.exp_pos _).le

/-- The budget of a level, squared, in the two cases. -/
theorem levelTime_sq_base {m : ℝ} (hm0 : 0 ≤ m) (hm : m ≤ (W q : ℝ) * log N) :
    S.levelTime G n N q ηn d m ^ 2 ≤ N ^ (q + 4 * W q) := by
  unfold Setting.levelTime
  rw [ite_eq_left hm]
  exact baseBudget_sq hC hQ hm0 hm

omit hC in
theorem levelTime_sq_step {m : ℝ} (hwalk : WalkBound G κ) (hκ : κ n = κn)
    (hm : (W q : ℝ) * log N < m) :
    S.levelTime G n N q ηn d m ^ 2 ≤ N ^ A q * exp m := by
  unfold Setting.levelTime
  rw [ite_eq_right (not_le.mpr hm)]
  exact walk_sq hQ hwalk hκ hm

/-- The budget of the calls at a node, squared: the terms of the estimate. -/
theorem budget_le (hwalk : WalkBound G κ) (hκ : κ n = κn) (v : I) :
    S.levelTime G n N q ηn d (padLevel N q (S.B v)) ^ 2 ≤
      N ^ (q + 4 * W q) + N ^ (A q + q - (7 * q + 1)) * S.B v :=
  budget_bound hQ.N_ge (B_pos hC v)
    (levelTime_sq_base hC hQ (by
      have hl := log_N_pos hQ.N_ge
      have h1 : 0 ≤ log (S.B v) := (log_B_pos hC v).le
      unfold padLevel
      positivity))
    (levelTime_sq_step hQ hwalk hκ)

/-- **The cost of a child.** -/
theorem stepOf_sq_le (Q : ℝ → ℝ) (v : I) :
    S.stepOf N q Q v ^ 2 ≤ N ^ q * (1 + N ^ q * Q (padLevel N q (S.B v)) ^ 2 + S.B v) := by
  have hN := hQ.N_ge
  have hN0 := N_pos hN
  set Qv := Q (padLevel N q (S.B v)) with hQv
  have hb := B_pos hC v
  have hNq : 0 < N ^ q := pow_pos hN0 q
  have hcalls : ((S.proc.calls v).length : ℝ) ≤ S.s := by exact_mod_cast hC.calls_le v
  have hcalls0 : (0 : ℝ) ≤ ((S.proc.calls v).length : ℝ) := Nat.cast_nonneg _
  have hcsq : ((S.proc.calls v).length : ℝ) ^ 2 ≤ (S.s : ℝ) ^ 2 := pow_le_pow_left₀ hcalls0 hcalls 2
  have ht1 : 12 * S.loc ^ 2 ≤ N ^ q * 1 := by simpa using hQ.loc_sq
  have ht2 : 12 * (((S.proc.calls v).length : ℝ) * Qv) ^ 2 ≤ N ^ q * (N ^ q * Qv ^ 2) := by
    have hq2 : N ^ (2 * q) = N ^ q * N ^ q := by rw [two_mul, pow_add]
    have := hQ.calls_sq
    rw [hq2] at this
    have h1 : 12 * ((S.proc.calls v).length : ℝ) ^ 2 ≤ N ^ q * N ^ q := by nlinarith
    calc 12 * (((S.proc.calls v).length : ℝ) * Qv) ^ 2
        = (12 * ((S.proc.calls v).length : ℝ) ^ 2) * Qv ^ 2 := by ring
      _ ≤ (N ^ q * N ^ q) * Qv ^ 2 := mul_le_mul_of_nonneg_right h1 (sq_nonneg _)
      _ = _ := by ring
  have ht3 : 12 * S.boxCost v ^ 2 ≤ N ^ q * S.B v := by
    unfold Setting.boxCost
    cases hbf : S.proc.boxFlag v with
    | false =>
      simp only [Bool.false_eq_true, ite_false]
      have : 0 ≤ N ^ q * S.B v := by positivity
      simpa using this
    | true =>
      simp only [ite_true]
      obtain ⟨h1, h2⟩ := hC.box_time v hbf
      have hr : (0 : ℝ) ≤ (S.r : ℝ) := Nat.cast_nonneg _
      have h3 : ((S.r : ℝ) * S.boxTime v) ^ 2 ≤ ((S.r : ℝ) * S.ρ) ^ 2 * S.B v := by
        have h4 : (S.boxTime v) ^ 2 ≤ (S.ρ * √(S.B v)) ^ 2 := pow_le_pow_left₀ h1 h2 2
        rw [mul_pow S.ρ, Real.sq_sqrt hb.le] at h4
        calc ((S.r : ℝ) * S.boxTime v) ^ 2 = (S.r : ℝ) ^ 2 * S.boxTime v ^ 2 := by ring
          _ ≤ (S.r : ℝ) ^ 2 * (S.ρ ^ 2 * S.B v) :=
              mul_le_mul_of_nonneg_left h4 (by positivity)
          _ = _ := by ring
      have h5 := mul_le_mul_of_nonneg_right hQ.box_sq hb.le
      nlinarith
  unfold Setting.stepOf
  refine (sq_three _ _ _).trans ?_
  rw [← hQv]
  nlinarith

/-- The number of children, as a power of `N`. -/
theorem kidsOf_length (Q : ℝ → ℝ) (v : I) : ((S.kidsOf N q Q v).length : ℝ) ≤ N ^ q := by
  simp only [Setting.kidsOf, List.length_replicate]
  have h1 : ((S.width v : ℕ) : ℝ) ≤ (S.t : ℝ) + 1 := by
    have : S.width v ≤ S.t + 1 := by
      unfold Setting.width
      have := hC.width_le v
      omega
    exact_mod_cast this
  exact h1.trans hQ.t_le

/-- **The precondition of the walk.** Above the base, the sum of the squared step counts over the
whole OR-tree of `x` is at most the parameter of the walk. -/
theorem treeSq_le (hwalk : WalkBound G κ) (hκ : κ n = κn) {x : I} {m : ℝ}
    (hR : S.Searched x) (hx : log (S.B x) ≤ m) : S.treeSq G n N q ηn d x ≤ tPrime N q m := by
  have hN := hQ.N_ge
  have hN0 := N_pos hN
  have hNq : 0 ≤ N ^ q := by positivity
  set Q := S.levelTime G n N q ηn d with hQdef
  have hest := sum_estimate (q := q) hN S.B hC.B_ge (S.treeNodes x) (S.B x)
    (sum_nodes_le_pow hC hQ hR) (S.kidsOf N q Q)
    (fun v => N ^ q * Q (padLevel N q (S.B v)) ^ 2) (kidsOf_length hC hQ Q)
    (fun v _ c hc => by
      have := List.eq_of_mem_replicate hc
      rw [this]
      exact stepOf_sq_le hC hQ Q v)
    (fun v _ => by positivity)
    (fun v _ => mul_le_mul_of_nonneg_left (budget_le hC hQ hwalk hκ v) hNq)
  have hBx : S.B x ≤ exp m := by
    rw [← Real.exp_log (B_pos hC x)]
    exact Real.exp_le_exp.mpr hx
  unfold Setting.treeSq
  rw [treeSqOf_eq]
  exact hest.trans (mul_le_mul_of_nonneg_right hBx (coef_pos hN).le)

/-- **The recursion on the tree.** For any budget `Q` of the levels, with the bound of the walk for
every upper bound `T` on the sums of the squared step counts at level `m`, and with the base, the
bound `Q m ^ 2 ≤ N ^ A q * exp m` follows by `quadratic_bound`. The hypotheses (M1) and the cost of a
child come from the setting, for the whole OR-tree. -/
theorem quadratic_bound_setting (Q : ℝ → ℝ)
    (hwalk : ∀ m, (W q : ℝ) * log N < m → ∀ T, 0 ≤ T →
      (∀ x, S.Searched x → log (S.B x) ≤ m → S.treeSqOf N q Q x ≤ T) → Q m ^ 2 ≤ N ^ (2 * q) * T)
    (hbase : ∀ m, m ≤ (W q : ℝ) * log N → Q m ^ 2 ≤ N ^ (q + 4 * W q)) {m : ℝ} (hm : 0 ≤ m) :
    Q m ^ 2 ≤ N ^ A q * exp m := by
  have hN := hQ.N_ge
  have hl := log_N_pos hN
  refine quadratic_bound (B := S.B) (R := S.Searched) (Q := Q) (V := S.treeNodes)
    (kids := S.kidsOf N q Q) ?_ ?_
  · refine ⟨hN, hQ.q_pos, hC.B_ge, ?_, ?_, kidsOf_length hC hQ Q, fun x hR => sum_nodes_le_pow hC hQ hR, hbase⟩
    · intro m hm T hT hx
      exact hwalk m hm T hT fun x hR hxm => by
        rw [treeSqOf_eq]
        exact hx x hR hxm
    · intro v c hc
      have := List.eq_of_mem_replicate hc
      rw [this]
      exact stepOf_sq_le hC hQ Q v
  · have : (0 : ℝ) ≤ ((6 * q + 1 : ℕ) : ℝ) * log N := by positivity
    linarith

/-- The base run fits its budget. This uses (M3). -/
theorem base_fits (hpeb : Pebbling G η d) (hη : η n = ηn) {x : I} {m : ℝ}
    (hx : log (S.B x) ≤ m) : G.pebble n (S.runTime x) ≤ S.baseBudget ηn d m := by
  have hτ1 := one_le_runTime hC x
  have h1 := hpeb n _ hτ1
  rw [hη] at h1
  have h2 := runTime_le hC x
  have hBx : S.B x ≤ exp m := by
    rw [← Real.exp_log (B_pos hC x)]
    exact Real.exp_le_exp.mpr hx
  have hK : 0 ≤ S.K := by linarith [hQ.K_ge]
  have hC0 : 0 ≤ S.loc + S.r * S.ρ := by
    have := hC.loc_ge
    have := hC.ρ_nonneg
    have hr : (0 : ℝ) ≤ (S.r : ℝ) := Nat.cast_nonneg _
    positivity
  have h3 : S.runTime x ≤ S.runBound m := by
    refine h2.trans ?_
    unfold Setting.runBound
    calc (S.loc + S.r * S.ρ) * (S.K * S.B x) ≤ (S.loc + S.r * S.ρ) * (S.K * exp m) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hBx hK) hC0
      _ = _ := by ring
  have hτ0 : 0 ≤ S.runTime x := by linarith
  have h4 : S.runTime x ^ ((1585 : ℝ) / 1000) ≤ S.runBound m ^ ((1585 : ℝ) / 1000) :=
    Real.rpow_le_rpow hτ0 h3 (by norm_num)
  have hl0 : 0 ≤ log (S.runTime x) := Real.log_nonneg hτ1
  have h5 : log (S.runTime x) ≤ log (S.runBound m) := Real.log_le_log (by linarith) h3
  have h6 : (1 + log (S.runTime x)) ^ d ≤ (1 + log (S.runBound m)) ^ d :=
    pow_le_pow_left₀ (by linarith) (by linarith) d
  have hη0 := hQ.η_nonneg
  have h7 : 0 ≤ S.runTime x ^ ((1585 : ℝ) / 1000) := Real.rpow_nonneg hτ0 _
  have h8 : 0 ≤ (1 + log (S.runTime x)) ^ d := by positivity
  have h9 : 0 ≤ S.runBound m ^ ((1585 : ℝ) / 1000) := Real.rpow_nonneg (by linarith) _
  refine h1.trans ?_
  unfold Setting.baseBudget
  exact mul_le_mul (mul_le_mul_of_nonneg_left h4 hη0) h6 h8 (mul_nonneg hη0 h9)

/-- **The search is valid.** For `log (B x) ≤ m`, with `x` the root or a target of a value call. Below the threshold, the classical run fits its
budget. Above it, the sum of the squared step counts is at most the parameter of the walk, the walk
accepts according to the answer, and the value calls are instances of the search at a level lower by
at least `log N`. -/
theorem search_valid (hwalk : WalkBound G κ) (hκ : κ n = κn) (hpeb : Pebbling G η d)
    (hη : η n = ηn) {x : I} {m : ℝ} (hR : S.Searched x) (hx : log (S.B x) ≤ m) :
    (m ≤ (W q : ℝ) * log N → G.pebble n (S.runTime x) ≤ S.levelTime G n N q ηn d m) ∧
    ((W q : ℝ) * log N < m →
      S.treeSq G n N q ηn d x ≤ tPrime N q m ∧
      (S.proc.answer x = true → (S.proc.orTree x).HasMarked ∧
        1 / 2 ≤ G.walkAccept n (S.treeSq G n N q ηn d x) (tPrime N q m) ((S.D : ℝ) + 1) true) ∧
      (S.proc.answer x = false → ¬ (S.proc.orTree x).HasMarked ∧
        G.walkAccept n (S.treeSq G n N q ηn d x) (tPrime N q m) ((S.D : ℝ) + 1) false ≤ 1 / 4) ∧
      (∀ v ∈ S.treeNodes x, ∀ y ∈ S.proc.calls v,
        log (S.B y) ≤ padLevel N q (S.B v) ∧ padLevel N q (S.B v) ≤ m - log N)) := by
  have hN := hQ.N_ge
  have hl := log_N_pos hN
  refine ⟨fun hm => ?_, fun hm => ?_⟩
  · unfold Setting.levelTime
    rw [ite_eq_left hm]
    exact base_fits hC hQ hpeb hη hx
  · have hle := treeSq_le hC hQ (ηn := ηn) (n := n) hwalk hκ hR hx
    have hT0 : 0 ≤ S.treeSq G n N q ηn d x := by
      unfold Setting.treeSq Setting.treeSqOf
      refine list_map_sum_nonneg fun v _ => ?_
      positivity
    have hm0 : 0 < m := lt_of_le_of_lt (by positivity) hm
    have hT1 : 1 ≤ tPrime N q m := by
      unfold tPrime
      have h1 := one_le_coef (q := q) hN
      have h2 := Real.one_le_exp hm0.le
      nlinarith
    have hD1 : (1 : ℝ) ≤ (S.D : ℝ) + 1 := by
      have : (0 : ℝ) ≤ (S.D : ℝ) := Nat.cast_nonneg _
      linarith
    obtain ⟨_, ha1, ha2⟩ := hwalk n _ _ _ hT0 hle hT1 hD1
    refine ⟨hle, fun ha => ⟨(S.proc.answer_iff_marked x).mp ha, ha1⟩, fun ha => ⟨?_, ha2⟩,
      fun v hv y hy => ⟨call_level hC hQ hy, level_drop hC hQ hR hx hm hv⟩⟩
    intro hmarked
    have := (S.proc.answer_iff_marked x).mpr hmarked
    rw [ha] at this
    exact Bool.noConfusion this

/-- The square of the time of the search at level `m ≥ 0` is at most `N ^ A q * exp m`. -/
theorem levelTime_sq_le (hwalk : WalkBound G κ) (hκ : κ n = κn) {m : ℝ} (hm : 0 ≤ m) :
    S.levelTime G n N q ηn d m ^ 2 ≤ N ^ A q * exp m := by
  have hN := hQ.N_ge
  have hN0 := N_pos hN
  by_cases hc : m ≤ (W q : ℝ) * log N
  · have h1 := levelTime_sq_base hC hQ (G := G) (n := n) (ηn := ηn) hm hc
    have h2 : N ^ (q + 4 * W q) ≤ N ^ A q := pow_mono_N hN (by simp only [A]; omega)
    have h3 := Real.one_le_exp hm
    have h4 : 0 < N ^ A q := pow_pos hN0 _
    nlinarith
  · exact levelTime_sq_step hQ hwalk hκ (not_le.mp hc)

/-- **The time bound.** The time of the search on `x`, at its own level, is at most
`N ^ (A q / 2) * √(B x)`. -/
theorem time_bound (hwalk : WalkBound G κ) (hκ : κ n = κn) (x : I) :
    S.levelTime G n N q ηn d (log (S.B x)) ≤ N ^ ((A q : ℝ) / 2) * √(S.B x) :=
  time_of_sq hQ.N_ge (B_pos hC x) (levelTime_sq_le hC hQ hwalk hκ (log_B_pos hC x).le)

end Valid

end Setting

section Family

theorem IsPoly.const (a : ℝ) : IsPoly fun _ => a := ⟨|a|, 0, abs_nonneg _, by simp⟩

theorem IsPoly.add {f g : ℕ → ℝ} (hf : IsPoly f) (hg : IsPoly g) : IsPoly fun n => f n + g n := by
  obtain ⟨C, k, hC, h⟩ := hf
  obtain ⟨D, l, hD, h'⟩ := hg
  refine ⟨C + D, k + l, by positivity, fun n => ?_⟩
  have hn : (1 : ℝ) ≤ (n : ℝ) + 1 := by
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg _
    linarith
  have h1 : ((n : ℝ) + 1) ^ k ≤ ((n : ℝ) + 1) ^ (k + l) := pow_le_pow_right₀ hn (by omega)
  have h2 : ((n : ℝ) + 1) ^ l ≤ ((n : ℝ) + 1) ^ (k + l) := pow_le_pow_right₀ hn (by omega)
  calc |f n + g n| ≤ |f n| + |g n| := abs_add_le _ _
    _ ≤ C * ((n : ℝ) + 1) ^ k + D * ((n : ℝ) + 1) ^ l := add_le_add (h n) (h' n)
    _ ≤ C * ((n : ℝ) + 1) ^ (k + l) + D * ((n : ℝ) + 1) ^ (k + l) :=
        add_le_add (mul_le_mul_of_nonneg_left h1 hC) (mul_le_mul_of_nonneg_left h2 hD)
    _ = _ := by ring

theorem IsPoly.mul {f g : ℕ → ℝ} (hf : IsPoly f) (hg : IsPoly g) : IsPoly fun n => f n * g n := by
  obtain ⟨C, k, hC, h⟩ := hf
  obtain ⟨D, l, hD, h'⟩ := hg
  refine ⟨C * D, k + l, by positivity, fun n => ?_⟩
  rw [abs_mul, pow_add]
  have hn : (0 : ℝ) ≤ ((n : ℝ) + 1) ^ l := by positivity
  calc |f n| * |g n| ≤ (C * ((n : ℝ) + 1) ^ k) * (D * ((n : ℝ) + 1) ^ l) :=
        mul_le_mul (h n) (h' n) (abs_nonneg _) (by positivity)
    _ = _ := by ring

theorem IsPoly.pow {f : ℕ → ℝ} (hf : IsPoly f) (m : ℕ) : IsPoly fun n => f n ^ m := by
  induction m with
  | zero => simpa using IsPoly.const 1
  | succ m ih =>
    simpa [pow_succ] using ih.mul hf

theorem IsPoly.id_pow (C : ℕ) : IsPoly fun n => (n : ℝ) ^ C := by
  refine ⟨1, C, zero_le_one, fun n => ?_⟩
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  rw [abs_of_nonneg (by positivity), one_mul]
  exact pow_le_pow_left₀ hn (by linarith) C

/-- A polynomial is at most a power of `n`, for `n ≥ 4`, with an exponent that does not depend on `n`. -/
theorem IsPoly.exists_pow {f : ℕ → ℝ} (hf : IsPoly f) :
    ∃ q : ℕ, ∀ n : ℕ, 4 ≤ n → f n ≤ (n : ℝ) ^ q := by
  obtain ⟨C, k, hC, h⟩ := hf
  obtain ⟨j, hj⟩ := pow_unbounded_of_one_lt C (by norm_num : (1 : ℝ) < 4)
  refine ⟨j + 2 * k, fun n hn => ?_⟩
  have hn4 : (4 : ℝ) ≤ n := by exact_mod_cast hn
  have h1 : C ≤ (n : ℝ) ^ j := hj.le.trans (pow_le_pow_left₀ (by norm_num) hn4 j)
  have h2 : (n : ℝ) + 1 ≤ (n : ℝ) ^ 2 := by nlinarith
  have h3 : ((n : ℝ) + 1) ^ k ≤ (n : ℝ) ^ (2 * k) := by
    rw [pow_mul]
    exact pow_le_pow_left₀ (by linarith) h2 k
  calc f n ≤ |f n| := le_abs_self _
    _ ≤ C * ((n : ℝ) + 1) ^ k := h n
    _ ≤ (n : ℝ) ^ j * (n : ℝ) ^ (2 * k) :=
        mul_le_mul h1 h3 (by positivity) (by positivity)
    _ = _ := by rw [pow_add]

variable {I : ℕ → Type*}

/-- The polynomial that dominates the constants of a family, without the logarithm of pebbling. -/
noncomputable def overhead (S : ∀ n, Setting (I n)) (κ η : ℕ → ℝ) (n : ℕ) : ℝ :=
  ((((S n).D : ℝ) + 1) * (S n).K) + (((S n).t : ℝ) + 1) + 12 * ((S n).s : ℝ) ^ 2 +
    (((S n).r : ℝ) * κ n) ^ 2 * (((S n).D : ℝ) + 1) + 12 * (S n).loc ^ 2 +
    12 * (((S n).r : ℝ) * (S n).ρ) ^ 2 + ((S n).loc + (S n).r * (S n).ρ) * (S n).K + η n ^ 2

/-- The logarithm of pebbling, against a power of `n` whose exponent does not depend on `a`. -/
theorem log_factor_le {n : ℕ} {a : ℝ} (d : ℕ) (ha : 0 ≤ a) (hn : (1 + a) ^ (2 * d) ≤ n) (hn1 : 1 ≤ n) :
    (1 + a * log (n : ℝ)) ^ (2 * d) ≤ (n : ℝ) ^ (2 * d + 1) := by
  have hn1' : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hlog : log (n : ℝ) ≤ n := Real.log_le_self (by linarith)
  have hlog0 : 0 ≤ log (n : ℝ) := Real.log_nonneg hn1'
  have h1 : 1 + a * log (n : ℝ) ≤ (1 + a) * n := by nlinarith
  have h2 : 0 ≤ 1 + a * log (n : ℝ) := by positivity
  calc (1 + a * log (n : ℝ)) ^ (2 * d) ≤ ((1 + a) * n) ^ (2 * d) := pow_le_pow_left₀ h2 h1 _
    _ = (1 + a) ^ (2 * d) * (n : ℝ) ^ (2 * d) := by rw [mul_pow]
    _ ≤ (n : ℝ) * (n : ℝ) ^ (2 * d) := mul_le_mul_of_nonneg_right hn (by positivity)
    _ = _ := by rw [pow_succ]; ring

/-- **Theorem 1, for the time.** Let a family of settings have polynomial constants, with `K = n ^ C`
and `c = C * log n`, and satisfy the conditions. Then there is a `q` that does not depend on `n`, and
`N₀`, such that for `n ≥ N₀` the constants are dominated by `n ^ q`, the time is at most
`n ^ (A q / 2) * √(B x)` for all `x`, and the base run and the walk at every level fit the budgets.
The exponent `q` comes from the polynomials and from the degree `d` alone. Only `N₀` depends on `W q`. -/
theorem theorem1 (S : ∀ n, Setting (I n)) (hC : ∀ n, (S n).Conditions) (C : ℕ)
    (hK : ∀ n, (S n).K = (n : ℝ) ^ C) (hc : ∀ n, (S n).c = C * log n)
    (hD : IsPoly fun n => ((S n).D : ℝ)) (ht : IsPoly fun n => ((S n).t : ℝ))
    (hs : IsPoly fun n => ((S n).s : ℝ)) (hr : IsPoly fun n => ((S n).r : ℝ))
    (hρ : IsPoly fun n => (S n).ρ) (hloc : IsPoly fun n => (S n).loc)
    {G : Primitives} {κ η : ℕ → ℝ} {d : ℕ} (hκ : IsPoly κ) (hη : IsPoly η) (hη0 : ∀ n, 0 ≤ η n)
    (hwalk : WalkBound G κ) (hpeb : Pebbling G η d) :
    ∃ (q N₀ : ℕ), 1 ≤ q ∧ ∀ n : ℕ, N₀ ≤ n →
      (S n).QBound (n : ℝ) q (κ n) (η n) d ∧
      (∀ x : I n,
        (S n).levelTime G n (n : ℝ) q (η n) d (log ((S n).B x)) ≤
          (n : ℝ) ^ ((A q : ℝ) / 2) * √((S n).B x)) ∧
      (∀ (x : I n) (m : ℝ), log ((S n).B x) ≤ m →
        (m ≤ (W q : ℝ) * log (n : ℝ) →
          G.pebble n ((S n).runTime x) ≤ (S n).levelTime G n (n : ℝ) q (η n) d m) ∧
        ((S n).Searched x → (S n).treeSq G n (n : ℝ) q (η n) d x ≤ Setting.tPrime (n : ℝ) q m)) := by
  have hKp : IsPoly fun n => (S n).K := by simpa [hK] using IsPoly.id_pow C
  have hFp : IsPoly (overhead S κ η) := by
    unfold overhead
    have h1 := IsPoly.const (1 : ℝ)
    have hrl := hr.mul hρ
    exact ((((((((hD.add h1).mul hKp).add (ht.add h1)).add ((IsPoly.const 12).mul (hs.pow 2))).add
      (((hr.mul hκ).pow 2).mul (hD.add h1))).add ((IsPoly.const 12).mul (hloc.pow 2))).add
      ((IsPoly.const 12).mul (hrl.pow 2))).add ((hloc.add hrl).mul hKp)).add (hη.pow 2)
  obtain ⟨q₀, hq₀⟩ := hFp.exists_pow
  set q := q₀ + C + 2 * d + 2 with hq
  obtain ⟨M, hM⟩ := exists_nat_ge ((1 + ((q + W q : ℕ) : ℝ)) ^ (2 * d))
  refine ⟨q, max 4 M, by omega, fun n hn => ?_⟩
  have hn4' : 4 ≤ n := le_trans (le_max_left _ _) hn
  have hnM : (M : ℝ) ≤ n := by exact_mod_cast le_trans (le_max_right _ _) hn
  have hn4 : (4 : ℝ) ≤ n := by exact_mod_cast hn4'
  have hF := hq₀ n hn4'
  have hle : (n : ℝ) ^ q₀ ≤ (n : ℝ) ^ q := pow_mono_N hn4 (by omega)
  have hle2 : (n : ℝ) ^ q₀ ≤ (n : ℝ) ^ (2 * q) := pow_mono_N hn4 (by omega)
  have hK1 : 1 ≤ (S n).K := by
    rw [hK]
    exact one_le_pow₀ (by linarith)
  have hK0 : 0 ≤ (S n).K := by linarith
  have hρ0 := (hC n).ρ_nonneg
  have hloc1 := (hC n).loc_ge
  have hrn : (0 : ℝ) ≤ ((S n).r : ℝ) := Nat.cast_nonneg _
  have hDn : (0 : ℝ) ≤ ((S n).D : ℝ) := Nat.cast_nonneg _
  have htn : (0 : ℝ) ≤ ((S n).t : ℝ) := Nat.cast_nonneg _
  have hsn : (0 : ℝ) ≤ ((S n).s : ℝ) := Nat.cast_nonneg _
  have ha1 : 0 ≤ (((S n).D : ℝ) + 1) * (S n).K := by positivity
  have ha2 : 0 ≤ ((S n).t : ℝ) + 1 := by positivity
  have ha3 : 0 ≤ 12 * ((S n).s : ℝ) ^ 2 := by positivity
  have ha4 : 0 ≤ (((S n).r : ℝ) * κ n) ^ 2 * (((S n).D : ℝ) + 1) := by positivity
  have ha5 : 0 ≤ 12 * (S n).loc ^ 2 := by positivity
  have ha6 : 0 ≤ 12 * (((S n).r : ℝ) * (S n).ρ) ^ 2 := by positivity
  have ha7 : 0 ≤ ((S n).loc + (S n).r * (S n).ρ) * (S n).K := by positivity
  have ha8 : 0 ≤ η n ^ 2 := by positivity
  unfold overhead at hF
  have hlogf := log_factor_le (n := n) (a := ((q + W q : ℕ) : ℝ)) d (Nat.cast_nonneg _)
    (hM.trans hnM) (by omega)
  have hbase : η n ^ 2 * (1 + ((q + W q : ℕ) : ℝ) * log (n : ℝ)) ^ (2 * d) ≤ (n : ℝ) ^ q := by
    have h1 : η n ^ 2 ≤ (n : ℝ) ^ q₀ := by linarith
    have hnpos : (0 : ℝ) < n := by linarith
    calc η n ^ 2 * (1 + ((q + W q : ℕ) : ℝ) * log (n : ℝ)) ^ (2 * d)
        ≤ (n : ℝ) ^ q₀ * (n : ℝ) ^ (2 * d + 1) :=
          mul_le_mul h1 hlogf (by
            have : 0 ≤ log (n : ℝ) := (log_N_pos hn4).le
            positivity) (by positivity)
      _ = (n : ℝ) ^ (q₀ + (2 * d + 1)) := (pow_add _ _ _).symm
      _ ≤ (n : ℝ) ^ q := pow_mono_N hn4 (by omega)
  have hQ : (S n).QBound (n : ℝ) q (κ n) (η n) d := by
    refine ⟨hn4, by omega, hK1, hη0 n, ?_, by linarith, by linarith, by linarith, by linarith,
      by linarith, by linarith, by linarith, hbase⟩
    rw [hc]
    have hl : 0 ≤ log (n : ℝ) := (log_N_pos hn4).le
    have : (C : ℝ) ≤ (q : ℝ) := by exact_mod_cast (by omega : C ≤ q)
    exact mul_le_mul_of_nonneg_right this hl
  refine ⟨hQ, fun x => Setting.time_bound (hC n) hQ hwalk rfl x, fun x m hx => ⟨fun hm => ?_,
    fun hR => Setting.treeSq_le (hC n) hQ hwalk rfl hR hx⟩⟩
  unfold Setting.levelTime
  rw [ite_eq_left hm]
  exact Setting.base_fits (hC n) hQ hpeb rfl hx

end Family

section Space

/-- **The levels of the space recursion.** If `S m ≤ S ((3/4) * m + c) + P` above `m0`, and `S m ≤ S0`
up to `m0`, then after a natural number `ℓ` of levels that brings `m` down to `m0`, `S m ≤ S0 + ℓ * P`. -/
theorem qubits_levels {Sp : ℝ → ℝ} {c m0 S0 P : ℝ} (hP : 0 ≤ P)
    (hrec : ∀ m, m0 < m → Sp m ≤ Sp ((3 / 4) * m + c) + P)
    (hbase : ∀ m, m ≤ m0 → Sp m ≤ S0) (ℓ : ℕ) :
    ∀ m, (3 / 4 : ℝ) ^ ℓ * (m - 4 * c) ≤ m0 - 4 * c → Sp m ≤ S0 + ℓ * P := by
  induction ℓ with
  | zero =>
    intro m hm
    have : m ≤ m0 := by simpa using hm
    simpa using hbase m this
  | succ ℓ ih =>
    intro m hm
    by_cases hc : m ≤ m0
    · have := hbase m hc
      push_cast
      nlinarith
    · have h1 := hrec m (not_le.mp hc)
      have h2 := ih ((3 / 4) * m + c) (by
        have heq : (3 / 4 : ℝ) ^ ℓ * ((3 / 4) * m + c - 4 * c) =
            (3 / 4 : ℝ) ^ (ℓ + 1) * (m - 4 * c) := by
          rw [pow_succ]
          ring
        rw [heq]
        exact hm)
      push_cast
      linarith

/-- **The space is polynomial.** With `m0 ≥ 4 * c + 1`, the number of levels up to `m ≤ L` is at most
`3 * clog₂ L`, so `S m ≤ S0 + 3 * clog₂ L * P`. -/
theorem qubits_polynomial {Sp : ℝ → ℝ} {c m0 S0 P : ℝ} (hP : 0 ≤ P) (hc : 0 ≤ c)
    (hm0 : 4 * c + 1 ≤ m0)
    (hrec : ∀ m, m0 < m → Sp m ≤ Sp ((3 / 4) * m + c) + P)
    (hbase : ∀ m, m ≤ m0 → Sp m ≤ S0) (L : ℕ) {m : ℝ} (hm : m ≤ L) :
    Sp m ≤ S0 + ((3 * Nat.clog 2 L : ℕ) : ℝ) * P := by
  refine qubits_levels hP hrec hbase (3 * Nat.clog 2 L) m ?_
  set j := Nat.clog 2 L with hj
  have hL : (L : ℝ) ≤ (2 : ℝ) ^ j := by exact_mod_cast Nat.le_pow_clog (by norm_num) L
  have hdec : (3 / 4 : ℝ) ^ (3 * j) ≤ (1 / 2) ^ j := by
    rw [pow_mul]
    exact pow_le_pow_left₀ (by norm_num) (by norm_num) j
  have hpos : (0 : ℝ) < (3 / 4 : ℝ) ^ (3 * j) := by positivity
  have h1 : m - 4 * c ≤ (2 : ℝ) ^ j := by linarith
  have h2 : (1 / 2 : ℝ) ^ j * (2 : ℝ) ^ j = 1 := by
    rw [← mul_pow]
    norm_num
  by_cases hs : m - 4 * c ≤ 0
  · have : (3 / 4 : ℝ) ^ (3 * j) * (m - 4 * c) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hpos.le hs
    linarith
  · push Not at hs
    have h3 : (3 / 4 : ℝ) ^ (3 * j) * (m - 4 * c) ≤ (1 / 2 : ℝ) ^ j * (2 : ℝ) ^ j :=
      mul_le_mul hdec h1 hs.le (by positivity)
    linarith

/-- The threshold of the base dominates the fixed point of the recursion on the levels. The level of
a value call at a node of an instance at level `m` is at most `(3/4) * m + 2 * q * log N`. -/
theorem threshold_above_fixed_point {N : ℝ} {q : ℕ} (hN : 4 ≤ N) :
    4 * (2 * (q : ℝ) * log N) + 1 ≤ (W q : ℝ) * log N := by
  have hl : 1 ≤ log N := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    linarith [Real.exp_one_lt_three]
  have hW : (W q : ℝ) = 22 * q + 3 := by simp only [W]; push_cast; ring
  rw [hW]
  have hq : (0 : ℝ) ≤ q * log N := by positivity
  nlinarith

/-- The recursion on the levels follows from (M1): `m_v ≤ (3/4) * m + 2 * q * log N`. -/
theorem padLevel_le_recursion {N : ℝ} {q : ℕ} (hN : 4 ≤ N) {m b : ℝ}
    (hv : log b ≤ m + q * log N) : padLevel N q b ≤ (3 / 4) * m + 2 * q * log N := by
  have hl := log_N_pos hN
  have hq : (0 : ℝ) ≤ q * log N := by positivity
  unfold padLevel
  nlinarith

end Space

section Errors

variable {G : Primitives}

/-- `r ≥ 32 * (4 * L + n)` rounds of error reduction reach the error `exp (-4 * L - n)`. -/
theorem reduction_error (hG : ErrorReduction G) {n r : ℕ} {L : ℝ}
    (hr : 32 * (4 * L + n) ≤ r) : G.boostError n r ≤ exp (-4 * L - n) := by
  refine (hG n r).1.trans (Real.exp_le_exp.mpr ?_)
  linarith

/-- The amplitude distance of a state with error probability `err` from the exact one, in the plane:
`√(2 - 2 * √(1 - err)) ≤ √(2 * err)`. -/
theorem amplitude_distance {err : ℝ} (h0 : 0 ≤ err) (h1 : err ≤ 1) :
    √(2 - 2 * √(1 - err)) ≤ √(2 * err) := by
  apply Real.sqrt_le_sqrt
  have h2 : 1 - err ≤ √(1 - err) := by
    apply Real.le_sqrt_of_sq_le
    nlinarith
  linarith

/-- **The sum of the amplitude errors.** With error `exp (-4 * L - n)` in each step, and at most
`exp L * u` uses, the sum of the amplitude errors is at most `√2 * u * exp (-L - n / 2)`. -/
theorem amplitude_budget (hG : AmplitudeError G) {n : ℕ} {L U u err : ℝ} (hU0 : 0 ≤ U)
    (herr0 : 0 ≤ err) (herr : err ≤ exp (-4 * L - n)) (hU : U ≤ exp L * u) :
    U * G.stepDefect n err ≤ √2 * u * exp (-L - (n : ℝ) / 2) := by
  have h1 := hG n err herr0
  have hs : √err ≤ exp (-2 * L - (n : ℝ) / 2) := by
    refine (Real.sqrt_le_sqrt herr).trans ?_
    rw [Real.sqrt_le_left (Real.exp_pos _).le, ← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    push_cast
    linarith
  have h2 : G.stepDefect n err ≤ √2 * exp (-2 * L - (n : ℝ) / 2) := by
    refine h1.trans ?_
    rw [Real.sqrt_mul (by norm_num)]
    exact mul_le_mul_of_nonneg_left hs (Real.sqrt_nonneg _)
  have hexp : exp L * exp (-2 * L - (n : ℝ) / 2) = exp (-L - (n : ℝ) / 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hE : 0 ≤ √2 * exp (-2 * L - (n : ℝ) / 2) := by positivity
  calc U * G.stepDefect n err ≤ U * (√2 * exp (-2 * L - (n : ℝ) / 2)) :=
        mul_le_mul_of_nonneg_left h2 hU0
    _ ≤ (exp L * u) * (√2 * exp (-2 * L - (n : ℝ) / 2)) := mul_le_mul_of_nonneg_right hU hE
    _ = √2 * u * (exp L * exp (-2 * L - (n : ℝ) / 2)) := by ring
    _ = _ := by rw [hexp]

end Errors

end QuantumBranching
