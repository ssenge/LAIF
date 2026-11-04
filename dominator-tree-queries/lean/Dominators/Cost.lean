import Dominators.DFS

/-!
# Cost

The charge of a search with `N` entries and `t ≥ 1` solutions is `√(N/t)`, and with no solution `√N`. This is
the bound of `BBHT` up to its constant. The sums here are of charges, and a charge is a real number.

Lemma 1 is Theorem 12 of quant-ph/0401091, with the same stack and the same sum.

* `expected_search_sum`: the sum `Σ_k √(N/(c - k + 1)) ≤ 2 √(c N)` in Lemma 1.
* `lemma1_cauchy`, `lemma1_array`, `lemma1_matrix`: the inner product step of Lemma 1.
* `dfs_charge_array`, `dfs_charge_matrix`: the actual charge of the executable search from one root.
* `sum_sqrt_inDeg_le`: `Σ_w √(deg⁻ w) ≤ √(n m)`.
* `partition_sum_le`, `partition_matrix_sum`: the sums over components in Theorem 3.
* `union_error_le`: error `1/(c n)` per call over `O(n)` calls.
* `dominator_charge_total`: the search and minimum-finding charges of Theorem 2 together.
* `bbht_budget`, `durrHoyer_total`: what the named hypotheses `BBHT` and `DurrHoyer` give.

That the charges add up to the query count of one quantum algorithm is not proved. That would need the composition
of quantum subroutines under classical control, with deferred measurement, and it is not formalized.
-/

open Finset

namespace Dominators

universe u

/-! ## The expected-search sum -/

theorem sum_inv_sqrt_le (c : ℕ) : ∑ j ∈ range c, (Real.sqrt ((j : ℝ) + 1))⁻¹ ≤ 2 * Real.sqrt c := by
  induction c with
  | zero => simp
  | succ c ih =>
    rw [Finset.sum_range_succ]
    have ha := Real.sqrt_nonneg (c : ℝ)
    have hb : 0 < Real.sqrt ((c : ℝ) + 1) := Real.sqrt_pos.mpr (by positivity)
    have ha2 : Real.sqrt (c : ℝ) ^ 2 = c := Real.sq_sqrt (by positivity)
    have hb2 : Real.sqrt ((c : ℝ) + 1) ^ 2 = (c : ℝ) + 1 := Real.sq_sqrt (by positivity)
    have hkey : (Real.sqrt ((c : ℝ) + 1))⁻¹ ≤ 2 * (Real.sqrt ((c : ℝ) + 1) - Real.sqrt c) := by
      rw [inv_le_iff_one_le_mul₀ hb]
      nlinarith [sq_nonneg (Real.sqrt ((c : ℝ) + 1) - Real.sqrt c)]
    push_cast
    linarith

/-- The sum in Lemma 1, for the successful searches at a vertex with `c` tree children and `N` entries. The
`k`-th search, `k = 0, …, c - 1`, has at least `c - k` solutions. -/
theorem expected_search_sum (N : ℝ) (hN : 0 ≤ N) (c : ℕ) :
    ∑ k ∈ range c, Real.sqrt (N / ((c - k : ℕ) : ℝ)) ≤ 2 * Real.sqrt (c * N) := by
  have hrefl : ∑ k ∈ range c, Real.sqrt (N / ((c - k : ℕ) : ℝ)) =
      ∑ j ∈ range c, Real.sqrt (N / ((j : ℝ) + 1)) := by
    rw [← Finset.sum_range_reflect]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hj' := Finset.mem_range.mp hj
    have : c - (c - 1 - j) = j + 1 := by omega
    rw [this]
    push_cast
    rfl
  rw [hrefl]
  have hterm : ∀ j : ℕ, Real.sqrt (N / ((j : ℝ) + 1)) = Real.sqrt N * (Real.sqrt ((j : ℝ) + 1))⁻¹ := by
    intro j
    rw [Real.sqrt_div hN, div_eq_mul_inv]
  simp only [hterm]
  rw [← Finset.mul_sum, Real.sqrt_mul (by positivity : (0 : ℝ) ≤ c) N]
  nlinarith [sum_inv_sqrt_le c, Real.sqrt_nonneg N, Real.sqrt_nonneg (c : ℝ),
    mul_le_mul_of_nonneg_left (sum_inv_sqrt_le c) (Real.sqrt_nonneg N)]

/-- The cost at one vertex: the successful searches and the final failed one. -/
theorem vertex_cost_le (N : ℝ) (hN : 0 ≤ N) (c : ℕ) :
    2 * Real.sqrt (c * N) + Real.sqrt N ≤ 3 * Real.sqrt (((c : ℝ) + 1) * N) := by
  have h1 : Real.sqrt (c * N) ≤ Real.sqrt (((c : ℝ) + 1) * N) :=
    Real.sqrt_le_sqrt (by nlinarith)
  have h2 : Real.sqrt N ≤ Real.sqrt (((c : ℝ) + 1) * N) :=
    Real.sqrt_le_sqrt (by nlinarith [Nat.cast_nonneg (α := ℝ) c])
  linarith

/-! ## The inner product inequality -/

/-- The inner product inequality in the form used throughout. -/
theorem sum_sqrt_mul_le {ι : Type*} (s : Finset ι) (f g : ι → ℝ) (hf : ∀ i, 0 ≤ f i) (hg : ∀ i, 0 ≤ g i) :
    ∑ i ∈ s, Real.sqrt (f i * g i) ≤ Real.sqrt ((∑ i ∈ s, f i) * ∑ i ∈ s, g i) := by
  apply Real.le_sqrt_of_sq_le
  have h := Finset.sum_mul_sq_le_sq_mul_sq s (fun i => Real.sqrt (f i)) (fun i => Real.sqrt (g i))
  simp only [Real.sq_sqrt (hf _), Real.sq_sqrt (hg _)] at h
  have he : ∑ i ∈ s, Real.sqrt (f i * g i) = ∑ i ∈ s, Real.sqrt (f i) * Real.sqrt (g i) :=
    Finset.sum_congr rfl fun i _ => Real.sqrt_mul (hf i) _
  rw [he]
  exact h

variable {V : Type u} [Fintype V]

/-- **The inner product step of Lemma 1.** With `Σ c_v ≤ n`: `Σ_v √((c_v + 1) N_v) ≤ √(2 n Σ N_v)`. -/
theorem lemma1_cauchy (c : V → ℕ) (N : V → ℝ) (hN : ∀ v, 0 ≤ N v) (hc : ∑ v, c v ≤ Fintype.card V) :
    ∑ v, Real.sqrt (((c v : ℝ) + 1) * N v) ≤ Real.sqrt (2 * Fintype.card V * ∑ v, N v) := by
  refine (sum_sqrt_mul_le univ (fun v => (c v : ℝ) + 1) N (fun _ => by positivity) hN).trans ?_
  apply Real.sqrt_le_sqrt
  apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun v _ => hN v)
  rw [Finset.sum_add_distrib]
  have h1 : ∑ v, (c v : ℝ) ≤ Fintype.card V := by exact_mod_cast hc
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  linarith

/-! ## Degrees -/

open Classical in
/-- The out-degree. -/
noncomputable def outDeg (E : V → V → Prop) (v : V) : ℕ := (univ.filter fun w => E v w).card

open Classical in
/-- The in-degree. -/
noncomputable def inDeg (E : V → V → Prop) (w : V) : ℕ := (univ.filter fun v => E v w).card

open Classical in
/-- The number of edges. -/
noncomputable def edgeCount (E : V → V → Prop) : ℕ := (univ.filter fun p : V × V => E p.1 p.2).card

open Classical in
theorem sum_outDeg (E : V → V → Prop) : ∑ v, outDeg E v = edgeCount E := by
  simp only [outDeg, edgeCount, Finset.card_filter]
  rw [← Finset.sum_product']
  rfl

open Classical in
theorem sum_inDeg (E : V → V → Prop) : ∑ w, inDeg E w = edgeCount E := by
  simp only [inDeg, edgeCount, Finset.card_filter]
  rw [Finset.sum_comm, ← Finset.sum_product']
  rfl

/-- **Lemma 1, array model.** `Σ_v √((c_v + 1) deg v) ≤ √(2 n m)`. -/
theorem lemma1_array (E : V → V → Prop) (c : V → ℕ) (hc : ∑ v, c v ≤ Fintype.card V) :
    ∑ v, Real.sqrt (((c v : ℝ) + 1) * outDeg E v) ≤ Real.sqrt (2 * Fintype.card V * edgeCount E) := by
  have h := lemma1_cauchy c (fun v => (outDeg E v : ℝ)) (fun _ => by positivity) hc
  have hs : ∑ v, (outDeg E v : ℝ) = edgeCount E := by exact_mod_cast sum_outDeg E
  rwa [hs] at h

/-- **Lemma 1, matrix model.** `Σ_v √((c_v + 1) n) ≤ √2 n^{3/2}`, written as `√(2 n · n²)`. -/
theorem lemma1_matrix (c : V → ℕ) (hc : ∑ v, c v ≤ Fintype.card V) :
    ∑ v, Real.sqrt (((c v : ℝ) + 1) * Fintype.card V) ≤
      Real.sqrt (2 * Fintype.card V * (Fintype.card V : ℝ) ^ 2) := by
  have h := lemma1_cauchy c (fun _ => (Fintype.card V : ℝ)) (fun _ => by positivity) hc
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at h
  rw [pow_two]
  exact h

/-- **Theorem 2's sum.** `Σ_w √(deg⁻ w) ≤ √(n m)`. -/
theorem sum_sqrt_inDeg_le (E : V → V → Prop) :
    ∑ w, Real.sqrt (inDeg E w) ≤ Real.sqrt (Fintype.card V * edgeCount E) := by
  have h := sum_sqrt_mul_le univ (fun _ : V => (1 : ℝ)) (fun w => (inDeg E w : ℝ)) (fun _ => by norm_num)
    (fun _ => by positivity)
  simp only [one_mul, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] at h
  have hs : ∑ w, (inDeg E w : ℝ) = edgeCount E := by exact_mod_cast sum_inDeg E
  rwa [hs] at h

/-! ## Sums over components (Theorem 3) -/

section Partition

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

open Classical in
/-- The number of vertices in class `C`. -/
noncomputable def classSize (cl : V → ι) (C : ι) : ℕ := (univ.filter fun x => cl x = C).card

open Classical in
/-- The number of edges inside class `C`. -/
noncomputable def classEdges (E : V → V → Prop) (cl : V → ι) (C : ι) : ℕ :=
  (univ.filter fun p : V × V => E p.1 p.2 ∧ cl p.1 = C ∧ cl p.2 = C).card

open Classical in
theorem sum_classSize (cl : V → ι) : ∑ C, classSize cl C = Fintype.card V := by
  simp only [classSize]
  rw [← Finset.card_eq_sum_card_fiberwise (fun x _ => Finset.mem_coe.mpr (Finset.mem_univ (cl x)))]
  rfl

open Classical in
theorem sum_classEdges_le (E : V → V → Prop) (cl : V → ι) : ∑ C, classEdges E cl C ≤ edgeCount E := by
  have h := Finset.card_eq_sum_card_fiberwise (s := univ.filter fun p : V × V => E p.1 p.2)
    (t := univ) (f := fun p => cl p.1) (fun x _ => Finset.mem_coe.mpr (Finset.mem_univ _))
  rw [edgeCount, h]
  refine Finset.sum_le_sum fun C _ => Finset.card_le_card ?_
  intro p hp
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
  exact ⟨hp.1, hp.2.1⟩

/-- **Theorem 3, array model.** `Σ_C √(n_C m_C) ≤ √(n m)`, for any partition of the vertices, and so for the
strongly connected components. -/
theorem partition_sum_le (E : V → V → Prop) (cl : V → ι) :
    ∑ C, Real.sqrt ((classSize cl C : ℝ) * classEdges E cl C) ≤ Real.sqrt (Fintype.card V * edgeCount E) := by
  refine (sum_sqrt_mul_le univ _ _ (fun _ => by positivity) (fun _ => by positivity)).trans ?_
  apply Real.sqrt_le_sqrt
  have h1 : ∑ C, (classSize cl C : ℝ) = Fintype.card V := by exact_mod_cast sum_classSize cl
  have h2 : ∑ C, (classEdges E cl C : ℝ) ≤ edgeCount E := by exact_mod_cast sum_classEdges_le E cl
  rw [h1]
  exact mul_le_mul_of_nonneg_left h2 (by positivity)

/-- **Theorem 3, matrix model.** `Σ_C n_C √n = n · √n`, which is `n^{3/2}`. -/
theorem partition_matrix_sum (cl : V → ι) :
    ∑ C, (classSize cl C : ℝ) * Real.sqrt (Fintype.card V) =
      (Fintype.card V : ℝ) * Real.sqrt (Fintype.card V) := by
  rw [← Finset.sum_mul]
  have h1 : ∑ C, (classSize cl C : ℝ) = Fintype.card V := by exact_mod_cast sum_classSize cl
  rw [h1]

end Partition

/-- The error budget: `K ≤ a n` calls at error `1/(c n)` each have total error at most `a / c`. So for `c ≥ 3 a`
the total is at most `1/3`. -/
theorem union_error_le {K a c n : ℝ} (hK : K ≤ a * n) (hc : 0 < c) (hn : 0 < n) : K * (1 / (c * n)) ≤ a / c := by
  have hpos : 0 < c * n := mul_pos hc hn
  calc K * (1 / (c * n)) ≤ a * n * (1 / (c * n)) := by
        exact mul_le_mul_of_nonneg_right hK (by positivity)
    _ = a / c := by field_simp

/-! ## The charge of the executable search -/

section Charge

variable [DecidableEq V] {E : V → V → Prop}

open Classical in
/-- The unvisited out-neighbours. -/
noncomputable def unvisitedNbrs (E : V → V → Prop) (v : V) (S : Finset V) : Finset V :=
  univ.filter fun w => E v w ∧ w ∉ S

/-- The charge of a search at `v` with `N v` entries: `√(N/t)` with `t` solutions, and `√N` with none. -/
noncomputable def charge (E : V → V → Prop) (N : V → ℝ) (v : V) (S : Finset V) : ℝ :=
  if (unvisitedNbrs E v S).card = 0 then Real.sqrt (N v)
  else Real.sqrt (N v / ((unvisitedNbrs E v S).card : ℝ))

/-- The total charge of a run. -/
noncomputable def runCharge (E : V → V → Prop) (N : V → ℝ) (search : V → Finset V → Option V) :
    ℕ → St V → ℝ
  | 0, _ => 0
  | k + 1, s =>
    (match s.stack with
      | [] => 0
      | v :: _ => charge E N v s.visited) + runCharge E N search k (step search s)

/-- The tree children of `v` made during a run. -/
def kids (search : V → Finset V → Option V) (v : V) : ℕ → St V → Finset V
  | 0, _ => ∅
  | k + 1, s =>
    match s.stack with
    | [] => kids search v k (step search s)
    | u :: _ =>
      match search u s.visited with
      | some w => if u = v then insert w (kids search v k (step search s)) else kids search v k (step search s)
      | none => kids search v k (step search s)

/-- The number of times `v` is popped during a run. -/
def pops (search : V → Finset V → Option V) (v : V) : ℕ → St V → ℕ
  | 0, _ => 0
  | k + 1, s =>
    match s.stack with
    | [] => pops search v k (step search s)
    | u :: _ =>
      match search u s.visited with
      | some _ => pops search v k (step search s)
      | none => (if u = v then 1 else 0) + pops search v k (step search s)

section Equations

variable {search : V → Finset V → Option V} {v u w : V} {k : ℕ} {s : St V} {rest : List V}

omit [Fintype V] in
theorem kids_nil (hst : s.stack = []) : kids search v (k + 1) s = kids search v k (step search s) := by
  rw [kids]
  simp only [hst]

omit [Fintype V] in
theorem kids_none (hst : s.stack = u :: rest) (hq : search u s.visited = none) :
    kids search v (k + 1) s = kids search v k (step search s) := by
  rw [kids]
  simp only [hst, hq]

omit [Fintype V] in
theorem kids_found (hst : s.stack = u :: rest) (hq : search u s.visited = some w) :
    kids search v (k + 1) s =
      if u = v then insert w (kids search v k (step search s)) else kids search v k (step search s) := by
  rw [kids]
  simp only [hst, hq]

omit [Fintype V] in
theorem pops_nil (hst : s.stack = []) : pops search v (k + 1) s = pops search v k (step search s) := by
  rw [pops]
  simp only [hst]

omit [Fintype V] in
theorem pops_none (hst : s.stack = u :: rest) (hq : search u s.visited = none) :
    pops search v (k + 1) s = (if u = v then 1 else 0) + pops search v k (step search s) := by
  rw [pops]
  simp only [hst, hq]

omit [Fintype V] in
theorem pops_found (hst : s.stack = u :: rest) (hq : search u s.visited = some w) :
    pops search v (k + 1) s = pops search v k (step search s) := by
  rw [pops]
  simp only [hst, hq]

end Equations

/-- The children made during a run were unvisited out-neighbours when it began. -/
theorem kids_subset {search : V → Finset V → Option V} (hS : IsSearch E search) (v : V) (k : ℕ) (s : St V) :
    kids search v k s ⊆ unvisitedNbrs E v s.visited := by
  induction k generalizing s with
  | zero => simp [kids]
  | succ k ih =>
    have hsub : unvisitedNbrs E v (step search s).visited ⊆ unvisitedNbrs E v s.visited := by
      intro w hw
      simp only [unvisitedNbrs, Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
      exact ⟨hw.1, fun h => hw.2 (visited_step_subset s h)⟩
    cases hst : s.stack with
    | nil =>
      rw [kids_nil hst]
      exact (ih _).trans hsub
    | cons u rest =>
      cases hq : search u s.visited with
      | none =>
        rw [kids_none hst hq]
        exact (ih _).trans hsub
      | some w =>
        rw [kids_found hst hq]
        split_ifs with huv
        · subst huv
          intro t ht
          rcases Finset.mem_insert.mp ht with rfl | ht
          · obtain ⟨he, hw⟩ := hS.found hq
            simp only [unvisitedNbrs, Finset.mem_filter, Finset.mem_univ, true_and]
            exact ⟨he, hw⟩
          · exact hsub (ih _ ht)
        · exact (ih _).trans hsub

/-- A child found by a search is visited afterwards, so it is not made again. -/
theorem not_mem_kids_of_found {search : V → Finset V → Option V} (hS : IsSearch E search) {u w : V} {rest : List V}
    {s : St V} (hst : s.stack = u :: rest) (hq : search u s.visited = some w) (v : V) (k : ℕ) :
    w ∉ kids search v k (step search s) := by
  intro hw
  have h := kids_subset hS v k (step search s) hw
  simp only [unvisitedNbrs, Finset.mem_filter, Finset.mem_univ, true_and] at h
  apply h.2
  rw [step_found hst hq]
  simp [St.push]

/-- The partial sum of `1/√j`. -/
noncomputable def harm (c : ℕ) : ℝ := ∑ j ∈ range c, (Real.sqrt ((j : ℝ) + 1))⁻¹

/-- **The charge of a run**, as a sum over vertices of the charges of its successful and failed searches. -/
theorem runCharge_le {search : V → Finset V → Option V} (hS : IsSearch E search) (N : V → ℝ) (hN : ∀ v, 0 ≤ N v)
    (k : ℕ) (s : St V) :
    runCharge E N search k s ≤
      ∑ v, (Real.sqrt (N v) * harm (kids search v k s).card + Real.sqrt (N v) * pops search v k s) := by
  induction k generalizing s with
  | zero => simp [runCharge, kids, pops, harm]
  | succ k ih =>
    rw [runCharge]
    cases hst : s.stack with
    | nil =>
      simp only [zero_add, kids_nil hst, pops_nil hst]
      exact ih _
    | cons u rest =>
      simp only
      have hih := ih (step search s)
      cases hq : search u s.visited with
      | none =>
        -- a failed search: no solutions, charge `√N`
        have ht : (unvisitedNbrs E u s.visited).card = 0 := by
          rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
          intro w hw
          simp only [unvisitedNbrs, Finset.mem_filter, Finset.mem_univ, true_and] at hw
          exact hw.2 (hS.none hq w hw.1)
        have hc : charge E N u s.visited = Real.sqrt (N u) := by
          rw [charge, ite_eq_left ht]
        rw [hc]
        have hk : ∀ v, kids search v (k + 1) s = kids search v k (step search s) := fun v => kids_none hst hq
        have hp : ∀ v, pops search v (k + 1) s = (if u = v then 1 else 0) + pops search v k (step search s) :=
          fun v => pops_none hst hq
        simp only [hk, hp]
        have : ∑ v, (Real.sqrt (N v) * harm (kids search v k (step search s)).card +
              Real.sqrt (N v) * (((if u = v then 1 else 0) + pops search v k (step search s) : ℕ) : ℝ)) =
            Real.sqrt (N u) + ∑ v, (Real.sqrt (N v) * harm (kids search v k (step search s)).card +
              Real.sqrt (N v) * (pops search v k (step search s) : ℝ)) := by
          have hsplit : ∀ v, Real.sqrt (N v) * harm (kids search v k (step search s)).card +
              Real.sqrt (N v) * (((if u = v then 1 else 0) + pops search v k (step search s) : ℕ) : ℝ) =
              (if u = v then Real.sqrt (N v) else 0) +
              (Real.sqrt (N v) * harm (kids search v k (step search s)).card +
                Real.sqrt (N v) * (pops search v k (step search s) : ℝ)) := by
            intro v
            split_ifs <;> push_cast <;> ring
          simp only [hsplit]
          rw [Finset.sum_add_distrib, Finset.sum_ite_eq]
          simp
        rw [this]
        linarith
      | some w =>
        -- a successful search: at least as many solutions as children still to come
        obtain ⟨he, hw⟩ := hS.found hq
        have hnew := not_mem_kids_of_found hS hst hq
        have hk : ∀ v, kids search v (k + 1) s =
            if u = v then insert w (kids search v k (step search s)) else kids search v k (step search s) :=
          fun v => kids_found hst hq
        have hp : ∀ v, pops search v (k + 1) s = pops search v k (step search s) := fun v => pops_found hst hq
        have hcard : (kids search u (k + 1) s).card = (kids search u k (step search s)).card + 1 := by
          rw [hk u, ite_eq_left rfl, Finset.card_insert_of_notMem (hnew u k)]
        have hle : (kids search u (k + 1) s).card ≤ (unvisitedNbrs E u s.visited).card :=
          Finset.card_le_card (kids_subset hS u (k + 1) s)
        have hpos : 0 < (unvisitedNbrs E u s.visited).card := by omega
        have hc : charge E N u s.visited ≤
            Real.sqrt (N u) * (Real.sqrt (((kids search u k (step search s)).card : ℝ) + 1))⁻¹ := by
          have hne : (unvisitedNbrs E u s.visited).card ≠ 0 := by omega
          simp only [charge, hne, ite_false]
          rw [Real.sqrt_div (hN u), div_eq_mul_inv]
          apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
          apply inv_anti₀ (Real.sqrt_pos.mpr (Nat.cast_add_one_pos _))
          apply Real.sqrt_le_sqrt
          have : (((kids search u k (step search s)).card + 1 : ℕ) : ℝ) ≤ (unvisitedNbrs E u s.visited).card := by
            exact_mod_cast (by omega : (kids search u k (step search s)).card + 1 ≤ (unvisitedNbrs E u s.visited).card)
          push_cast at this
          exact this
        have hsum : ∑ v, (Real.sqrt (N v) * harm (kids search v (k + 1) s).card +
              Real.sqrt (N v) * (pops search v (k + 1) s : ℝ)) =
            Real.sqrt (N u) * (Real.sqrt (((kids search u k (step search s)).card : ℝ) + 1))⁻¹ +
              ∑ v, (Real.sqrt (N v) * harm (kids search v k (step search s)).card +
                Real.sqrt (N v) * (pops search v k (step search s) : ℝ)) := by
          have hsplit : ∀ v, Real.sqrt (N v) * harm (kids search v (k + 1) s).card +
              Real.sqrt (N v) * (pops search v (k + 1) s : ℝ) =
              (if u = v then Real.sqrt (N v) *
                (Real.sqrt (((kids search v k (step search s)).card : ℝ) + 1))⁻¹ else 0) +
              (Real.sqrt (N v) * harm (kids search v k (step search s)).card +
                Real.sqrt (N v) * (pops search v k (step search s) : ℝ)) := by
            intro v
            rw [hp v]
            by_cases huv : u = v
            · subst huv
              rw [hcard, ite_eq_left rfl, harm, Finset.sum_range_succ, ← harm]
              ring
            · rw [hk v, ite_eq_right huv, ite_eq_right huv]
              ring
          simp only [hsplit]
          rw [Finset.sum_add_distrib, Finset.sum_ite_eq]
          simp
        rw [hsum]
        linarith

omit [Fintype V] in
/-- In a run, a vertex is popped at most once, and not at all if already finished. -/
theorem pops_le {search : V → Finset V → Option V} (hS : IsSearch E search) (v : V) (k : ℕ) (s : St V)
    (hI : Inv E s) : pops search v k s ≤ 1 ∧ (v ∈ s.finished → pops search v k s = 0) := by
  induction k generalizing s with
  | zero => simp [pops]
  | succ k ih =>
    obtain ⟨h1, h2⟩ := ih (step search s) (hI.step hS)
    cases hst : s.stack with
    | nil =>
      rw [pops_nil hst]
      refine ⟨h1, fun hv => h2 ?_⟩
      rwa [step_nil hst]
    | cons u rest =>
      cases hq : search u s.visited with
      | some w =>
        rw [pops_found hst hq]
        refine ⟨h1, fun hv => h2 ?_⟩
        rw [step_found hst hq]
        exact hv
      | none =>
        rw [pops_none hst hq]
        have hfin : ∀ t, t ∈ (step search s).finished ↔ t = u ∨ t ∈ s.finished := by
          intro t
          rw [step_none hst hq]
          simp
        have hnd := hI.nodup
        rw [hst] at hnd
        by_cases huv : u = v
        · subst huv
          have h0 := h2 ((hfin u).mpr (Or.inl rfl))
          rw [ite_eq_left rfl, h0]
          refine ⟨by norm_num, fun hu => ?_⟩
          simp only [List.cons_append, List.nodup_cons, List.mem_append, not_or] at hnd
          exact absurd hu hnd.1.2
        · rw [ite_eq_right huv, zero_add]
          exact ⟨h1, fun hv => h2 ((hfin v).mpr (Or.inr hv))⟩

/-- The number of children in a run is limited by the unvisited vertices. -/
theorem sum_kids_le {search : V → Finset V → Option V} (hS : IsSearch E search) (k : ℕ) (s : St V) :
    ∑ v, (kids search v k s).card + s.visited.card ≤ Fintype.card V := by
  induction k generalizing s with
  | zero =>
    simp only [kids, Finset.card_empty, Finset.sum_const_zero, zero_add]
    exact Finset.card_le_univ _
  | succ k ih =>
    have hih := ih (step search s)
    cases hst : s.stack with
    | nil =>
      have hk : ∀ v, kids search v (k + 1) s = kids search v k (step search s) := fun v => kids_nil hst
      simp only [hk]
      rw [step_nil hst] at hih ⊢
      exact hih
    | cons u rest =>
      cases hq : search u s.visited with
      | none =>
        have hk : ∀ v, kids search v (k + 1) s = kids search v k (step search s) := fun v => kids_none hst hq
        simp only [hk]
        have : (step search s).visited = s.visited := by
          rw [step_none hst hq]
        rwa [this] at hih
      | some w =>
        have hnew := not_mem_kids_of_found hS hst hq
        have hw := (hS.found hq).2
        have hv : (step search s).visited.card = s.visited.card + 1 := by
          rw [step_found hst hq]
          simp [St.push, Finset.card_insert_of_notMem hw]
        have hk : ∀ v, (kids search v (k + 1) s).card =
            (if u = v then 1 else 0) + (kids search v k (step search s)).card := by
          intro v
          rw [kids_found hst hq]
          by_cases huv : u = v
          · subst huv
            rw [ite_eq_left rfl, ite_eq_left rfl, Finset.card_insert_of_notMem (hnew u k)]
            omega
          · rw [ite_eq_right huv, ite_eq_right huv, zero_add]
        simp only [hk]
        rw [Finset.sum_add_distrib, Finset.sum_ite_eq]
        simp only [Finset.mem_univ, ite_true]
        omega

/-- **Lemma 1 on the executable search.** The total charge of a run from one root is at most
`3 √(2 n Σ N_v)`, for any entry counts `N_v`. Here `c_v` is the number of children of `v` in that run. -/
theorem runCharge_total {search : V → Finset V → Option V} (hS : IsSearch E search) (N : V → ℝ)
    (hN : ∀ v, 0 ≤ N v) (k : ℕ) (s : St V) (hI : Inv E s) :
    runCharge E N search k s ≤ 3 * Real.sqrt (2 * Fintype.card V * ∑ v, N v) := by
  refine (runCharge_le hS N hN k s).trans ?_
  set c : V → ℕ := fun v => (kids search v k s).card with hc
  have hsum : ∑ v, c v ≤ Fintype.card V := by
    have := sum_kids_le hS k s
    simp only [hc]
    omega
  refine le_trans ?_ (mul_le_mul_of_nonneg_left (lemma1_cauchy c N hN hsum) (by norm_num))
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun v _ => ?_
  have hh : harm (c v) ≤ 2 * Real.sqrt (c v) := sum_inv_sqrt_le (c v)
  have hp : ((pops search v k s : ℕ) : ℝ) ≤ 1 := by exact_mod_cast (pops_le hS v k s hI).1
  have hs := Real.sqrt_nonneg (N v)
  have h1 : Real.sqrt (N v) * harm (c v) ≤ 2 * Real.sqrt ((c v : ℝ) * N v) := by
    rw [Real.sqrt_mul (Nat.cast_nonneg _)]
    nlinarith [mul_le_mul_of_nonneg_left hh hs]
  have h2 : Real.sqrt (N v) * (pops search v k s : ℝ) ≤ Real.sqrt (N v) := by
    nlinarith
  have h3 := vertex_cost_le (N v) (hN v) (c v)
  linarith

/-- **Lemma 1, array model, for the search itself.** Charges with `N_v = deg v` sum to at most `3 √(2 n m)`. -/
theorem dfs_charge_array {search : V → Finset V → Option V} (hS : IsSearch E search) (k : ℕ) (s : St V)
    (hI : Inv E s) :
    runCharge E (fun v => (outDeg E v : ℝ)) search k s ≤
      3 * Real.sqrt (2 * Fintype.card V * edgeCount E) := by
  have h := runCharge_total hS (fun v => (outDeg E v : ℝ)) (fun _ => by positivity) k s hI
  have hs : ∑ v, (outDeg E v : ℝ) = edgeCount E := by exact_mod_cast sum_outDeg E
  rwa [hs] at h

/-- **Lemma 1, matrix model, for the search itself.** Charges with `N_v = n` sum to at most `3 √(2 n · n²)`. -/
theorem dfs_charge_matrix {search : V → Finset V → Option V} (hS : IsSearch E search) (k : ℕ) (s : St V)
    (hI : Inv E s) :
    runCharge E (fun _ => (Fintype.card V : ℝ)) search k s ≤
      3 * Real.sqrt (2 * Fintype.card V * (Fintype.card V : ℝ) ^ 2) := by
  have h := runCharge_total hS (fun _ => (Fintype.card V : ℝ)) (fun _ => by positivity) k s hI
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at h
  rw [pow_two]
  exact h

end Charge

/-- **Theorem 2's total, array model.** The search charges and the minimum-finding charges together are at most
`6 √(n m)`. -/
theorem dominator_charge_total (E : V → V → Prop) [DecidableEq V] {search : V → Finset V → Option V}
    (hS : IsSearch E search) (k : ℕ) (s : St V) (hI : Inv E s) :
    runCharge E (fun v => (outDeg E v : ℝ)) search k s + ∑ w, Real.sqrt (inDeg E w) ≤
      6 * Real.sqrt (Fintype.card V * edgeCount E) := by
  have h1 := dfs_charge_array hS k s hI
  have h2 := sum_sqrt_inDeg_le E
  have h3 : Real.sqrt (2 * Fintype.card V * edgeCount E) = Real.sqrt 2 * Real.sqrt (Fintype.card V * edgeCount E) := by
    rw [mul_assoc, Real.sqrt_mul (by norm_num)]
  have h4 : Real.sqrt 2 ≤ 3 / 2 := by
    rw [Real.sqrt_le_left (by norm_num)]
    norm_num
  have h5 := Real.sqrt_nonneg ((Fintype.card V : ℝ) * edgeCount E)
  rw [h3] at h1
  nlinarith

/-! ## What the named hypotheses give -/

/-- From `BBHT`: with `t ≥ 1` marked entries, budget `k + 1 ≥ 3 C √(N/t)` finds one with probability at least
`2/3`. This is the truncation of Lemma 1: "truncating costs a constant". -/
theorem bbht_budget (h : BBHT) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (α : Type) (marked : Fin N → α → Bool), ∃ d : ℕ → ℕ,
      ∃ A : ∀ k, QAlg (Fin N) α (Fin (d k)) (Option (Fin N)) k,
      ∀ (x : Fin N → α) (k : ℕ), 1 ≤ markedCount marked x →
        3 * C * Real.sqrt ((N : ℝ) / markedCount marked x) ≤ (k : ℝ) + 1 →
        2 / 3 ≤ (A k).prob x (fun o => ∃ i, o = some i ∧ marked i (x i) = true) := by
  obtain ⟨C, hC, hA⟩ := h
  refine ⟨C, hC, fun N α marked => ?_⟩
  obtain ⟨d, A, hAx⟩ := hA N α marked
  refine ⟨d, A, fun x k ht hk => ?_⟩
  obtain ⟨_, hmono, hsum⟩ := hAx x
  obtain ⟨hsm, hle⟩ := hsum ht
  set P : ℕ → ℝ := fun j => (A j).prob x (fun o => ∃ i, o = some i ∧ marked i (x i) = true) with hP
  have hmono' : Monotone P := monotone_nat_of_le_succ hmono
  by_contra hcon
  push Not at hcon
  have hterm : ∀ j ≤ k, 1 / 3 < 1 - P j := by
    intro j hj
    have := hmono' hj
    simp only [hP] at this hcon ⊢
    linarith
  -- the terms decrease and sum, so they tend to zero from above
  have hanti : Antitone (fun j => 1 - P j) := fun a b hab => by
    have := hmono' hab
    simp only
    linarith
  have hnn : ∀ j, 0 ≤ 1 - P j := fun j => hanti.le_of_tendsto hsm.tendsto_atTop_zero j
  have hpart : ∑ j ∈ range (k + 1), (1 - P j) ≤ ∑' j, (1 - P j) :=
    hsm.sum_le_tsum _ (fun j _ => hnn j)
  have hlow : ((k : ℝ) + 1) * (1 / 3) < ∑ j ∈ range (k + 1), (1 - P j) := by
    have := Finset.sum_lt_sum_of_nonempty (s := range (k + 1)) (by simp)
      (fun j hj => hterm j (by simpa [Nat.lt_succ_iff] using hj))
    simpa [mul_comm] using this
  have hsq := Real.sqrt_nonneg ((N : ℝ) / markedCount marked x)
  linarith

/-- From `DurrHoyer`: with error `δ` per vertex, the query budgets of the minimum findings at all vertices with
predecessors sum to at most `C √(n m) (1 + log (1/δ))`. Each budget belongs to an algorithm with that success
probability. This is the sum in Theorem 2, with `δ = 1/(c n)` giving the factor `O(log n)`. -/
theorem durrHoyer_total (h : DurrHoyer) :
    ∃ C : ℝ, 0 < C ∧ ∀ (δ : ℝ) (_ : 0 < δ) (_ : δ ≤ 1 / 2) (E : V → V → Prop) (α : Type)
      (key : ∀ w, Fin (inDeg E w) → α → WithTop ℕ),
      ∃ T : V → ℕ,
        (∀ w, 1 ≤ inDeg E w → ∃ (d : ℕ) (A : QAlg (Fin (inDeg E w)) α (Fin d) (Option (Fin (inDeg E w))) (T w)),
          ∀ x : Fin (inDeg E w) → α, 1 - δ ≤ A.prob x (fun o => ∃ i, o = some i ∧ ∀ j, key w i (x i) ≤ key w j (x j))) ∧
        ∑ w, (T w : ℝ) ≤ C * Real.sqrt (Fintype.card V * edgeCount E) * (1 + Real.log (1 / δ)) := by
  classical
  obtain ⟨C, hC, hA⟩ := h
  refine ⟨C, hC, fun δ hδ hδ2 E α key => ?_⟩
  have hex : ∀ w, ∃ t : ℕ, (t : ℝ) ≤ C * Real.sqrt (inDeg E w) * (1 + Real.log (1 / δ)) ∧
      (1 ≤ inDeg E w → ∃ (d : ℕ) (A : QAlg (Fin (inDeg E w)) α (Fin d) (Option (Fin (inDeg E w))) t),
        ∀ x : Fin (inDeg E w) → α, 1 - δ ≤ A.prob x (fun o => ∃ i, o = some i ∧ ∀ j, key w i (x i) ≤ key w j (x j))) := by
    intro w
    by_cases hw : 1 ≤ inDeg E w
    · obtain ⟨d, T, A, hT, hp⟩ := hA (inDeg E w) hw α (key w) δ hδ hδ2
      exact ⟨T, hT, fun _ => ⟨d, A, hp⟩⟩
    · refine ⟨0, ?_, fun h => absurd h hw⟩
      have hlog : 0 ≤ Real.log (1 / δ) := Real.log_nonneg (by
        rw [le_div_iff₀ hδ]
        linarith)
      push_cast
      positivity
  choose T hT1 hT2 using hex
  refine ⟨T, hT2, ?_⟩
  have hlog : 0 ≤ 1 + Real.log (1 / δ) := by
    have : 0 ≤ Real.log (1 / δ) := Real.log_nonneg (by
      rw [le_div_iff₀ hδ]
      linarith)
    linarith
  calc ∑ w, (T w : ℝ) ≤ ∑ w, C * Real.sqrt (inDeg E w) * (1 + Real.log (1 / δ)) :=
        Finset.sum_le_sum fun w _ => hT1 w
    _ = C * (∑ w, Real.sqrt (inDeg E w)) * (1 + Real.log (1 / δ)) := by
        rw [← Finset.sum_mul, ← Finset.mul_sum]
    _ ≤ C * Real.sqrt (Fintype.card V * edgeCount E) * (1 + Real.log (1 / δ)) := by
        apply mul_le_mul_of_nonneg_right _ hlog
        exact mul_le_mul_of_nonneg_left (sum_sqrt_inDeg_le E) hC.le

end Dominators
