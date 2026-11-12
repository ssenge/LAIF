import QuantumBranching.Composition

/-!
# The halving form

A variant of the composition for procedures whose value calls shrink the instance by half, while
their measure may be as large as at the calling node. This is the form of algorithms that split an
instance into independent parts of equal measure.

`HConditions` replaces (M2) and (M3) by a size `size : I → ℕ` with

- (H0) `size c ≤ size x` for every child `c` in the OR-tree of `x`;
- (H2) every value call `y` at `v` has `2 * size y ≤ size v`, `0 < size v`, and
  `log (B y) ≤ log (B v) + c`.

(M1) and the bounds on depth, width and calls are as before. There are no Box nodes.

The search on the instances of size below `2 ^ j` is the walk on the OR-tree with the parameter
`tH j m = exp m * N ^ (a q + b q * j)`, where a value call at a node `v` is the search of level
`j - 1` at the level `log (B v) + q * log N`. `treeSqH_le` is the precondition of the walk: the sum of
the squared step counts over the OR-tree of `x` is at most `tH j m`. `hsearch_valid` adds the
acceptance and the levels of the calls, and `htime_bound` the time
`N ^ (q + bH q * (j + 1) / 2) * √(B x)`. For instances of size at most `n`, `j` is about `log₂ n`,
so the factor is `n ^ O(log n)`.
-/

open Real

namespace QuantumBranching

/-- The exponent per level of the halving form. -/
def bH (q : ℕ) : ℕ := 7 * q + 1

namespace Setting

variable {I : Type*} (S : Setting I)

/-- The conditions of the halving form. -/
structure HConditions (size : I → ℕ) : Prop where
  B_ge : ∀ x, 2 ≤ S.B x
  rank_le : ∀ x, S.proc.rank x ≤ S.D
  width_le : ∀ x, (S.proc.children x).length ≤ S.t
  calls_le : ∀ x, (S.proc.calls x).length ≤ S.s
  loc_ge : 1 ≤ S.loc
  /-- There are no Box nodes. -/
  no_box : ∀ a, S.proc.boxFlag a = false
  /-- (M1). -/
  M1 : ∀ x, S.Searched x → ∀ l, (S.proc.orTree x).IsAntichain l → (l.map S.B).sum ≤ S.K * S.B x
  /-- (H0). -/
  H0 : ∀ x, ∀ c ∈ S.proc.children x, size c ≤ size x
  /-- (H2), the size. -/
  H2size : ∀ v, ∀ y ∈ S.proc.calls v, 2 * size y ≤ size v ∧ 0 < size v
  /-- (H2), the measure. -/
  H2B : ∀ v, ∀ y ∈ S.proc.calls v, log (S.B y) ≤ log (S.B v) + S.c

/-- The powers of `N` that dominate the constants of the halving form. -/
structure HBound (N : ℝ) (q : ℕ) (κ : ℝ) : Prop where
  N_ge : 4 ≤ N
  c_le : S.c ≤ q * log N
  depth_le : ((S.D : ℝ) + 1) * S.K ≤ N ^ q
  t_le : (S.t : ℝ) + 1 ≤ N ^ q
  calls_sq : 12 * (S.s : ℝ) ^ 2 ≤ N ^ (2 * q)
  walk_sq : ((S.r : ℝ) * κ) ^ 2 * ((S.D : ℝ) + 1) ≤ N ^ (2 * q)
  loc_sq : 12 * S.loc ^ 2 ≤ N ^ q

variable (G : Primitives) (n : ℕ) (N : ℝ) (q : ℕ)

/-- The level of the value calls at a node of measure `b`. -/
noncomputable def hLevel (b : ℝ) : ℝ := log b + q * log N

/-- The parameter of the walk at size level `j` and measure level `m`. -/
noncomputable def tH (j : ℕ) (m : ℝ) : ℝ := exp m * N ^ (bH q * (j + 1))

/-- The time of the search at size level `j` and measure level `m`. -/
noncomputable def hTime (j : ℕ) (m : ℝ) : ℝ := (S.r : ℝ) * G.walkTime n (tH N q j m) ((S.D : ℝ) + 1)

/-- The number of steps to a child of `v`, for a budget `Q` of the value calls. -/
noncomputable def stepH (Q : ℝ → ℝ) (v : I) : ℝ :=
  2 * (S.loc + ((S.proc.calls v).length : ℝ) * Q (hLevel N q (S.B v)))

/-- The sum of the squared step counts over the OR-tree of `x`, at size level `j`. -/
noncomputable def treeSqH (j : ℕ) (x : I) : ℝ :=
  ((S.treeNodes x).map fun v =>
    (S.width v : ℝ) * S.stepH N q (S.hTime G n N q (j - 1)) v ^ 2).sum

variable {S}

section Nodes

variable {size : I → ℕ}

/-- Sizes do not grow along the OR-tree. -/
theorem size_le_of_mem_nodes (hH0 : ∀ x, ∀ c ∈ S.proc.children x, size c ≤ size x) :
    ∀ x, ∀ v ∈ S.treeNodes x, size v ≤ size x := by
  intro x
  induction hk : S.proc.rank x using Nat.strong_induction_on generalizing x with
  | _ k ih =>
    intro v hv
    unfold Setting.treeNodes at hv
    cases ho : S.proc.outcome x with
    | inl b =>
      rw [S.proc.orTree_inl ho, ORTree.nodes_node] at hv
      simp at hv
      rw [hv]
    | inr cs =>
      rw [S.proc.orTree_inr ho, ORTree.nodes_node] at hv
      rcases List.mem_cons.mp hv with rfl | hv
      · exact le_rfl
      · obtain ⟨t, ht, hvt⟩ := List.mem_flatMap.mp hv
        obtain ⟨c, hc, rfl⟩ := List.mem_map.mp ht
        have hcx : c ∈ S.proc.children x := by
          unfold Proc.children
          rw [ho]
          exact hc
        have h1 := ih _ (hk ▸ S.proc.rank_child ho hc) c rfl v hvt
        exact h1.trans (hH0 x c hcx)

end Nodes

section Valid

variable {G : Primitives} {n : ℕ} {N : ℝ} {q : ℕ} {κ : ℕ → ℝ} {size : I → ℕ}
variable (hC : S.HConditions size) {κn : ℝ} (hQ : S.HBound N q κn)
include hC hQ

omit hQ in
theorem hB_pos (x : I) : 0 < S.B x := by linarith [hC.B_ge x]

/-- (M1) across depths, in powers of `N`. -/
theorem hsum_nodes_le {x : I} (hx : S.Searched x) :
    ((S.treeNodes x).map S.B).sum ≤ N ^ q * S.B x := by
  have h1 := S.proc.nodes_sum_le_levels S.B x (S.D + 1) (Nat.lt_succ_of_le (hC.rank_le x))
  have h2 : ∀ ℓ ∈ Finset.range (S.D + 1),
      (((S.proc.orTree x).levelNodes ℓ).map S.B).sum ≤ S.K * S.B x := fun ℓ _ =>
    hC.M1 x hx _ (ORTree.isAntichain_levelNodes _ ℓ)
  have h3 : ((S.treeNodes x).map S.B).sum ≤ ((S.D : ℝ) + 1) * S.K * S.B x := by
    refine h1.trans ((Finset.sum_le_sum h2).trans (le_of_eq ?_))
    simp [Finset.sum_const, nsmul_eq_mul]
    ring
  exact h3.trans (mul_le_mul_of_nonneg_right hQ.depth_le (hB_pos hC x).le)

omit hC in
/-- The time of a level, squared, from the bound of the walk. -/
theorem hTime_sq (hwalk : WalkBound G κ) (hκ : κ n = κn) (j : ℕ) {m : ℝ} (hm : 0 ≤ m) :
    S.hTime G n N q j m ^ 2 ≤ N ^ (2 * q) * tH N q j m := by
  have hN := hQ.N_ge
  have hN0 := N_pos hN
  have hT1 : 1 ≤ tH N q j m := by
    unfold tH
    have h1 := one_le_pow_N hN (bH q * (j + 1))
    have h2 := Real.one_le_exp hm
    nlinarith
  have hD1 : (1 : ℝ) ≤ (S.D : ℝ) + 1 := by
    have : (0 : ℝ) ≤ (S.D : ℝ) := Nat.cast_nonneg _
    linarith
  have hT0 : 0 ≤ tH N q j m := by linarith
  obtain ⟨h1, _, _⟩ := hwalk n (tH N q j m) (tH N q j m) ((S.D : ℝ) + 1) hT0 le_rfl hT1 hD1
  have hnn := G.walkTime_nonneg n (tH N q j m) ((S.D : ℝ) + 1)
  have hs : 0 ≤ tH N q j m * ((S.D : ℝ) + 1) := by positivity
  rw [hκ] at h1
  have hsq : G.walkTime n (tH N q j m) ((S.D : ℝ) + 1) ^ 2 ≤
      κn ^ 2 * (tH N q j m * ((S.D : ℝ) + 1)) := by
    have := pow_le_pow_left₀ hnn h1 2
    rwa [mul_pow, Real.sq_sqrt hs] at this
  have hr2 : (0 : ℝ) ≤ (S.r : ℝ) ^ 2 := by positivity
  unfold Setting.hTime
  calc ((S.r : ℝ) * G.walkTime n (tH N q j m) ((S.D : ℝ) + 1)) ^ 2
      = (S.r : ℝ) ^ 2 * G.walkTime n (tH N q j m) ((S.D : ℝ) + 1) ^ 2 := by ring
    _ ≤ (S.r : ℝ) ^ 2 * (κn ^ 2 * (tH N q j m * ((S.D : ℝ) + 1))) :=
        mul_le_mul_of_nonneg_left hsq hr2
    _ = (((S.r : ℝ) * κn) ^ 2 * ((S.D : ℝ) + 1)) * tH N q j m := by ring
    _ ≤ N ^ (2 * q) * tH N q j m := mul_le_mul_of_nonneg_right hQ.walk_sq hT0

/-- **The cost of a child.** At size level `j + 1`, the calls at `v` are searches of level `j`. -/
theorem stepH_sq_le (hwalk : WalkBound G κ) (hκ : κ n = κn) (j : ℕ) (v : I) :
    S.stepH N q (S.hTime G n N q j) v ^ 2 ≤
      N ^ q * (1 + N ^ (4 * q) * N ^ (bH q * (j + 1)) * S.B v) := by
  have hN := hQ.N_ge
  have hN0 := N_pos hN
  have hl := log_N_pos hN
  have hb := hB_pos hC v
  set Qv := S.hTime G n N q j (hLevel N q (S.B v)) with hQv
  have hlev0 : 0 ≤ hLevel N q (S.B v) := by
    unfold hLevel
    have : 0 ≤ log (S.B v) := Real.log_nonneg (by linarith [hC.B_ge v])
    positivity
  have hQsq : Qv ^ 2 ≤ N ^ (3 * q) * N ^ (bH q * (j + 1)) * S.B v := by
    have h1 := hTime_sq hQ hwalk hκ j hlev0
    rw [← hQv] at h1
    refine h1.trans (le_of_eq ?_)
    unfold tH hLevel
    rw [Real.exp_add, Real.exp_log hb, ← pow_eq_exp hN q]
    rw [show 3 * q = 2 * q + q by ring, pow_add]
    ring
  have hcalls : ((S.proc.calls v).length : ℝ) ≤ S.s := by exact_mod_cast hC.calls_le v
  have hcalls0 : (0 : ℝ) ≤ ((S.proc.calls v).length : ℝ) := Nat.cast_nonneg _
  have hcsq : ((S.proc.calls v).length : ℝ) ^ 2 ≤ (S.s : ℝ) ^ 2 :=
    pow_le_pow_left₀ hcalls0 hcalls 2
  have h12 : 12 * ((S.proc.calls v).length : ℝ) ^ 2 ≤ N ^ q * N ^ q := by
    have := hQ.calls_sq
    rw [two_mul, pow_add] at this
    linarith
  have hQ0 : 0 ≤ Qv ^ 2 := sq_nonneg _
  have hNq : 0 < N ^ q := pow_pos hN0 q
  have hloc := hQ.loc_sq
  have hstep : S.stepH N q (S.hTime G n N q j) v ^ 2 ≤
      12 * S.loc ^ 2 + 12 * ((S.proc.calls v).length : ℝ) ^ 2 * Qv ^ 2 := by
    unfold Setting.stepH
    rw [← hQv]
    nlinarith [sq_nonneg (S.loc - ((S.proc.calls v).length : ℝ) * Qv)]
  have h4 : 12 * ((S.proc.calls v).length : ℝ) ^ 2 * Qv ^ 2 ≤
      (N ^ q * N ^ q) * (N ^ (3 * q) * N ^ (bH q * (j + 1)) * S.B v) :=
    mul_le_mul h12 hQsq hQ0 (by positivity)
  have h5 : (N ^ q * N ^ q) * (N ^ (3 * q) * N ^ (bH q * (j + 1)) * S.B v) =
      N ^ q * (N ^ (4 * q) * N ^ (bH q * (j + 1)) * S.B v) := by
    rw [show 4 * q = q + 3 * q by ring, pow_add]
    ring
  rw [h5] at h4
  have h6 : 12 * S.loc ^ 2 ≤ N ^ q * 1 := by simpa using hloc
  calc S.stepH N q (S.hTime G n N q j) v ^ 2 ≤ _ := hstep
    _ ≤ N ^ q * 1 + N ^ q * (N ^ (4 * q) * N ^ (bH q * (j + 1)) * S.B v) := add_le_add h6 h4
    _ = _ := by ring

omit hQ in
/-- At size level `0` there are no value calls. -/
theorem calls_nil_of_size {x v : I} (hx : size x < 2 ^ 0) (hv : v ∈ S.treeNodes x) :
    S.proc.calls v = [] := by
  have h1 := size_le_of_mem_nodes hC.H0 x v hv
  rw [pow_zero] at hx
  rcases hcv : S.proc.calls v with _ | ⟨y, l⟩
  · rfl
  · have := (hC.H2size v y (by rw [hcv]; simp)).2
    omega

omit hQ in
/-- A value call at a node of the tree of `x` at size level `j + 1` is at size level `j`. -/
theorem call_size {x v y : I} {j : ℕ} (hx : size x < 2 ^ (j + 1)) (hv : v ∈ S.treeNodes x)
    (hy : y ∈ S.proc.calls v) : size y < 2 ^ j := by
  have h1 := size_le_of_mem_nodes hC.H0 x v hv
  have h2 := (hC.H2size v y hy).1
  rw [pow_succ] at hx
  omega

/-- A value call is at the measure level of its node. -/
theorem call_hLevel {v y : I} (hy : y ∈ S.proc.calls v) :
    log (S.B y) ≤ hLevel N q (S.B v) := by
  have := hC.H2B v y hy
  have := hQ.c_le
  unfold hLevel
  linarith

/-- **The precondition of the walk.** At size level `j`, the sum of the squared step counts over the
OR-tree of `x` is at most `tH j m`. -/
theorem treeSqH_le (hwalk : WalkBound G κ) (hκ : κ n = κn) {x : I} {j : ℕ} {m : ℝ}
    (hR : S.Searched x) (hsize : size x < 2 ^ j) (hx : log (S.B x) ≤ m) :
    S.treeSqH G n N q j x ≤ tH N q j m := by
  have hN := hQ.N_ge
  have hN0 := N_pos hN
  have hNq : 0 < N ^ q := pow_pos hN0 q
  have hBx : S.B x ≤ exp m := by
    rw [← Real.exp_log (hB_pos hC x)]
    exact Real.exp_le_exp.mpr hx
  set V := S.treeNodes x with hV
  set e : ℕ := bH q * j with he
  have hone : ∀ v ∈ V, (S.width v : ℝ) * S.stepH N q (S.hTime G n N q (j - 1)) v ^ 2 ≤
      N ^ q * (N ^ q * (1 + N ^ (4 * q) * N ^ e * S.B v)) := by
    intro v hv
    have hw : (S.width v : ℝ) ≤ N ^ q := by
      have : S.width v ≤ S.t + 1 := by
        unfold Setting.width
        have := hC.width_le v
        omega
      exact (by exact_mod_cast this : ((S.width v : ℕ) : ℝ) ≤ (S.t : ℝ) + 1).trans hQ.t_le
    have hs : S.stepH N q (S.hTime G n N q (j - 1)) v ^ 2 ≤
        N ^ q * (1 + N ^ (4 * q) * N ^ e * S.B v) := by
      rcases Nat.eq_zero_or_pos j with hj | hj
      · subst hj
        have hnil := calls_nil_of_size hC hsize hv
        unfold Setting.stepH
        rw [hnil]
        have h6 : 12 * S.loc ^ 2 ≤ N ^ q * 1 := by simpa using hQ.loc_sq
        have hpos : 0 ≤ N ^ q * (N ^ (4 * q) * N ^ e * S.B v) := by
          have := hB_pos hC v
          positivity
        simp only [List.length_nil, Nat.cast_zero, zero_mul, add_zero]
        nlinarith [sq_nonneg S.loc]
      · have he' : e = bH q * (j - 1 + 1) := by rw [he]; congr 1; omega
        rw [he']
        exact stepH_sq_le hC hQ hwalk hκ (j - 1) v
    have hs0 : 0 ≤ S.stepH N q (S.hTime G n N q (j - 1)) v ^ 2 := sq_nonneg _
    exact mul_le_mul hw hs hs0 hNq.le
  have hsum := list_map_sum_le (l := V) hone
  have haff : (V.map fun v => N ^ q * (N ^ q * (1 + N ^ (4 * q) * N ^ e * S.B v))).sum =
      N ^ q * N ^ q * V.length + N ^ q * N ^ q * N ^ (4 * q) * N ^ e * (V.map S.B).sum := by
    have := list_sum_affine V S.B (N ^ q * N ^ q) (N ^ q * N ^ q * N ^ (4 * q) * N ^ e)
    rw [← this]
    congr 1
    refine List.map_congr_left fun v _ => ?_
    ring
  have hM1 := hsum_nodes_le hC hQ hR
  have hlen : (V.length : ℝ) ≤ N ^ q * S.B x := by
    have : (V.length : ℝ) ≤ (V.map S.B).sum := by
      have h := list_map_sum_le (l := V) (f := fun _ => (1 : ℝ)) (g := S.B)
        (fun a _ => by linarith [hC.B_ge a])
      simpa using h
    linarith
  have hT : S.treeSqH G n N q j x ≤ (N ^ (3 * q) + N ^ (7 * q) * N ^ e) * S.B x := by
    unfold Setting.treeSqH
    rw [← hV]
    refine hsum.trans (haff.le.trans ?_)
    have hc1 : 0 ≤ N ^ q * N ^ q := by positivity
    have hc2 : 0 ≤ N ^ q * N ^ q * N ^ (4 * q) * N ^ e := by positivity
    have h1 := mul_le_mul_of_nonneg_left hlen hc1
    have h2 := mul_le_mul_of_nonneg_left hM1 hc2
    have h3 : N ^ q * N ^ q * (N ^ q * S.B x) +
        N ^ q * N ^ q * N ^ (4 * q) * N ^ e * (N ^ q * S.B x)
        = (N ^ (3 * q) + N ^ (7 * q) * N ^ e) * S.B x := by
      rw [show 3 * q = q + q + q by ring, show 7 * q = q + q + 4 * q + q by ring]
      simp only [pow_add]
      ring
    linarith
  have hcoef : N ^ (3 * q) + N ^ (7 * q) * N ^ e ≤ N ^ (bH q * (j + 1)) := by
    have h1 : N ^ (3 * q) ≤ N ^ (7 * q) * N ^ e := by
      rw [← pow_add]; exact pow_mono_N hN (by omega)
    have h2 : N ^ (bH q * (j + 1)) = N ^ (7 * q) * N ^ e * N := by
      rw [he, ← pow_add, ← pow_succ]
      congr 1
      simp only [bH]
      ring
    have h3 : 0 ≤ N ^ (7 * q) * N ^ e := by positivity
    rw [h2]
    nlinarith
  have hB0 := hB_pos hC x
  refine hT.trans ?_
  unfold tH
  have h4 : 0 ≤ N ^ (3 * q) + N ^ (7 * q) * N ^ e := by positivity
  calc (N ^ (3 * q) + N ^ (7 * q) * N ^ e) * S.B x ≤ N ^ (bH q * (j + 1)) * exp m :=
        mul_le_mul hcoef hBx hB0.le (by positivity)
    _ = _ := by ring

/-- **The search is valid.** At size level `j`, for `x` the root or the target of a value call: the
sum of the squared step counts is at most the parameter of the walk, the walk accepts according to the
answer, and every value call at a node of the tree is an instance of the search at size level `j - 1`
and at the measure level of its node. -/
theorem hsearch_valid (hwalk : WalkBound G κ) (hκ : κ n = κn) {x : I} {j : ℕ} {m : ℝ}
    (hR : S.Searched x) (hsize : size x < 2 ^ j) (hx : log (S.B x) ≤ m) (hm : 0 ≤ m) :
    S.treeSqH G n N q j x ≤ tH N q j m ∧
      (S.proc.answer x = true → (S.proc.orTree x).HasMarked ∧
        1 / 2 ≤ G.walkAccept n (S.treeSqH G n N q j x) (tH N q j m) ((S.D : ℝ) + 1) true) ∧
      (S.proc.answer x = false → ¬ (S.proc.orTree x).HasMarked ∧
        G.walkAccept n (S.treeSqH G n N q j x) (tH N q j m) ((S.D : ℝ) + 1) false ≤ 1 / 4) ∧
      (∀ v ∈ S.treeNodes x, ∀ y ∈ S.proc.calls v,
        S.Searched y ∧ size y < 2 ^ (j - 1) ∧ log (S.B y) ≤ hLevel N q (S.B v)) := by
  have hN := hQ.N_ge
  have hN0 := N_pos hN
  have hle := treeSqH_le hC hQ hwalk hκ hR hsize hx
  have hT0 : 0 ≤ S.treeSqH G n N q j x := by
    unfold Setting.treeSqH
    refine list_map_sum_nonneg fun v _ => ?_
    positivity
  have hT1 : 1 ≤ tH N q j m := by
    unfold tH
    have h1 := one_le_pow_N hN (bH q * (j + 1))
    have h2 := Real.one_le_exp hm
    nlinarith
  have hD1 : (1 : ℝ) ≤ (S.D : ℝ) + 1 := by
    have : (0 : ℝ) ≤ (S.D : ℝ) := Nat.cast_nonneg _
    linarith
  obtain ⟨_, ha1, ha2⟩ := hwalk n _ _ _ hT0 hle hT1 hD1
  refine ⟨hle, fun ha => ⟨(S.proc.answer_iff_marked x).mp ha, ha1⟩, fun ha => ⟨?_, ha2⟩,
    fun v hv y hy => ⟨Or.inr ⟨v, hy⟩, ?_, call_hLevel hC hQ hy⟩⟩
  · intro hmarked
    have := (S.proc.answer_iff_marked x).mpr hmarked
    rw [ha] at this
    exact Bool.noConfusion this
  · rcases Nat.eq_zero_or_pos j with hj | hj
    · subst hj
      have := calls_nil_of_size hC hsize hv
      rw [this] at hy
      simp at hy
    · obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
      simpa using call_size hC hsize hv hy

/-- **The time bound.** At size level `j`, the time of the search on `x` is at most
`N ^ (q + bH q * (j + 1) / 2) * √(B x)`. -/
theorem htime_bound (hwalk : WalkBound G κ) (hκ : κ n = κn) (j : ℕ) (x : I) :
    S.hTime G n N q j (log (S.B x)) ≤ N ^ (((2 * q + bH q * (j + 1) : ℕ) : ℝ) / 2) * √(S.B x) := by
  have hN := hQ.N_ge
  have hb := hB_pos hC x
  have h0 : 0 ≤ log (S.B x) := Real.log_nonneg (by linarith [hC.B_ge x])
  have h1 := hTime_sq hQ hwalk hκ j h0
  refine time_of_sq hN hb (h1.trans (le_of_eq ?_))
  unfold tH
  rw [pow_add]
  ring

end Valid

end Setting

end QuantumBranching
