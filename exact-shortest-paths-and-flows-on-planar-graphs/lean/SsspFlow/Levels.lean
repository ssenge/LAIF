import SsspFlow.Emulator

/-!
# The metrics along a sequence of levels

For a level `Γ` of a planar connected map `M` with dart weights `g`, `lvlT` is `U` times the distance
in the split at `Γ`. The bags of the level are the cycles of `ψ`. `cycOf` lists a cycle from its corner
of least code.

`LevelMetric` holds, for values `δ` on the corners of a level, a metric `μ` with (M) per bag such that
`lvlT ≤ μ ≤ Λ * lvlT` and `μ ≤ δ ≤ (U + 4) / U * μ`. `levelMetric_step`: such values at a larger set `Γ'`
give such values at `Γ` by one call of the bag function per bag, on the least total weights of hub walks
over `δ`. Errors add up: `Λ` grows by the factor `((U + 4) / U) ^ 2` per level. The feasible point for
the bag function is the composition of the disks of the larger set, by `hubDist_monge`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped ENNReal

namespace SsspFlow

open FourColor
open Congest (RealizationBox)

/-! ### Cycles of a permutation as lists -/

section Cycles

variable {D : Type*} [Fintype D] [DecidableEq D] (f : Equiv.Perm D)

/-- The orbit of `x`, in order from `x`. -/
noncomputable def orbitList (x : D) : List D :=
  (List.range (Function.minimalPeriod f x)).map fun i => f^[i] x

private theorem mem_periodicPts (x : D) : x ∈ Function.periodicPts f := by
  refine ⟨orderOf f, orderOf_pos f, ?_⟩
  show f^[orderOf f] x = x
  rw [← Equiv.Perm.coe_pow, pow_orderOf_eq_one]
  rfl

theorem minimalPeriod_perm_pos (x : D) : 0 < Function.minimalPeriod f x :=
  Function.minimalPeriod_pos_of_mem_periodicPts (mem_periodicPts f x)

theorem length_orbitList (x : D) : (orbitList f x).length = Function.minimalPeriod f x := by
  simp [orbitList]

theorem orbitList_ne_nil (x : D) : orbitList f x ≠ [] := by
  intro h
  have h1 := length_orbitList f x
  rw [h] at h1
  have h2 := minimalPeriod_perm_pos f x
  simp at h1
  omega

theorem getElem_orbitList (x : D) (i : ℕ) (h : i < (orbitList f x).length) :
    (orbitList f x)[i] = f^[i] x := by
  simp [orbitList]

theorem orbitList_nodup (x : D) : (orbitList f x).Nodup := by
  refine List.Nodup.map_on ?_ List.nodup_range
  intro i hi j hj h
  exact Function.iterate_injOn_Iio_minimalPeriod (List.mem_range.1 hi) (List.mem_range.1 hj) h

theorem mem_orbitList {x y : D} : y ∈ orbitList f x ↔ fconnect f x y := by
  constructor
  · intro h
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 h
    exact fconnect_iterate _ _ _
  · intro h
    obtain ⟨n, rfl⟩ := fconnect_iff_iterate.1 h
    refine List.mem_map.2 ⟨n % Function.minimalPeriod f x, List.mem_range.2 ?_,
      Function.iterate_mod_minimalPeriod_eq⟩
    exact Nat.mod_lt _ (minimalPeriod_perm_pos f x)

theorem orbitList_formPerm (x : D) {y : D} (hy : y ∈ orbitList f x) :
    f y = (orbitList f x).formPerm y := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hy
  rw [List.formPerm_apply_getElem _ (orbitList_nodup f x), getElem_orbitList, getElem_orbitList,
    length_orbitList, Function.iterate_mod_minimalPeriod_eq, Function.iterate_succ_apply']

variable (code : D → ℕ)

open Classical in
/-- The element of least code on the orbit of `x`. -/
noncomputable def startOf (x : D) : D :=
  Classical.choose (Finset.exists_min_image (Finset.univ.filter (fconnect f x)) code
    ⟨x, Finset.mem_filter.2 ⟨Finset.mem_univ x, connect_refl x⟩⟩)

open Classical in
private theorem startOf_spec (x : D) :
    fconnect f x (startOf f code x) ∧ ∀ y, fconnect f x y → code (startOf f code x) ≤ code y := by
  have h := Classical.choose_spec (Finset.exists_min_image (Finset.univ.filter (fconnect f x)) code
    ⟨x, Finset.mem_filter.2 ⟨Finset.mem_univ x, connect_refl x⟩⟩)
  exact ⟨(Finset.mem_filter.1 h.1).2, fun y hy =>
    h.2 y (Finset.mem_filter.2 ⟨Finset.mem_univ y, hy⟩)⟩

theorem fconnect_startOf (x : D) : fconnect f x (startOf f code x) := (startOf_spec f code x).1

variable {code}

theorem startOf_congr (hinj : Function.Injective code) {x y : D} (h : fconnect f x y) :
    startOf f code x = startOf f code y := by
  have hs := fconnect_sym f.injective
  have h1 := (startOf_spec f code x)
  have h2 := (startOf_spec f code y)
  refine hinj (le_antisymm (h1.2 _ (connect_trans h h2.1)) (h2.2 _ ?_))
  exact connect_trans (hs _ _ h) h1.1

variable (code)

/-- The cycle of `x`, listed from its element of least code. -/
noncomputable def cycOf (x : D) : List D := orbitList f (startOf f code x)

variable {code}

theorem mem_cycOf {x y : D} : y ∈ cycOf f code x ↔ fconnect f x y := by
  rw [cycOf, mem_orbitList]
  have hs := fconnect_sym f.injective
  exact ⟨fun h => connect_trans (fconnect_startOf f code x) h,
    fun h => connect_trans (hs _ _ (fconnect_startOf f code x)) h⟩

theorem cycOf_congr (hinj : Function.Injective code) {x y : D} (h : fconnect f x y) :
    cycOf f code x = cycOf f code y := by
  rw [cycOf, cycOf, startOf_congr f hinj h]

theorem cycOf_nodup (x : D) : (cycOf f code x).Nodup := orbitList_nodup f _

theorem self_mem_cycOf (x : D) : x ∈ cycOf f code x := (mem_cycOf f).2 (connect_refl x)

theorem cycOf_formPerm (x : D) {y : D} (hy : y ∈ cycOf f code x) :
    f y = (cycOf f code x).formPerm y := orbitList_formPerm f _ hy

end Cycles

namespace RotSystem

/-! ### The cycles of a level as a family -/

section Family

variable {D : Type*} [Fintype D] [DecidableEq D] {M : RotSystem D} {code : D → ℕ}

/-- The cycles of `ψ` in `Γ`, named by their start. -/
abbrev CycIdx (M : RotSystem D) (Γ : Finset D) (code : D → ℕ) : Type _ :=
  {x : D // x ∈ Γ ∧ startOf (M.psi Γ) code x = x}

theorem mem_of_fconnect_psi {Γ : Finset D} {x y : D} (hx : x ∈ Γ) (h : fconnect (M.psi Γ) x y) :
    y ∈ Γ := by
  obtain ⟨n, rfl⟩ := fconnect_iff_iterate.1 h
  clear h
  induction n with
  | zero => exact hx
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact ((M.fixesOff_psi Γ).mem_iff _).2 ih

/-- The cycles of `ψ` form a listing in the sense of `ListsCycles`. -/
theorem listsCycles (hinj : Function.Injective code) (Γ : Finset D) :
    ListsCycles M Γ (fun i : CycIdx M Γ code => cycOf (M.psi Γ) code i.1) where
  nodup i := cycOf_nodup _ _
  mem i x hx := mem_of_fconnect_psi i.2.1 ((mem_cycOf _).1 hx)
  cover x hx := by
    have h1 := fconnect_startOf (M.psi Γ) code x
    refine ⟨⟨startOf (M.psi Γ) code x, mem_of_fconnect_psi hx h1, ?_⟩, ?_⟩
    · exact (startOf_congr _ hinj h1).symm
    · exact (mem_cycOf _).2 (fconnect_sym (M.psi Γ).injective _ _ h1)
  disj i j x hi hj := by
    have h1 := startOf_congr (M.psi Γ) hinj ((mem_cycOf _).1 hi)
    have h2 := startOf_congr (M.psi Γ) hinj ((mem_cycOf _).1 hj)
    refine Subtype.ext ?_
    rw [← i.2.2, ← j.2.2, h1, h2]
  psi i x hx := cycOf_formPerm _ _ hx
  ne i := List.ne_nil_of_mem (self_mem_cycOf _ _)

end Family

/-! ### Distances at a level -/

section Dist

variable {D : Type*} [Fintype D] [DecidableEq D] (M : RotSystem D) (g : D → ℕ) (U : ℕ)

/-- `U` times the distance in the split at `Γ`. -/
noncomputable def lvlT (Γ : Finset D) (x y : D) : ℝ≥0∞ :=
  (U : ℝ≥0∞) * (M.split Γ).walkDist (fun z => (g z : ℝ≥0∞)) ((M.split Γ).tail x) ((M.split Γ).tail y)

variable {M g U} {Γ Γ' : Finset D}

theorem lvlT_self (x : D) : lvlT M g U Γ x x = 0 := by
  rw [lvlT, walkDist_self, mul_zero]

theorem lvlT_tri (x y z : D) : lvlT M g U Γ x z ≤ lvlT M g U Γ x y + lvlT M g U Γ y z := by
  unfold lvlT
  rw [← mul_add]
  gcongr
  exact walkDist_triangle _ _ _ _

/-- Corners on different cycles have no walk in the split. -/
theorem lvlT_top (hR : M.Planar) (hc : M.Connected) (hΓ : Γ.Nonempty) (hS : M.SkeletonConnected Γ)
    (hU : 1 ≤ U) {x y : D} (hx : x ∈ Γ) (hy : y ∈ Γ) (h : ¬ fconnect (M.psi Γ) x y) :
    lvlT M g U Γ x y = ⊤ := by
  have h0 : (U : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast (by omega : U ≠ 0)
  unfold lvlT
  rw [show (M.split Γ).walkDist (fun z => (g z : ℝ≥0∞)) ((M.split Γ).tail x) ((M.split Γ).tail y)
      = ⊤ from ?_, ENNReal.mul_top h0]
  simp only [walkDist, iInf_eq_top]
  intro p hp
  have h1 : (M.split Γ).toHypermap.gcomp x y := ((M.split Γ).gcomp_iff x y).2 ⟨p, hp⟩
  exact absurd (((M.split_planar hR hc hΓ hS).2.2.2 x hx y hy).1 h1) h

/-- Different corners are at different vertices of the split, and each dart has weight at least `1`. -/
theorem le_lvlT (hg : ∀ z, 1 ≤ g z) {x y : D} (hx : x ∈ Γ) (hy : y ∈ Γ) (h : x ≠ y) :
    (U : ℝ≥0∞) ≤ lvlT M g U Γ x y := by
  unfold lvlT
  conv_lhs => rw [← mul_one (U : ℝ≥0∞)]
  gcongr
  refine le_iInf₂ fun p hp => ?_
  cases p with
  | nil => exact absurd (eq_of_tail_eq (M.nodeReturn_split Γ) hx hy hp) h
  | cons z p =>
    simp only [List.map_cons, List.sum_cons]
    have h1 : (1 : ℝ≥0∞) ≤ (g z : ℝ≥0∞) := by
      exact_mod_cast hg z
    exact h1.trans le_self_add

private theorem sum_le_length_mul {W : ℕ} (hW : ∀ z, g z ≤ W) (p : List D) :
    (p.map fun z => (g z : ℝ≥0∞)).sum ≤ (p.length : ℝ≥0∞) * W := by
  induction p with
  | nil => simp
  | cons z p ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    have h1 : (g z : ℝ≥0∞) ≤ W := by
      exact_mod_cast hW z
    calc (g z : ℝ≥0∞) + (p.map fun z => (g z : ℝ≥0∞)).sum ≤ W + (p.length : ℝ≥0∞) * W :=
          add_le_add h1 ih
      _ = ((p.length + 1 : ℕ) : ℝ≥0∞) * W := by
        push_cast
        ring

/-- Corners on one cycle are at finite distance. -/
theorem lvlT_le {W : ℕ} (hW : ∀ z, g z ≤ W) {x y : D} (h : fconnect (M.psi Γ) x y) :
    lvlT M g U Γ x y ≤ ((U * Fintype.card D * W : ℕ) : ℝ≥0∞) := by
  have h1 : (M.split Γ).toHypermap.gcomp x y := by
    have h2 : fconnect ((M.split Γ).faceReturn Γ) x y := by
      rw [faceReturn_split]
      exact h
    exact (M.split Γ).gcomp_of_fconnect_faceReturn h2
  obtain ⟨p, hp⟩ := ((M.split Γ).gcomp_iff x y).1 h1
  obtain ⟨q, hq, hqn, -, -⟩ := hp.exists_simple
  have h3 : q.length ≤ Fintype.card D := by
    have h4 := List.Nodup.of_map _ hqn
    exact h4.length_le_card
  unfold lvlT
  push_cast
  rw [mul_assoc]
  gcongr
  refine (walkDist_le _ hq).trans ((sum_le_length_mul hW q).trans ?_)
  gcongr

end Dist

end RotSystem

/-! ### The factor of one call -/

/-- The factor `(U + 4) / U`. -/
noncomputable def cU (U : ℕ) : ℝ≥0∞ := ((U : ℝ≥0∞) + 4) * (U : ℝ≥0∞)⁻¹

section Factor

variable {U : ℕ}

private theorem natU_ne_zero (hU : 1 ≤ U) : (U : ℝ≥0∞) ≠ 0 := by
  exact_mod_cast (by omega : U ≠ 0)

theorem mul_cU (hU : 1 ≤ U) : (U : ℝ≥0∞) * cU U = (U : ℝ≥0∞) + 4 := by
  unfold cU
  rw [mul_comm, mul_assoc, ENNReal.inv_mul_cancel (natU_ne_zero hU) (ENNReal.natCast_ne_top U),
    mul_one]

theorem le_cU_mul (hU : 1 ≤ U) {a b : ℝ≥0∞} (h : (U : ℝ≥0∞) * a ≤ ((U : ℝ≥0∞) + 4) * b) :
    a ≤ cU U * b := by
  refine (ENNReal.mul_le_mul_iff_right (natU_ne_zero hU) (ENNReal.natCast_ne_top U)).1 ?_
  rw [← mul_assoc, mul_cU hU]
  exact h

theorem one_le_cU (hU : 1 ≤ U) : 1 ≤ cU U := by
  refine (ENNReal.mul_le_mul_iff_right (natU_ne_zero hU) (ENNReal.natCast_ne_top U)).1 ?_
  rw [mul_one, mul_cU hU]
  exact le_self_add

theorem cU_ne_top (hU : 1 ≤ U) : cU U ≠ ⊤ := by
  refine ENNReal.mul_ne_top ?_ (ENNReal.inv_ne_top.2 (natU_ne_zero hU))
  exact ENNReal.add_ne_top.2 ⟨ENNReal.natCast_ne_top U, by norm_num⟩

theorem cU_ne_zero (hU : 1 ≤ U) : cU U ≠ 0 :=
  (lt_of_lt_of_le one_pos (one_le_cU hU)).ne'

end Factor

/-! ### One step -/

section Step

variable {D : Type*} [Fintype D] [DecidableEq D]

/-- A matrix on the positions of `c`, read on the darts of `c`, and `⊤` otherwise. -/
noncomputable def atIdx (c : List D) (m : Fin c.length → Fin c.length → ℝ≥0∞) (x y : D) : ℝ≥0∞ :=
  if h : x ∈ c ∧ y ∈ c then
    m ⟨c.idxOf x, List.idxOf_lt_length_iff.2 h.1⟩ ⟨c.idxOf y, List.idxOf_lt_length_iff.2 h.2⟩
  else ⊤

theorem atIdx_getElem {c : List D} (hc : c.Nodup) (m : Fin c.length → Fin c.length → ℝ≥0∞)
    (a b : Fin c.length) : atIdx c m c[a] c[b] = m a b := by
  have h : c[a] ∈ c ∧ c[b] ∈ c := ⟨List.getElem_mem _, List.getElem_mem _⟩
  unfold atIdx
  rw [dite_eq_left h]
  congr 1
  · exact Fin.ext (hc.idxOf_getElem _ _)
  · exact Fin.ext (hc.idxOf_getElem _ _)

theorem atIdx_of_not_mem (c : List D) (m : Fin c.length → Fin c.length → ℝ≥0∞) {x y : D}
    (h : y ∉ c) : atIdx c m x y = ⊤ := by
  unfold atIdx
  rw [dite_eq_right (fun h' => h h'.2)]

/-- The label of `x` on the bag listed by `c`, from the matrix `w` on the darts. -/
noncomputable def labOn (bag : ∀ k, (Fin k → Fin k → ℝ≥0∞) → Fin k → List ℕ) (w : D → D → ℝ≥0∞)
    (c : List D) (x : D) : List ℕ :=
  if h : x ∈ c then
    bag c.length (fun a b => w c[a] c[b]) ⟨c.idxOf x, List.idxOf_lt_length_iff.2 h⟩
  else []

theorem labOn_getElem (bag : ∀ k, (Fin k → Fin k → ℝ≥0∞) → Fin k → List ℕ) (w : D → D → ℝ≥0∞)
    {c : List D} (hc : c.Nodup) (a : Fin c.length) :
    labOn bag w c c[a] = bag c.length (fun a b => w c[a] c[b]) a := by
  have h : c[a] ∈ c := List.getElem_mem _
  unfold labOn
  rw [dite_eq_left h]
  congr 1
  exact Fin.ext (hc.idxOf_getElem _ _)

/-- The values at a level: zero on the diagonal, `⊤` between bags, and within a bag the decoded query
on the labels of the bag function. -/
noncomputable def deltaStep (bag : ∀ k, (Fin k → Fin k → ℝ≥0∞) → Fin k → List ℕ)
    (dec : List ℕ → List ℕ → ℝ≥0∞) (f : Equiv.Perm D) (code : D → ℕ) (w : D → D → ℝ≥0∞)
    (x y : D) : ℝ≥0∞ :=
  open Classical in
  if x = y then 0 else
    if fconnect f x y then dec (labOn bag w (cycOf f code x) x) (labOn bag w (cycOf f code x) y)
    else ⊤

namespace RotSystem

variable {M : RotSystem D} {g : D → ℕ} {code : D → ℕ} {U V : ℕ}

/-- Values `δ` on a level: a metric `μ` with disks close to the distances, and `δ` close to `μ`. -/
structure LevelMetric (M : RotSystem D) (g : D → ℕ) (code : D → ℕ) (U V : ℕ) (Γ : Finset D)
    (Λ : ℝ≥0∞) (μ δ : D → D → ℝ≥0∞) : Prop where
  /-- The metric is at least the distance. -/
  lo : ∀ x ∈ Γ, ∀ y ∈ Γ, lvlT M g U Γ x y ≤ μ x y
  /-- The metric is at most `Λ` times the distance. -/
  hi : ∀ x ∈ Γ, ∀ y ∈ Γ, μ x y ≤ Λ * lvlT M g U Γ x y
  /-- The value is at least the metric. -/
  val_lo : ∀ x ∈ Γ, ∀ y ∈ Γ, μ x y ≤ δ x y
  /-- The value is at most `(U + 4) / U` times the metric. -/
  val_hi : ∀ x ∈ Γ, ∀ y ∈ Γ, δ x y ≤ cU U * μ x y
  /-- Each bag has a disk for the metric. -/
  real : ∀ x ∈ Γ, Realizes V (fun a b : Fin (cycOf (M.psi Γ) code x).length =>
    μ (cycOf (M.psi Γ) code x)[a] (cycOf (M.psi Γ) code x)[b])

variable {Γ Γ' : Finset D}

/-- The distances at a level in terms of those at a larger set. -/
theorem lvlT_eq_hub (hsub : Γ ⊆ Γ') (hU : 1 ≤ U) {x y : D} (hx : x ∈ Γ') (hy : y ∈ Γ') :
    lvlT M g U Γ x y = hubDist Γ' (stepOf ((M.split Γ).nodeReturn Γ') (lvlT M g U Γ')) x y := by
  unfold lvlT
  rw [M.walkDist_split_hub hsub _ hx hy, ← hubDist_const_mul (natU_ne_zero hU)
    (ENNReal.natCast_ne_top U)]
  congr 1
  funext a b
  exact (stepOf_const_mul _ _ a b).symm

/-- Hub walks over a metric above the distances are above the distances. -/
theorem lvlT_le_hub {Λ' : ℝ≥0∞} {μ' δ' : D → D → ℝ≥0∞} (hsub : Γ ⊆ Γ') (hU : 1 ≤ U)
    (h' : LevelMetric M g code U V Γ' Λ' μ' δ') {y z : D} (hy : y ∈ Γ') (hz : z ∈ Γ') :
    lvlT M g U Γ y z ≤ hubDist Γ' (stepOf ((M.split Γ).nodeReturn Γ') μ') y z := by
  rw [lvlT_eq_hub hsub hU hy hz]
  exact hubDist_mono (stepOf_mono h'.lo) y z

/-- Hub walks over a metric within `Λ'` of the distances are within `Λ'` of the distances. -/
theorem hub_le_lvlT {Λ' : ℝ≥0∞} {μ' δ' : D → D → ℝ≥0∞} (hsub : Γ ⊆ Γ') (hU : 1 ≤ U)
    (hΛ0 : Λ' ≠ ⊤) (hΛ1 : Λ' ≠ 0) (h' : LevelMetric M g code U V Γ' Λ' μ' δ') {y z : D} (hy : y ∈ Γ')
    (hz : z ∈ Γ') :
    hubDist Γ' (stepOf ((M.split Γ).nodeReturn Γ') μ') y z ≤ Λ' * lvlT M g U Γ y z := by
  rw [lvlT_eq_hub hsub hU hy hz, ← hubDist_const_mul hΛ1 hΛ0]
  refine hubDist_mono ?_ y z
  intro a ha b hb
  rw [← stepOf_const_mul]
  exact stepOf_mono h'.hi a ha b hb

/-- The list `c` as the image of `Fin c.length`. -/
private theorem map_finRange_getElem (c : List D) :
    (List.finRange c.length).map (fun i : Fin c.length => c[i]) = c := by
  refine List.ext_getElem (by simp) fun i h1 h2 => ?_
  simp

/-- **Hub walks over disks are a metric with (M) on a cycle.** The feasible point of a bag. -/
theorem mongeMetric_hub (hR : M.Planar) (hc : M.Connected) (hsub : Γ ⊆ Γ') (hΓ : Γ.Nonempty)
    (hS : M.SkeletonConnected Γ) (hS' : M.SkeletonConnected Γ') (hinj : Function.Injective code)
    (hU : 1 ≤ U) (hg : ∀ z, 1 ≤ g z) {Wt : ℕ} (hWt : ∀ z, g z ≤ Wt) {Λ' : ℝ≥0∞}
    {μ' δ' : D → D → ℝ≥0∞} (hΛ0 : Λ' ≠ ⊤) (hΛ1 : Λ' ≠ 0)
    (h' : LevelMetric M g code U V Γ' Λ' μ' δ') {x : D} (hx : x ∈ Γ) :
    MongeMetric (fun a b : Fin (cycOf (M.psi Γ) code x).length => cU U *
      hubDist Γ' (stepOf ((M.split Γ).nodeReturn Γ') μ')
        (cycOf (M.psi Γ) code x)[a] (cycOf (M.psi Γ) code x)[b]) := by
  classical
  set c := cycOf (M.psi Γ) code x with hcdef
  set ν := (M.split Γ).nodeReturn Γ' with hν
  have hcn : c.Nodup := cycOf_nodup _ _
  have hcm : ∀ y ∈ c, y ∈ Γ := fun y hy => mem_of_fconnect_psi hx ((mem_cycOf _).1 hy)
  have hcm' : ∀ y ∈ c, y ∈ Γ' := fun y hy => hsub (hcm y hy)
  have hlo : ∀ y ∈ Γ', ∀ z ∈ Γ', lvlT M g U Γ y z ≤ hubDist Γ' (stepOf ν μ') y z :=
    fun y hy z hz => lvlT_le_hub hsub hU h' hy hz
  have hhi : ∀ y ∈ Γ', ∀ z ∈ Γ', hubDist Γ' (stepOf ν μ') y z ≤ Λ' * lvlT M g U Γ y z :=
    fun y hy z hz => hub_le_lvlT hsub hU hΛ0 hΛ1 h' hy hz
  refine ⟨fun a => ?_, fun a b hab => ?_, fun a b l => ?_, fun a b c' f u v y z hl huv hyz => ?_⟩
  · have h0 : c[a] ∈ Γ' := hcm' _ (List.getElem_mem _)
    rw [hubDist_self_le h0, mul_zero]
  · have hne : c[a] ≠ c[b] := fun h => hab (Fin.ext ((List.Nodup.getElem_inj_iff hcn).1 h))
    have h1 := le_lvlT (M := M) (U := U) hg (hcm _ (List.getElem_mem a.2)) (hcm _
      (List.getElem_mem b.2)) hne
    have h2 := hlo _ (hcm' _ (List.getElem_mem a.2)) _ (hcm' _ (List.getElem_mem b.2))
    have hpos : (0 : ℝ≥0∞) < U := by
      exact_mod_cast (by omega : 0 < U)
    have h3 : fconnect (M.psi Γ) c[a] c[b] := by
      have ha : fconnect (M.psi Γ) x c[a] := (mem_cycOf _).1 (List.getElem_mem _)
      have hb : fconnect (M.psi Γ) x c[b] := (mem_cycOf _).1 (List.getElem_mem _)
      exact connect_trans (fconnect_sym (M.psi Γ).injective _ _ ha) hb
    have h4 := lvlT_le (U := U) hWt h3
    constructor
    · exact mul_ne_zero (cU_ne_zero hU) (lt_of_lt_of_le hpos (h1.trans h2)).ne'
    · refine ENNReal.mul_ne_top (cU_ne_top hU) (ne_top_of_le_ne_top ?_
        (hhi _ (hcm' _ (List.getElem_mem a.2)) _ (hcm' _ (List.getElem_mem b.2))))
      exact ENNReal.mul_ne_top hΛ0 (ne_top_of_le_ne_top (ENNReal.natCast_ne_top _) h4)
  · rw [← mul_add]
    gcongr
    exact hubDist_triangle _ _ _ _
  · have hreal : ∀ i : CycIdx M Γ' code, ∃ (m : ℕ) (K : RotSystem (Fin m)) (g' : Fin m → ℝ≥0∞)
        (l : Fin (cycOf (M.psi Γ') code i.1).length → Fin m), K.DiskDrawn (List.ofFn l) ∧
        ∀ a b, K.walkDist g' (K.tail (l a)) (K.tail (l b)) =
          μ' (cycOf (M.psi Γ') code i.1)[a] (cycOf (M.psi Γ') code i.1)[b] := by
      intro i
      obtain ⟨m, K, g', l, -, h2, h3⟩ := h'.real i.1 i.2.1
      exact ⟨m, K, g', l, h2, h3⟩
    choose m K g' l hKd hKw using hreal
    have hsl : [c[a], c[b], c[c'], c[f]].Sublist c := by
      have h1 := hl.map (fun i : Fin c.length => c[i])
      rwa [map_finRange_getElem] at h1
    have hmono := hubDist_monge (M := M) (μ := μ') (Γ := Γ) (Γ' := Γ')
      (l := fun i => List.ofFn (l i)) (Lst := fun i : CycIdx M Γ' code => cycOf (M.psi Γ') code i.1)
      hR hc hsub hΓ hS hS' (listsCycles hinj Γ') K g' hKd (by simp)
      (by
        intro i n hn1 hn2 n' hn3 hn4
        simp only [List.getElem_ofFn]
        exact hKw i ⟨n, hn2⟩ ⟨n', hn4⟩)
      (by
        intro i j y' z' hij hy' hz'
        have hy'm := (listsCycles hinj Γ').mem i y' hy'
        have hz'm := (listsCycles hinj Γ').mem j z' hz'
        have hnot : ¬ fconnect (M.psi Γ') y' z' := by
          intro h
          refine hij ((listsCycles hinj Γ').disj i j z' ?_ hz')
          exact (mem_cycOf _).2 (connect_trans ((mem_cycOf _).1 hy') h)
        have h1 := h'.lo y' hy'm z' hz'm
        rw [lvlT_top hR hc (hΓ.mono hsub) hS' hU hy'm hz'm hnot] at h1
        exact top_le_iff.1 h1)
      hcn hcm (fun y hy => cycOf_formPerm _ _ hy) (u := c[u]) (v := c[v]) (x := c[y]) (z := c[z])
      hsl (by
        rcases huv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact Or.inl ⟨rfl, rfl⟩
        · exact Or.inr ⟨rfl, rfl⟩) (by
        rcases hyz with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact Or.inl ⟨rfl, rfl⟩
        · exact Or.inr ⟨rfl, rfl⟩)
    rw [← mul_add, ← mul_add]
    gcongr

/-- The metric at one bag and the exact distances: the top of the recursion. -/
theorem mongeMetric_exact (hR : M.Planar) (hc : M.Connected) (hΓ : Γ.Nonempty)
    (hS : M.SkeletonConnected Γ) (hU : 1 ≤ U) (hg : ∀ z, 1 ≤ g z) {Wt : ℕ} (hWt : ∀ z, g z ≤ Wt)
    {x : D} (hx : x ∈ Γ) :
    MongeMetric (fun a b : Fin (cycOf (M.psi Γ) code x).length =>
      lvlT M g U Γ (cycOf (M.psi Γ) code x)[a] (cycOf (M.psi Γ) code x)[b]) := by
  classical
  set c := cycOf (M.psi Γ) code x with hcdef
  have hcn : c.Nodup := cycOf_nodup _ _
  have hcm : ∀ y ∈ c, y ∈ Γ := fun y hy => mem_of_fconnect_psi hx ((mem_cycOf _).1 hy)
  refine ⟨fun a => lvlT_self _, fun a b hab => ?_, fun a b l => lvlT_tri _ _ _,
    fun a b c' f u v y z hl huv hyz => ?_⟩
  · have hne : c[a] ≠ c[b] := fun h => hab (Fin.ext ((List.Nodup.getElem_inj_iff hcn).1 h))
    have h1 := le_lvlT (M := M) (U := U) hg (hcm _ (List.getElem_mem a.2)) (hcm _
      (List.getElem_mem b.2)) hne
    have hpos : (0 : ℝ≥0∞) < U := by
      exact_mod_cast (by omega : 0 < U)
    have h3 : fconnect (M.psi Γ) c[a] c[b] := by
      have ha : fconnect (M.psi Γ) x c[a] := (mem_cycOf _).1 (List.getElem_mem _)
      have hb : fconnect (M.psi Γ) x c[b] := (mem_cycOf _).1 (List.getElem_mem _)
      exact connect_trans (fconnect_sym (M.psi Γ).injective _ _ ha) hb
    have h4 := lvlT_le (U := U) hWt h3
    exact ⟨(lt_of_lt_of_le hpos h1).ne', ne_top_of_le_ne_top (ENNReal.natCast_ne_top _) h4⟩
  · have hsl : [c[a], c[b], c[c'], c[f]].Sublist c := by
      have h1 := hl.map (fun i : Fin c.length => c[i])
      rwa [map_finRange_getElem] at h1
    have hd := M.split_faceDrawn hR hc hΓ hS hcn hcm (fun y hy => cycOf_formPerm _ _ hy)
    have hm := hd.monge (fun z => (g z : ℝ≥0∞)) (u := c[u]) (v := c[v]) (w := c[y]) (z := c[z]) hsl
      (by
        rcases huv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact Or.inl ⟨rfl, rfl⟩
        · exact Or.inr ⟨rfl, rfl⟩) (by
        rcases hyz with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact Or.inl ⟨rfl, rfl⟩
        · exact Or.inr ⟨rfl, rfl⟩)
    unfold lvlT
    rw [← mul_add, ← mul_add]
    gcongr

/-- The exact distances are values at a level with `Λ = 1`. -/
theorem levelMetric_exact {C : ℕ} (hC : RealizationBox C) (hR : M.Planar) (hc : M.Connected)
    (hΓ : Γ.Nonempty) (hS : M.SkeletonConnected Γ) (hU : 1 ≤ U) (hg : ∀ z, 1 ≤ g z) {Wt : ℕ}
    (hWt : ∀ z, g z ≤ Wt)
    (hks : ∀ x ∈ Γ, C * ((cycOf (M.psi Γ) code x).length + 1) ^ 6 ≤ V) :
    LevelMetric M g code U V Γ 1 (lvlT M g U Γ) (lvlT M g U Γ) where
  lo x _ y _ := le_rfl
  hi x _ y _ := by rw [one_mul]
  val_lo x _ y _ := le_rfl
  val_hi x _ y _ := by
    calc lvlT M g U Γ x y = 1 * lvlT M g U Γ x y := (one_mul _).symm
      _ ≤ cU U * lvlT M g U Γ x y := by
        gcongr
        exact one_le_cU hU
  real x hx := by
    obtain ⟨m, K, g', l, h1, h2, h3⟩ := realizes_of_box hC
      (List.length_pos_of_mem (self_mem_cycOf (M.psi Γ) (code := code) x))
      (mongeMetric_exact hR hc hΓ hS hU hg hWt hx)
    exact ⟨m, K, g', l, h1.trans (hks x hx), h2, h3⟩

end RotSystem

/-- The labels and the metric of a bag, if there are any. -/
noncomputable def bagData (query : List ℕ → List ℕ → ℕ∞) (U s L W k : ℕ)
    (w : Fin k → Fin k → ℝ≥0∞) : (Fin k → List ℕ) × (Fin k → Fin k → ℝ≥0∞) :=
  open Classical in
  if h : ∃ p : (Fin k → List ℕ) × (Fin k → Fin k → ℝ≥0∞), BagOK query s U s L W w p.1 p.2 then
    h.choose
  else (fun _ => [], fun _ _ => ⊤)

theorem bagData_spec {query : List ℕ → List ℕ → ℕ∞} {U s L W k : ℕ} {w : Fin k → Fin k → ℝ≥0∞}
    {lab : Fin k → List ℕ} {m : Fin k → Fin k → ℝ≥0∞} (h : BagOK query s U s L W w lab m) :
    BagOK query s U s L W w (bagData query U s L W k w).1 (bagData query U s L W k w).2 := by
  have h1 : ∃ p : (Fin k → List ℕ) × (Fin k → Fin k → ℝ≥0∞), BagOK query s U s L W w p.1 p.2 :=
    ⟨(lab, m), h⟩
  unfold bagData
  rw [dite_eq_left h1]
  exact h1.choose_spec

/-- The values at a level by one call per bag on the matrix `w`. -/
noncomputable def levelVal (query : List ℕ → List ℕ → ℕ∞) (U s L W : ℕ) (f : Equiv.Perm D)
    (code : D → ℕ) (w : D → D → ℝ≥0∞) : D → D → ℝ≥0∞ :=
  deltaStep (fun k w => (bagData query U s L W k w).1) (fun a b => (decode s (query a b) : ℝ≥0∞)) f
    code w

/-- The matrix of a bag listed by `c`. -/
noncomputable def listMat (w : D → D → ℝ≥0∞) (c : List D) : Fin c.length → Fin c.length → ℝ≥0∞ :=
  fun a b => w c[a] c[b]

/-- The metric of a level, from the metrics of its bags. -/
noncomputable def levelMu (query : List ℕ → List ℕ → ℕ∞) (U s L W : ℕ) (f : Equiv.Perm D)
    (code : D → ℕ) (w : D → D → ℝ≥0∞) (x y : D) : ℝ≥0∞ :=
  atIdx (cycOf f code x) (bagData query U s L W _ (listMat w (cycOf f code x))).2 x y

section LevelVal

variable {query : List ℕ → List ℕ → ℕ∞} {U s L W : ℕ} {f : Equiv.Perm D} {code : D → ℕ}
  {w : D → D → ℝ≥0∞}

theorem levelMu_getElem (hinj : Function.Injective code) (z : D)
    (a b : Fin (cycOf f code z).length) :
    levelMu query U s L W f code w (cycOf f code z)[a] (cycOf f code z)[b] =
      (bagData query U s L W _ (listMat w (cycOf f code z))).2 a b := by
  have h : cycOf f code (cycOf f code z)[a] = cycOf f code z :=
    (cycOf_congr f hinj ((mem_cycOf f).1 (List.getElem_mem _))).symm
  unfold levelMu
  rw [h]
  exact atIdx_getElem (cycOf_nodup _ _) _ a b

theorem levelMu_of_not (x y : D) (h : ¬ fconnect f x y) :
    levelMu query U s L W f code w x y = ⊤ :=
  atIdx_of_not_mem _ _ fun h' => h ((mem_cycOf f).1 h')

theorem levelVal_self (x : D) : levelVal query U s L W f code w x x = 0 := by
  simp [levelVal, deltaStep]

theorem levelVal_of_not {x y : D} (h : ¬ fconnect f x y) :
    levelVal query U s L W f code w x y = ⊤ := by
  have hne : x ≠ y := by
    rintro rfl
    exact h (connect_refl x)
  simp [levelVal, deltaStep, hne, h]

theorem levelVal_getElem (hinj : Function.Injective code) (z : D)
    (a b : Fin (cycOf f code z).length) (hne : (cycOf f code z)[a] ≠ (cycOf f code z)[b]) :
    levelVal query U s L W f code w (cycOf f code z)[a] (cycOf f code z)[b] =
      (decode s (query ((bagData query U s L W _ (listMat w (cycOf f code z))).1 a)
        ((bagData query U s L W _ (listMat w (cycOf f code z))).1 b)) : ℝ≥0∞) := by
  have ha : fconnect f z (cycOf f code z)[a] := (mem_cycOf f).1 (List.getElem_mem _)
  have hb : fconnect f z (cycOf f code z)[b] := (mem_cycOf f).1 (List.getElem_mem _)
  have h : cycOf f code (cycOf f code z)[a] = cycOf f code z := (cycOf_congr f hinj ha).symm
  have hf : fconnect f (cycOf f code z)[a] (cycOf f code z)[b] :=
    connect_trans (fconnect_sym f.injective _ _ ha) hb
  classical
  unfold levelVal deltaStep
  rw [ite_eq_right hne, ite_eq_left hf, h]
  beta_reduce
  rw [labOn_getElem _ _ (cycOf_nodup _ _) a, labOn_getElem _ _ (cycOf_nodup _ _) b]
  rfl

end LevelVal

namespace RotSystem

variable {M : RotSystem D} {g : D → ℕ} {code : D → ℕ} {U V : ℕ} {Γ Γ' : Finset D}

/-- The bound for the words of a level. -/
abbrev bagLen (Cl cl U s B : ℕ) : ℕ := Cl * Nat.log 2 (s + 2 * s * B + 2) ^ cl * U

/-- The bound for the size of a word of a level. -/
abbrev bagWord (cl s B : ℕ) : ℕ := (s + 2 * s * B + 2) ^ cl

/-- **One level.** Values `δ'` at a larger set give values at `Γ` by one call per bag on the least
total weights of hub walks over `δ'`, and the factor `Λ` grows by `((U + 4) / U) ^ 2`. -/
theorem levelMetric_step {C Cl cl s B Wt : ℕ} (hC : RealizationBox C)
    {query : List ℕ → List ℕ → ℕ∞} (hq : LabelQuery Cl cl U query) (hR : M.Planar)
    (hc : M.Connected) (hsub : Γ ⊆ Γ') (hΓ : Γ.Nonempty) (hS : M.SkeletonConnected Γ)
    (hS' : M.SkeletonConnected Γ') (hinj : Function.Injective code) (hU : 1 ≤ U)
    (hg : ∀ z, 1 ≤ g z) (hWt : ∀ z, g z ≤ Wt) (hs : 1 ≤ s) (hB : 1 ≤ B)
    (hks : ∀ x ∈ Γ, C * ((cycOf (M.psi Γ) code x).length + 1) ^ 6 ≤ s)
    (hBig : 2 * (U * Fintype.card D * Wt) ≤ B) {Λ' : ℝ≥0∞} {μ' δ' : D → D → ℝ≥0∞} (hΛ1 : 1 ≤ Λ')
    (hΛ2 : cU U * Λ' ≤ 2) (h' : LevelMetric M g code U V Γ' Λ' μ' δ') :
    (∃ μ, LevelMetric M g code U s Γ (cU U * (cU U * Λ')) μ
      (levelVal query U s (bagLen Cl cl U s B) (bagWord cl s B) (M.psi Γ) code
        (hubDist Γ' (stepOf ((M.split Γ).nodeReturn Γ') δ')))) ∧
    ∀ x ∈ Γ, ∀ a,
      ((bagData query U s (bagLen Cl cl U s B) (bagWord cl s B) _
        (listMat (hubDist Γ' (stepOf ((M.split Γ).nodeReturn Γ') δ'))
          (cycOf (M.psi Γ) code x))).1 a).length ≤ bagLen Cl cl U s B ∧
      ∀ w ∈ (bagData query U s (bagLen Cl cl U s B) (bagWord cl s B) _
        (listMat (hubDist Γ' (stepOf ((M.split Γ).nodeReturn Γ') δ'))
          (cycOf (M.psi Γ) code x))).1 a, w < bagWord cl s B := by
  classical
  set ν := (M.split Γ).nodeReturn Γ' with hν
  set w := hubDist Γ' (stepOf ν δ') with hw
  set d0 := hubDist Γ' (stepOf ν μ') with hd0
  set L := bagLen Cl cl U s B with hL
  set W := bagWord cl s B with hW
  have hΛT : Λ' ≠ ⊤ := by
    intro h
    rw [h, ENNReal.mul_top (cU_ne_zero hU)] at hΛ2
    exact absurd hΛ2 (by simp)
  have hΛ0 : Λ' ≠ 0 := (lt_of_lt_of_le one_pos hΛ1).ne'
  have h1 : ∀ y z, d0 y z ≤ w y z := fun y z => hubDist_mono (stepOf_mono h'.val_lo) y z
  have h2 : ∀ y z, w y z ≤ cU U * d0 y z := by
    intro y z
    rw [hd0, ← hubDist_const_mul (cU_ne_zero hU) (cU_ne_top hU)]
    refine hubDist_mono ?_ y z
    intro a ha b hb
    rw [← stepOf_const_mul]
    exact stepOf_mono h'.val_hi a ha b hb
  have key : ∀ x ∈ Γ, BagOK query s U s L W (listMat w (cycOf (M.psi Γ) code x))
      (bagData query U s L W _ (listMat w (cycOf (M.psi Γ) code x))).1
      (bagData query U s L W _ (listMat w (cycOf (M.psi Γ) code x))).2 := by
    intro x hx
    set c := cycOf (M.psi Γ) code x with hcdef
    have hcn : c.Nodup := cycOf_nodup _ _
    have hcm : ∀ y ∈ c, y ∈ Γ := fun y hy => mem_of_fconnect_psi hx ((mem_cycOf _).1 hy)
    have hk : 1 ≤ c.length := List.length_pos_of_mem (self_mem_cycOf _ x)
    obtain ⟨lab, hlab⟩ := exists_bagOK (w := listMat w c)
      (m := fun a b => cU U * d0 c[a] c[b]) hC hq hU hs hB hk (hks x hx)
      (mongeMetric_hub hR hc hsub hΓ hS hS' hinj hU hg hWt hΛT hΛ0 h' hx)
      (fun a b => h2 _ _)
      (fun a b => by
        rw [← mul_assoc, mul_cU hU]
        gcongr
        exact h1 _ _)
      (fun a b hab => by
        have hne : c[a] ≠ c[b] := fun h => hab (Fin.ext ((List.Nodup.getElem_inj_iff hcn).1 h))
        have ha := hcm _ (List.getElem_mem a.2)
        have hb := hcm _ (List.getElem_mem b.2)
        have h3 := le_lvlT (M := M) (U := U) hg ha hb hne
        have h4 := lvlT_le_hub hsub hU h' (hsub ha) (hsub hb)
        constructor
        · calc (U : ℝ≥0∞) ≤ d0 c[a] c[b] := h3.trans h4
            _ = 1 * d0 c[a] c[b] := (one_mul _).symm
            _ ≤ cU U * d0 c[a] c[b] := by
              gcongr
              exact one_le_cU hU
        · have h5 := hub_le_lvlT hsub hU hΛT hΛ0 h' (hsub ha) (hsub hb)
          have h6 : fconnect (M.psi Γ) c[a] c[b] := by
            have ha' : fconnect (M.psi Γ) x c[a] := (mem_cycOf _).1 (List.getElem_mem _)
            have hb' : fconnect (M.psi Γ) x c[b] := (mem_cycOf _).1 (List.getElem_mem _)
            exact connect_trans (fconnect_sym (M.psi Γ).injective _ _ ha') hb'
          have h7 := lvlT_le (U := U) hWt h6
          calc cU U * d0 c[a] c[b] ≤ cU U * (Λ' * ((U * Fintype.card D * Wt : ℕ) : ℝ≥0∞)) := by
                refine mul_le_mul_right ?_ _
                exact h5.trans (mul_le_mul_right h7 _)
            _ = (cU U * Λ') * ((U * Fintype.card D * Wt : ℕ) : ℝ≥0∞) := by ring
            _ ≤ 2 * ((U * Fintype.card D * Wt : ℕ) : ℝ≥0∞) := by gcongr
            _ ≤ (B : ℝ≥0∞) := by
              exact_mod_cast hBig)
    exact bagData_spec hlab
  have hpair : ∀ x ∈ Γ, ∀ a b : Fin (cycOf (M.psi Γ) code x).length,
      lvlT M g U Γ (cycOf (M.psi Γ) code x)[a] (cycOf (M.psi Γ) code x)[b] ≤
        levelMu query U s L W (M.psi Γ) code w (cycOf (M.psi Γ) code x)[a]
          (cycOf (M.psi Γ) code x)[b] ∧
      levelMu query U s L W (M.psi Γ) code w (cycOf (M.psi Γ) code x)[a]
          (cycOf (M.psi Γ) code x)[b] ≤ cU U * (cU U * Λ') *
        lvlT M g U Γ (cycOf (M.psi Γ) code x)[a] (cycOf (M.psi Γ) code x)[b] ∧
      levelMu query U s L W (M.psi Γ) code w (cycOf (M.psi Γ) code x)[a]
          (cycOf (M.psi Γ) code x)[b] ≤
        levelVal query U s L W (M.psi Γ) code w (cycOf (M.psi Γ) code x)[a]
          (cycOf (M.psi Γ) code x)[b] ∧
      levelVal query U s L W (M.psi Γ) code w (cycOf (M.psi Γ) code x)[a]
          (cycOf (M.psi Γ) code x)[b] ≤ cU U *
        levelMu query U s L W (M.psi Γ) code w (cycOf (M.psi Γ) code x)[a]
          (cycOf (M.psi Γ) code x)[b] := by
    intro x hx a b
    have hk := key x hx
    have hcm : ∀ y ∈ cycOf (M.psi Γ) code x, y ∈ Γ :=
      fun y hy => mem_of_fconnect_psi hx ((mem_cycOf _).1 hy)
    have ha := hcm _ (List.getElem_mem a.2)
    have hb := hcm _ (List.getElem_mem b.2)
    rw [levelMu_getElem hinj]
    refine ⟨?_, ?_, ?_⟩
    · exact (lvlT_le_hub hsub hU h' (hsub ha) (hsub hb)).trans ((h1 _ _).trans (hk.lo a b))
    · refine (le_cU_mul hU (hk.hi a b)).trans ?_
      calc cU U * listMat w (cycOf (M.psi Γ) code x) a b
          ≤ cU U * (cU U * d0 (cycOf (M.psi Γ) code x)[a] (cycOf (M.psi Γ) code x)[b]) :=
            mul_le_mul_right (h2 _ _) _
        _ ≤ cU U * (cU U * (Λ' * lvlT M g U Γ (cycOf (M.psi Γ) code x)[a]
              (cycOf (M.psi Γ) code x)[b])) :=
            mul_le_mul_right (mul_le_mul_right
              (hub_le_lvlT hsub hU hΛT hΛ0 h' (hsub ha) (hsub hb)) _) _
        _ = _ := by ring
    · by_cases hab : a = b
      · subst hab
        rw [levelVal_self, hk.monge.self a]
        exact ⟨zero_le, by simp⟩
      · have hne : (cycOf (M.psi Γ) code x)[a] ≠ (cycOf (M.psi Γ) code x)[b] := fun h =>
          hab (Fin.ext ((List.Nodup.getElem_inj_iff (cycOf_nodup _ _)).1 h))
        rw [levelVal_getElem hinj x a b hne]
        exact ⟨hk.val_lo a b hab, le_cU_mul hU (hk.val_hi a b hab)⟩
  have hget : ∀ x y, fconnect (M.psi Γ) x y → ∃ a b : Fin (cycOf (M.psi Γ) code x).length,
      (cycOf (M.psi Γ) code x)[a] = x ∧ (cycOf (M.psi Γ) code x)[b] = y := by
    intro x y hxy
    obtain ⟨a, ha, h3⟩ := List.getElem_of_mem (self_mem_cycOf (M.psi Γ) (code := code) x)
    obtain ⟨b, hb, h4⟩ := List.getElem_of_mem ((mem_cycOf (M.psi Γ) (code := code)).2 hxy)
    exact ⟨⟨a, ha⟩, ⟨b, hb⟩, h3, h4⟩
  have hfacts : ∀ x ∈ Γ, ∀ y, fconnect (M.psi Γ) x y →
      lvlT M g U Γ x y ≤ levelMu query U s L W (M.psi Γ) code w x y ∧
      levelMu query U s L W (M.psi Γ) code w x y ≤ cU U * (cU U * Λ') * lvlT M g U Γ x y ∧
      levelMu query U s L W (M.psi Γ) code w x y ≤ levelVal query U s L W (M.psi Γ) code w x y ∧
      levelVal query U s L W (M.psi Γ) code w x y ≤
        cU U * levelMu query U s L W (M.psi Γ) code w x y := by
    intro x hx y hxy
    obtain ⟨a, b, ha, hb⟩ := hget x y hxy
    have h3 := hpair x hx a b
    rwa [ha, hb] at h3
  have hne : cU U * (cU U * Λ') ≠ 0 := mul_ne_zero (cU_ne_zero hU) (mul_ne_zero (cU_ne_zero hU) hΛ0)
  refine ⟨⟨levelMu query U s L W (M.psi Γ) code w, ?_⟩, fun x hx a =>
    ⟨(key x hx).len a, (key x hx).word a⟩⟩
  refine ⟨fun x hx y hy => ?_, fun x hx y hy => ?_, fun x hx y hy => ?_, fun x hx y hy => ?_,
    fun x hx => ?_⟩
  · by_cases hxy : fconnect (M.psi Γ) x y
    · exact (hfacts x hx y hxy).1
    · rw [levelMu_of_not _ _ hxy]
      exact le_top
  · by_cases hxy : fconnect (M.psi Γ) x y
    · exact (hfacts x hx y hxy).2.1
    · rw [lvlT_top hR hc hΓ hS hU hx hy hxy, ENNReal.mul_top hne]
      exact le_top
  · by_cases hxy : fconnect (M.psi Γ) x y
    · exact (hfacts x hx y hxy).2.2.1
    · rw [levelVal_of_not hxy]
      exact le_top
  · by_cases hxy : fconnect (M.psi Γ) x y
    · exact (hfacts x hx y hxy).2.2.2
    · rw [levelMu_of_not _ _ hxy, ENNReal.mul_top (cU_ne_zero hU)]
      exact le_top
  · have h3 : (fun a b : Fin (cycOf (M.psi Γ) code x).length =>
        levelMu query U s L W (M.psi Γ) code w (cycOf (M.psi Γ) code x)[a]
          (cycOf (M.psi Γ) code x)[b]) =
        (bagData query U s L W _ (listMat w (cycOf (M.psi Γ) code x))).2 := by
      funext a b
      exact levelMu_getElem hinj x a b
    rw [h3]
    exact (key x hx).real

/-! ### All levels -/

variable (M g code U) in
/-- The values at the levels `Γs 0 ⊇ Γs 1 ⊇ ...`, from the exact distances at `Γs 0`. -/
noncomputable def valSeq (query : List ℕ → List ℕ → ℕ∞) (s L W : ℕ) (Γs : ℕ → Finset D) :
    ℕ → D → D → ℝ≥0∞
  | 0 => lvlT M g U (Γs 0)
  | i + 1 => levelVal query U s L W (M.psi (Γs (i + 1))) code
      (hubDist (Γs i) (stepOf ((M.split (Γs (i + 1))).nodeReturn (Γs i))
        (valSeq query s L W Γs i)))

/-- **All levels.** The values at step `i` from the top have factor `((U + 4) / U) ^ (2 * i)`. -/
theorem levelMetric_seq {C Cl cl s B Wt n : ℕ} (hC : RealizationBox C)
    {query : List ℕ → List ℕ → ℕ∞} (hq : LabelQuery Cl cl U query) (hR : M.Planar)
    (hc : M.Connected) (Γs : ℕ → Finset D) (hsub : ∀ i, i < n → Γs (i + 1) ⊆ Γs i)
    (hΓ : ∀ i, i ≤ n → (Γs i).Nonempty) (hS : ∀ i, i ≤ n → M.SkeletonConnected (Γs i))
    (hinj : Function.Injective code) (hU : 1 ≤ U) (hg : ∀ z, 1 ≤ g z) (hWt : ∀ z, g z ≤ Wt)
    (hs : 1 ≤ s) (hB : 1 ≤ B)
    (hks : ∀ i, i ≤ n → ∀ x ∈ Γs i, C * ((cycOf (M.psi (Γs i)) code x).length + 1) ^ 6 ≤ s)
    (hBig : 2 * (U * Fintype.card D * Wt) ≤ B) (hcn : cU U ^ (2 * n + 1) ≤ 2) (i : ℕ) (hi : i ≤ n) :
    ∃ μ, LevelMetric M g code U s (Γs i) (cU U ^ (2 * i)) μ
      (valSeq M g code U query s (bagLen Cl cl U s B) (bagWord cl s B) Γs i) := by
  induction i with
  | zero =>
    refine ⟨lvlT M g U (Γs 0), ?_⟩
    simp only [mul_zero, pow_zero]
    exact levelMetric_exact hC hR hc (hΓ 0 hi) (hS 0 hi) hU hg hWt (hks 0 hi)
  | succ i ih =>
    obtain ⟨μ', h'⟩ := ih (by omega)
    have h1 : 1 ≤ cU U ^ (2 * i) := one_le_pow₀ (one_le_cU hU)
    have h2 : cU U * cU U ^ (2 * i) ≤ 2 := by
      refine le_trans ?_ hcn
      rw [← pow_succ']
      exact pow_le_pow_right₀ (one_le_cU hU) (by omega)
    obtain ⟨⟨μ, h3⟩, -⟩ := levelMetric_step hC hq hR hc (hsub i (by omega)) (hΓ _ hi) (hS _ hi)
      (hS _ (by omega)) hinj hU hg hWt hs hB (hks _ hi) hBig h1 h2 h'
    refine ⟨μ, ?_⟩
    have h4 : cU U ^ (2 * (i + 1)) = cU U * (cU U * cU U ^ (2 * i)) := by ring
    rw [h4]
    exact h3

/-! ### The factor over all levels -/

/-- `(1 + x) ^ n ≤ 1 + 2 * n * x` as long as `2 * n * x ≤ 1`. -/
theorem one_add_pow_le (x : ℝ≥0∞) (n : ℕ) (h : 2 * (n : ℝ≥0∞) * x ≤ 1) :
    (1 + x) ^ n ≤ 1 + 2 * (n : ℝ≥0∞) * x := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h1 : 2 * (n : ℝ≥0∞) * x ≤ 1 := by
      refine le_trans ?_ h
      gcongr
      simp
    calc (1 + x) ^ (n + 1) = (1 + x) ^ n * (1 + x) := pow_succ _ _
      _ ≤ (1 + 2 * (n : ℝ≥0∞) * x) * (1 + x) := mul_le_mul_left (ih h1) _
      _ = 1 + 2 * (n : ℝ≥0∞) * x + x + (2 * (n : ℝ≥0∞) * x) * x := by ring
      _ ≤ 1 + 2 * (n : ℝ≥0∞) * x + x + 1 * x := by gcongr
      _ = 1 + 2 * ((n + 1 : ℕ) : ℝ≥0∞) * x := by
        push_cast
        ring

theorem cU_eq (hU : 1 ≤ U) : cU U = 1 + 4 * (U : ℝ≥0∞)⁻¹ := by
  unfold cU
  rw [add_mul, ENNReal.mul_inv_cancel (natU_ne_zero hU) (ENNReal.natCast_ne_top U)]

/-- The factor after `n` steps is at most `1 + 8 * n / U` if `8 * n ≤ U`. -/
theorem pow_cU_le (hU : 1 ≤ U) (n : ℕ) (h : 8 * n ≤ U) :
    cU U ^ n ≤ 1 + 8 * (n : ℝ≥0∞) * (U : ℝ≥0∞)⁻¹ := by
  have h0 : (8 * (n : ℝ≥0∞)) * (U : ℝ≥0∞)⁻¹ ≤ 1 := by
    calc (8 * (n : ℝ≥0∞)) * (U : ℝ≥0∞)⁻¹ ≤ (U : ℝ≥0∞) * (U : ℝ≥0∞)⁻¹ := by
          gcongr
          exact_mod_cast h
      _ = 1 := ENNReal.mul_inv_cancel (natU_ne_zero hU) (ENNReal.natCast_ne_top U)
  have h1 : 2 * (n : ℝ≥0∞) * (4 * (U : ℝ≥0∞)⁻¹) = 8 * (n : ℝ≥0∞) * (U : ℝ≥0∞)⁻¹ := by ring
  rw [cU_eq hU]
  have h2 := one_add_pow_le (4 * (U : ℝ≥0∞)⁻¹) n (by rw [h1]; exact h0)
  rwa [h1] at h2

/-- The bound needed along the levels. -/
theorem pow_cU_le_two (hU : 1 ≤ U) (n : ℕ) (h : 8 * n ≤ U) : cU U ^ n ≤ 2 := by
  have h0 : (8 * (n : ℝ≥0∞)) * (U : ℝ≥0∞)⁻¹ ≤ 1 := by
    calc (8 * (n : ℝ≥0∞)) * (U : ℝ≥0∞)⁻¹ ≤ (U : ℝ≥0∞) * (U : ℝ≥0∞)⁻¹ := by
          gcongr
          exact_mod_cast h
      _ = 1 := ENNReal.mul_inv_cancel (natU_ne_zero hU) (ENNReal.natCast_ne_top U)
  calc cU U ^ n ≤ 1 + 8 * (n : ℝ≥0∞) * (U : ℝ≥0∞)⁻¹ := pow_cU_le hU n h
    _ ≤ 1 + 1 := by gcongr
    _ = 2 := one_add_one_eq_two

end RotSystem


end Step

end SsspFlow
