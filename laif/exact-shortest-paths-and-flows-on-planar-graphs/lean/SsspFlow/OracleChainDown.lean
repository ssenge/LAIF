import SsspFlow.OracleChainCount

/-!
# Runs down the parent chains of an oracle

With length `g a` on the arc from a node `a` to each child `b`, that is, to each `b` whose parent is
`a`, and `⊤` on every other arc, a walk of finite length goes down the parent chains, and its length
is the sum of `g` over its nodes but the last. So one more run of the oracle from a set of sources
gives each node the least such sum from a source above it on its chain. When exactly one source lies
above the node, the run gives the sum of `g` over the nodes between that source and the node, and
with `g` the indicator of a flag, the node learns whether a flagged node lies there.

* `Net.downLenW`: the lengths `g a` on the arcs from a node `a` to its children.
* `Net.walk_downW`: a walk of finite length goes down the parents, with the sum of `g` as length.
* `Net.ExactSpec.walk_down`: the chain from a node up to a node above it, walked down, is such a walk.
* `Net.ExactSpec.dsrcTop_downW`: the distance from the sources is the least sum of `g` along the
  parent steps from the node up to a source.
* `Net.ExactSpec.dsrcTop_down_sum`, `Net.ExactSpec.dsrcTop_down_flag_eq_zero`: the distance for a
  single source above the node, and for the indicator of a flag.
* `Net.parSteps_add`: valid parent steps compose.
* `Net.ExactSpec.first_iff`, `Net.ExactSpec.down_none_iff`, `Net.ExactSpec.last_iff`: after a
  counting run up the chains and a run down from the first node flagged by `F0`, the first node
  flagged by `F0` and the last node below it flagged by `F1` each know that they are these nodes.
-/

set_option autoImplicit false

namespace SsspFlow

namespace Congest

open scoped ENNReal

variable {V : Type} [Fintype V] [DecidableEq V]

/-- The lengths `g a` on the arc from each node `a` to each of its children, `⊤` elsewhere. -/
def Net.downLenW (r : V → ℕ∞ × Option V) (g : V → ℕ∞) (a b : V) : ℕ∞ :=
  if (r b).2 = some a then g a else ⊤

/-- **Walks go down the parents.** A walk of finite length for `downLenW` from `a` to `b` reaches
`a` from `b` by valid parent steps, and its length is the sum of `g` over the nodes above `b` up to
`a`. -/
theorem Net.walk_downW {N : Net V} {r : V → ℕ∞ × Option V} {g : V → ℕ∞} :
    ∀ {a b : V} (q : SsspFlow.Walk N.G.Adj a b), q.wt (lenTop (Net.downLenW r g)) ≠ ⊤ →
      ∃ j, Net.ParSteps r b j ∧ (Net.parOf r)^[j] b = a ∧
        q.wt (lenTop (Net.downLenW r g)) = ((∑ l ∈ Finset.range j, g ((Net.parOf r)^[l + 1] b) : ℕ∞) : ℝ≥0∞)
  | _, _, .nil _, _ => ⟨0, fun k hk => absurd hk (Nat.not_lt_zero k), rfl, by simp [SsspFlow.Walk.wt]⟩
  | a, b, .cons (b := a') _ q, hq => by
    rw [SsspFlow.Walk.wt_cons] at hq ⊢
    have h1 : lenTop (Net.downLenW r g) a a' ≠ ⊤ := fun e => hq (by rw [e, top_add])
    have h2 : (r a').2 = some a := by
      by_contra hc
      exact h1 (by simp [lenTop, Net.downLenW, hc])
    obtain ⟨j, hj, he, hw⟩ := Net.walk_downW q (fun e => hq (by rw [e, add_top]))
    have hpar : (Net.parOf r)^[j + 1] b = a := by
      rw [Function.iterate_succ_apply', he]
      exact Net.parOf_some h2
    refine ⟨j + 1, fun k hk => ?_, hpar, ?_⟩
    · rcases Nat.lt_or_ge k j with hkj | hkj
      · exact hj k hkj
      · obtain rfl : k = j := by omega
        rw [he, hpar]
        exact h2
    · rw [hw, Finset.sum_range_succ, ENat.toENNReal_add, hpar, add_comm]
      simp [lenTop, Net.downLenW, h2]

/-- **The chain walked down.** Along `j` valid parent steps from `b` there is a walk from
`parOf^[j] b` down to `b` whose length is the sum of `g` over the nodes above `b`. -/
theorem Net.ExactSpec.walk_down {N : Net V} {ℓ : V → V → ℕ∞} {φ : V → ℕ∞} {r : V → ℕ∞ × Option V}
    (h : N.ExactSpec ℓ φ r) (g : V → ℕ∞) :
    ∀ (j : ℕ) (b : V), Net.ParSteps r b j → ∃ q : SsspFlow.Walk N.G.Adj ((Net.parOf r)^[j] b) b,
      q.wt (lenTop (Net.downLenW r g)) = ((∑ l ∈ Finset.range j, g ((Net.parOf r)^[l + 1] b) : ℕ∞) : ℝ≥0∞)
  | 0, b, _ => ⟨.nil b, by simp [SsspFlow.Walk.wt]⟩
  | j + 1, b, hs => by
    obtain ⟨q, hq⟩ := h.walk_down g j b fun k hk => hs k (by omega)
    have h0 : (r ((Net.parOf r)^[j] b)).2 = some ((Net.parOf r)^[j + 1] b) := hs j (by omega)
    refine ⟨.cons (h.adj_par h0).symm q, ?_⟩
    rw [SsspFlow.Walk.wt_cons, hq, Finset.sum_range_succ, ENat.toENNReal_add, add_comm]
    simp [lenTop, Net.downLenW, h0]

open Classical in
/-- **Sums down the chains.** With length `g a` on the arcs from each node `a` to its children and
offset `0` at the sources, the distance at `w` is the least sum of `g` over the nodes above `w` up to
a source reached from `w` by valid parent steps. -/
theorem Net.ExactSpec.dsrcTop_downW {N : Net V} {ℓ : V → V → ℕ∞} {φ : V → ℕ∞} {r : V → ℕ∞ × Option V}
    (h : N.ExactSpec ℓ φ r) (g : V → ℕ∞) (isX : V → Bool) (w : V) :
    N.dsrcTop (Net.downLenW r g) (Net.markOffB isX) w =
      ⨅ j, ⨅ (_ : Net.ParSteps r w j ∧ isX ((Net.parOf r)^[j] w) = true),
        ((∑ l ∈ Finset.range j, g ((Net.parOf r)^[l + 1] w) : ℕ∞) : ℝ≥0∞) := by
  unfold Net.dsrcTop dsrc
  apply le_antisymm
  · refine le_iInf fun j => le_iInf fun ⟨hs, hx⟩ => ?_
    obtain ⟨q, hq⟩ := h.walk_down g j w hs
    refine iInf_le_of_le ((Net.parOf r)^[j] w) ?_
    have h0 : offTop (Net.markOffB isX) ((Net.parOf r)^[j] w) = 0 := by
      simp [offTop, Net.markOffB, hx]
    rw [h0, zero_add]
    unfold dist
    exact iInf₂_le_of_le q (fun _ _ => Set.mem_univ _) hq.le
  · refine le_iInf fun a => ?_
    by_cases ha : isX a = true
    · have h0 : offTop (Net.markOffB isX) a = 0 := by simp [offTop, Net.markOffB, ha]
      rw [h0, zero_add]
      unfold dist
      refine le_iInf₂ fun q _ => ?_
      by_cases hq : q.wt (lenTop (Net.downLenW r g)) = ⊤
      · rw [hq]
        exact le_top
      · obtain ⟨j, hs, hx, hw⟩ := Net.walk_downW q hq
        rw [hw]
        exact iInf_le_of_le j (iInf_le_of_le ⟨hs, hx ▸ ha⟩ le_rfl)
    · simp [offTop, Net.markOffB, ha]

open Classical in
/-- **A single source above.** If the node `J` valid steps above `w` is a source and no other node
reached from `w` by valid parent steps is one, the distance at `w` is the sum of `g` over the nodes
`1, …, J` steps above `w`. -/
theorem Net.ExactSpec.dsrcTop_down_sum {N : Net V} {ℓ : V → V → ℕ∞} {φ : V → ℕ∞}
    {r : V → ℕ∞ × Option V} (h : N.ExactSpec ℓ φ r) (g : V → ℕ∞) (isX : V → Bool) {w : V} {J : ℕ}
    (hJ : Net.ParSteps r w J) (hXJ : isX ((Net.parOf r)^[J] w) = true)
    (hX : ∀ j, Net.ParSteps r w j → isX ((Net.parOf r)^[j] w) = true → j = J) :
    N.dsrcTop (Net.downLenW r g) (Net.markOffB isX) w =
      ((∑ l ∈ Finset.range J, g ((Net.parOf r)^[l + 1] w) : ℕ∞) : ℝ≥0∞) := by
  rw [h.dsrcTop_downW]
  apply le_antisymm
  · exact iInf_le_of_le J (iInf_le_of_le ⟨hJ, hXJ⟩ le_rfl)
  · refine le_iInf fun j => le_iInf fun ⟨hs, hx⟩ => ?_
    obtain rfl := hX j hs hx
    exact le_rfl

open Classical in
/-- **No flag between.** For a single source `J` valid steps above `w` and the indicator of a flag
`P` as lengths on the arcs to the children, the distance at `w` is `0` exactly when no node
`1, …, J` steps above `w` is flagged. -/
theorem Net.ExactSpec.dsrcTop_down_flag_eq_zero {N : Net V} {ℓ : V → V → ℕ∞} {φ : V → ℕ∞}
    {r : V → ℕ∞ × Option V} (h : N.ExactSpec ℓ φ r) (P : V → Prop) (isX : V → Bool) {w : V} {J : ℕ}
    (hJ : Net.ParSteps r w J) (hXJ : isX ((Net.parOf r)^[J] w) = true)
    (hX : ∀ j, Net.ParSteps r w j → isX ((Net.parOf r)^[j] w) = true → j = J) :
    N.dsrcTop (Net.downLenW r fun a => if P a then 1 else 0) (Net.markOffB isX) w = 0 ↔
      ∀ l < J, ¬ P ((Net.parOf r)^[l + 1] w) := by
  rw [h.dsrcTop_down_sum _ isX hJ hXJ hX]
  rw [← ENat.toENNReal_zero, ENat.toENNReal_inj, Finset.sum_eq_zero_iff]
  refine forall_congr' fun l => ?_
  rw [Finset.mem_range]
  refine imp_congr_right fun _ => ?_
  split_ifs with hP
  · exact iff_of_false one_ne_zero (not_not.2 hP)
  · exact iff_of_true rfl hP

omit [Fintype V] [DecidableEq V] in
/-- Valid parent steps compose: `i + j` steps from `v` are valid exactly when `i` steps from `v` and
then `j` steps from the node reached are. -/
theorem Net.parSteps_add {r : V → ℕ∞ × Option V} {v : V} {i j : ℕ} :
    Net.ParSteps r v (i + j) ↔ Net.ParSteps r v i ∧ Net.ParSteps r ((Net.parOf r)^[i] v) j := by
  have e : ∀ m, (Net.parOf r)^[m] ((Net.parOf r)^[i] v) = (Net.parOf r)^[i + m] v := fun m => by
    rw [← Function.iterate_add_apply, Nat.add_comm]
  constructor
  · intro hs
    refine ⟨fun k hk => hs k (by omega), fun k hk => ?_⟩
    rw [e, e (k + 1), ← Nat.add_assoc]
    exact hs (i + k) (by omega)
  · rintro ⟨h1, h2⟩ k hk
    rcases Nat.lt_or_ge k i with hki | hki
    · exact h1 k hki
    · obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hki
      have := h2 m (by omega)
      rwa [e, e (m + 1), ← Nat.add_assoc] at this

open Classical in
/-- **The first flagged node knows itself.** Let the chains of distinct targets not meet, and let the
node `ia` valid steps above a target `v` be the first one flagged by `F0`. After the counting run for
the indicator of `F0`, a node `n` valid steps above `v` is flagged with distance `0` exactly when
`n = ia`. -/
theorem Net.ExactSpec.first_iff {N : Net V} {ℓ : V → V → ℕ∞} {φ : V → ℕ∞} {r : V → ℕ∞ × Option V}
    (h : N.ExactSpec ℓ φ r) (F0 : V → Prop) (isT : V → Bool)
    (hT : ∀ t t' i i', isT t = true → isT t' = true → Net.ParSteps r t i → Net.ParSteps r t' i' →
      (Net.parOf r)^[i] t = (Net.parOf r)^[i'] t' → t = t')
    {v : V} (hv : isT v = true) {ia : ℕ} (h0 : F0 ((Net.parOf r)^[ia] v))
    (h0' : ∀ l < ia, ¬ F0 ((Net.parOf r)^[l] v)) {n : ℕ} (hn : Net.ParSteps r v n) :
    decide (F0 ((Net.parOf r)^[n] v) ∧ N.dsrcTop (Net.markLenW r fun a => if F0 a then 1 else 0)
      (Net.markOffB isT) ((Net.parOf r)^[n] v) = 0) = true ↔ n = ia := by
  rw [decide_eq_true_iff, h.dsrcTop_flag_eq_zero F0 isT hT hv hn]
  constructor
  · rintro ⟨hF, hb⟩
    rcases lt_trichotomy n ia with hl | rfl | hl
    · exact absurd hF (h0' n hl)
    · rfl
    · exact absurd h0 (hb ia hl)
  · rintro rfl
    exact ⟨h0, h0'⟩

open Classical in
/-- **No flag up to the first node.** Under the conditions of `first_iff`, take as sources the nodes
flagged by `F0` with distance `0` in the counting run. For the indicator of `F1` as lengths on the
arcs to the children, the distance at the node `i ≤ ia` valid steps above `v` is `0` exactly when no
node `i + 1, …, ia` steps above `v` is flagged by `F1`. -/
theorem Net.ExactSpec.down_none_iff {N : Net V} {ℓ : V → V → ℕ∞} {φ : V → ℕ∞} {r : V → ℕ∞ × Option V}
    (h : N.ExactSpec ℓ φ r) (F0 F1 : V → Prop) (isT : V → Bool)
    (hT : ∀ t t' i i', isT t = true → isT t' = true → Net.ParSteps r t i → Net.ParSteps r t' i' →
      (Net.parOf r)^[i] t = (Net.parOf r)^[i'] t' → t = t')
    {v : V} (hv : isT v = true) {ia : ℕ} (hia : Net.ParSteps r v ia) (h0 : F0 ((Net.parOf r)^[ia] v))
    (h0' : ∀ l < ia, ¬ F0 ((Net.parOf r)^[l] v)) {i : ℕ} (hi : i ≤ ia) :
    N.dsrcTop (Net.downLenW r fun a => if F1 a then 1 else 0)
      (Net.markOffB fun a => decide (F0 a ∧ N.dsrcTop (Net.markLenW r fun a => if F0 a then 1 else 0)
        (Net.markOffB isT) a = 0)) ((Net.parOf r)^[i] v) = 0 ↔
      ∀ l, i < l → l ≤ ia → ¬ F1 ((Net.parOf r)^[l] v) := by
  have e : ∀ m, (Net.parOf r)^[m] ((Net.parOf r)^[i] v) = (Net.parOf r)^[i + m] v := fun m => by
    rw [← Function.iterate_add_apply, Nat.add_comm]
  have hsi : Net.ParSteps r v i := fun k hk => hia k (by omega)
  have hJ : Net.ParSteps r ((Net.parOf r)^[i] v) (ia - i) :=
    (Net.parSteps_add.1 (by rwa [Nat.add_sub_of_le hi])).2
  rw [h.dsrcTop_down_flag_eq_zero F1 _ hJ ?_ ?_]
  · constructor
    · intro H l h1 h2
      have := H (l - i - 1) (by omega)
      rwa [e, show i + (l - i - 1 + 1) = l by omega] at this
    · intro H l hl
      rw [e]
      exact H _ (by omega) (by omega)
  · rw [e, Nat.add_sub_of_le hi]
    exact (h.first_iff F0 isT hT hv h0 h0' hia).2 rfl
  · intro j hj hx
    rw [e] at hx
    have := (h.first_iff F0 isT hT hv h0 h0' (Net.parSteps_add.2 ⟨hsi, hj⟩)).1 hx
    omega

open Classical in
/-- **The last flagged node below the first knows itself.** Under the conditions of `down_none_iff`,
let `iy ≤ ia` be the last node up to `ia` flagged by `F1`. A node `i ≤ ia` valid steps above `v` is
flagged by `F1` with distance `0` in the run down the chains exactly when `i = iy`. -/
theorem Net.ExactSpec.last_iff {N : Net V} {ℓ : V → V → ℕ∞} {φ : V → ℕ∞} {r : V → ℕ∞ × Option V}
    (h : N.ExactSpec ℓ φ r) (F0 F1 : V → Prop) (isT : V → Bool)
    (hT : ∀ t t' i i', isT t = true → isT t' = true → Net.ParSteps r t i → Net.ParSteps r t' i' →
      (Net.parOf r)^[i] t = (Net.parOf r)^[i'] t' → t = t')
    {v : V} (hv : isT v = true) {ia iy : ℕ} (hia : Net.ParSteps r v ia) (h0 : F0 ((Net.parOf r)^[ia] v))
    (h0' : ∀ l < ia, ¬ F0 ((Net.parOf r)^[l] v)) (hya : iy ≤ ia) (h1 : F1 ((Net.parOf r)^[iy] v))
    (h1' : ∀ l, iy < l → l ≤ ia → ¬ F1 ((Net.parOf r)^[l] v)) {i : ℕ} (hi : i ≤ ia) :
    (F1 ((Net.parOf r)^[i] v) ∧ N.dsrcTop (Net.downLenW r fun a => if F1 a then 1 else 0)
      (Net.markOffB fun a => decide (F0 a ∧ N.dsrcTop (Net.markLenW r fun a => if F0 a then 1 else 0)
        (Net.markOffB isT) a = 0)) ((Net.parOf r)^[i] v) = 0) ↔ i = iy := by
  rw [h.down_none_iff F0 F1 isT hT hv hia h0 h0' hi]
  constructor
  · rintro ⟨hF, hb⟩
    rcases lt_trichotomy i iy with hl | rfl | hl
    · exact absurd h1 (hb iy hl hya)
    · rfl
    · exact absurd hF (h1' i hl hi)
  · rintro rfl
    exact ⟨h1, h1'⟩

end Congest

end SsspFlow
