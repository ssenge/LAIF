import SsspFlow.DualDist
import SsspFlow.CutPathExists
import SsspFlow.OracleChainPos
import SsspFlow.OracleChainCount

/-!
# The cut path from the parent chain of the dual network

Run the exact shortest-path oracle on the dual network from the corner of `cs`, with lengths
`dualLen e g` for costs at least `1`. The parent chain from the corner of `ct` enters a node of kind
`m1` only from the corner of the same dart, across that dart. Read from the root, the darts of the
nodes of kind `m1` on the chain form a shortest walk of the dual map from the face of `cs` to the face
of `ct`, so a simple one and a shortest cut path. A second run counts, at every node of the chain, the
nodes of kind `m1` below it.

* `m1Dart`: the dart of a node of kind `m1`.
* `step_arc`: an arc of finite length into a node of kind `m1` crosses its dart, and every other arc
  stays in its face with length `0`.
* `chain_cutPath`: the cut path of the chain is shortest; the dart `e t` is the dart whose node of kind
  `m1` has count `m - 1 - t`, and the corner of `cs` has count `m`.
-/

set_option autoImplicit false

namespace SsspFlow.Congest

open XNode Kind FourColor
open scoped ENNReal

section Chain

variable {V : Type} [Fintype V] [DecidableEq V] {W : Type} [Fintype W] [DecidableEq W]
variable (N : Net V) (e : V × V × Kind ≃ W)

/-- The dart of a node of kind `m1`. -/
def m1Dart (b : W) : Option N.G.Dart :=
  if h : N.G.Adj (e.symm b).1 (e.symm b).2.1 ∧ (e.symm b).2.2 = m1 then
    some ⟨((e.symm b).1, (e.symm b).2.1), h.1⟩ else none

/-- The offsets of the oracle from the corner of `x₀`. -/
def cornerOff (x₀ : N.G.Dart) (a : W) : ℕ∞ := if a = idx N e corner x₀ then 0 else ⊤

/-- The flag of a node of kind `m1`, as a length. -/
def m1Flag (a : W) : ℕ∞ := ((m1Dart N e a).toList.length : ℕ∞)

variable {N e}

theorem m1Dart_idx (k : Kind) (x : N.G.Dart) :
    m1Dart N e (idx N e k x) = if k = m1 then some x else none := by
  unfold m1Dart idx
  simp only [Equiv.symm_apply_apply]
  by_cases hk : k = m1
  · subst hk; simp [x.adj]
  · simp [hk]

theorem m1Dart_eq_some {b : W} {x : N.G.Dart} (h : m1Dart N e b = some x) : b = idx N e m1 x := by
  unfold m1Dart at h
  split_ifs at h with h'
  cases h
  show b = e (_, _, m1)
  rw [← h'.2]
  simp

variable (g : V → V → ℕ)

/-- **The arcs of finite length.** -/
theorem step_arc (f₀ : N.toRot.dual.Vertex) {a b : W} (hab : (dualNet N e).G.Adj a b)
    (hfin : dualLen e g a b ≠ ⊤) :
    (m1Dart N e b = none ∧ dualLen e g a b = 0 ∧ faceId N e f₀ a = faceId N e f₀ b) ∨
      (∃ x, m1Dart N e b = some x ∧ dualLen e g a b = g x.fst x.snd ∧
        N.toRot.dual.IsWalk (faceId N e f₀ a) [x] (faceId N e f₀ b)) := by
  cases hw : dualW e (fun u v => (g u v : ℤ)) a b with
  | none => simp [dualLen, hw] at hfin
  | some y =>
    have hl : dualLen e g a b = (y.toNat : ℕ∞) := by simp [dualLen, hw]
    rw [hl]
    cases dual_arc hab hw with
    | cost x =>
      right
      refine ⟨x, by rw [m1Dart_idx]; rfl, by simp, ?_, ?_⟩
      · rw [faceId_idx]; rfl
      · rw [faceId_idx]; exact dualHead_eq x
    | m12 x => left; refine ⟨by rw [m1Dart_idx]; rfl, by simp, ?_⟩; rw [faceId_idx, faceId_idx]; rfl
    | m2c x => left; refine ⟨by rw [m1Dart_idx]; rfl, by simp, ?_⟩; rw [faceId_idx, faceId_idx]; rfl
    | cr1 x => left; refine ⟨by rw [m1Dart_idx]; rfl, by simp, ?_⟩; rw [faceId_idx, faceId_idx]; rfl
    | r1c x => left; refine ⟨by rw [m1Dart_idx]; rfl, by simp, ?_⟩; rw [faceId_idx, faceId_idx]; rfl
    | r12 x =>
      left; refine ⟨by rw [m1Dart_idx]; rfl, by simp, ?_⟩; rw [faceId_idx, faceId_idx]
      exact (dualTail_ring x).symm
    | r21 x =>
      left; refine ⟨by rw [m1Dart_idx]; rfl, by simp, ?_⟩; rw [faceId_idx, faceId_idx]
      have h := dualTail_ring (N := N) x.symm
      rw [SimpleGraph.Dart.symm_symm] at h
      exact h
    | r2c x => left; refine ⟨by rw [m1Dart_idx]; rfl, by simp, ?_⟩; rw [faceId_idx, faceId_idx]; rfl
    | cr2 x =>
      left; refine ⟨by rw [m1Dart_idx]; rfl, by simp, ?_⟩; rw [faceId_idx, faceId_idx]
      show N.toRot.dual.tail x = N.toRot.dual.tail (N.rotPerm.symm (N.rotPerm x))
      rw [Equiv.symm_apply_apply]

variable (N e) in
/-- The darts of the nodes of kind `m1` among `y (j - 1), …, y 0`, in this order. -/
def chainDarts (y : ℕ → W) (j : ℕ) : List N.G.Dart :=
  ((List.range j).reverse).filterMap fun i => m1Dart N e (y i)

theorem chainDarts_zero (y : ℕ → W) : chainDarts N e y 0 = [] := rfl

theorem chainDarts_succ (y : ℕ → W) (j : ℕ) :
    chainDarts N e y (j + 1) = (m1Dart N e (y j)).toList ++ chainDarts N e y j := by
  unfold chainDarts
  cases h : m1Dart N e (y j) <;> simp [List.range_succ, h]

theorem chainDarts_length (y : ℕ → W) : ∀ j,
    ∑ i ∈ Finset.range j, m1Flag N e (y i) = ((chainDarts N e y j).length : ℕ∞)
  | 0 => by simp [chainDarts_zero]
  | j + 1 => by
    rw [Finset.sum_range_succ, chainDarts_length y j, chainDarts_succ, List.length_append, Nat.cast_add,
      add_comm]
    rfl

theorem chainDarts_mem (y : ℕ → W) : ∀ j t (ht : t < (chainDarts N e y j).length),
    ∃ i < j, m1Dart N e (y i) = some ((chainDarts N e y j)[t]) ∧
      (chainDarts N e y i).length + 1 + t = (chainDarts N e y j).length
  | 0, t, ht => absurd ht (by simp [chainDarts_zero])
  | j + 1, t, ht => by
    have hs := chainDarts_succ (N := N) (e := e) y j
    cases hm : m1Dart N e (y j) with
    | none =>
      simp only [hm, Option.toList_none, List.nil_append] at hs
      have ht' : t < (chainDarts N e y j).length := by rw [← hs]; exact ht
      obtain ⟨i, hi, h1, h2⟩ := chainDarts_mem y j t ht'
      refine ⟨i, by omega, ?_, ?_⟩
      · rw [h1]; congr 1; simp only [hs]
      · rw [h2, hs]
    | some x =>
      simp only [hm, Option.toList_some, List.singleton_append] at hs
      cases t with
      | zero =>
        refine ⟨j, by omega, ?_, ?_⟩
        · rw [hm]; congr 1; simp only [hs, List.getElem_cons_zero]
        · rw [hs]; simp
      | succ t =>
        have ht' : t < (chainDarts N e y j).length := by
          have := ht; rw [hs] at this; simpa using this
        obtain ⟨i, hi, h1, h2⟩ := chainDarts_mem y j t ht'
        refine ⟨i, by omega, ?_, ?_⟩
        · rw [h1]; congr 1; simp only [hs, List.getElem_cons_succ]
        · rw [hs, List.length_cons]; omega

theorem chainDarts_append (y : ℕ → W) (i : ℕ) : ∀ j, i ≤ j →
    ∃ B, chainDarts N e y j = B ++ chainDarts N e y i
  | j, hij => by
    induction j with
    | zero => obtain rfl : i = 0 := by omega
              exact ⟨[], (List.nil_append _).symm⟩
    | succ j ih =>
      rcases Nat.lt_or_ge i (j + 1) with h | h
      · obtain ⟨B, hB⟩ := ih (by omega)
        exact ⟨(m1Dart N e (y j)).toList ++ B, by rw [chainDarts_succ, hB, List.append_assoc]⟩
      · obtain rfl : i = j + 1 := by omega
        exact ⟨[], (List.nil_append _).symm⟩

theorem chainDarts_walk (f₀ : N.toRot.dual.Vertex) (y : ℕ → W) (k : ℕ)
    (hstep : ∀ i < k, (dualNet N e).G.Adj (y (i + 1)) (y i) ∧ dualLen e g (y (i + 1)) (y i) ≠ ⊤) :
    ∀ j, j ≤ k → N.toRot.dual.IsWalk (faceId N e f₀ (y j)) (chainDarts N e y j) (faceId N e f₀ (y 0)) ∧
      ((((chainDarts N e y j).map fun x => g x.fst x.snd).sum : ℕ) : ℕ∞) =
        ∑ i ∈ Finset.range j, dualLen e g (y (i + 1)) (y i)
  | 0, _ => ⟨rfl, by simp [chainDarts_zero]⟩
  | j + 1, hj => by
    obtain ⟨ih1, ih2⟩ := chainDarts_walk f₀ y k hstep j (by omega)
    obtain ⟨hadj, hfin⟩ := hstep j (by omega)
    rw [chainDarts_succ, Finset.sum_range_succ, ← ih2]
    rcases step_arc g f₀ hadj hfin with ⟨hm, h0, hf⟩ | ⟨x, hm, hx, hw⟩
    · rw [hm, h0]
      exact ⟨by simpa [hf] using ih1, by simp⟩
    · rw [hm, hx]
      refine ⟨⟨hw.1, hw.2 ▸ ih1⟩, ?_⟩
      simp [add_comm]

end Chain

section ChainCut

variable {V : Type} [Fintype V] [DecidableEq V] {W : Type} [Fintype W] [DecidableEq W]
  {N : Net V} {e : V × V × Kind ≃ W} (g : V → V → ℕ)

open Classical in
/-- **The cut path of the parent chain.** For costs at least `1`, let `r` meet the specification of
the oracle on the dual network with offset `0` at the corner of `cs`. The darts of the nodes of kind
`m1` on the parent chain of the corner of `ct` form a cut path from `cs` to `ct` that is shortest for
the costs. With the flags of the nodes of kind `m1` as lengths on the arcs to the parents, and the
corner of `ct` as target, the dart `e t` is the dart whose node of kind `m1` has distance `m - 1 - t`,
and the corner of `cs` has distance `m`. -/
theorem chain_cutPath (hg : ∀ d : N.G.Dart, 1 ≤ g d.fst d.snd) {cs ct : N.G.Dart}
    (hf : ¬ fconnect N.toRot.dual.facePerm cs ct)
    (hw : ∃ q, N.toRot.dual.IsWalk (N.toRot.dual.tail cs) q (N.toRot.dual.tail ct))
    {r : W → ℕ∞ × Option W} (h : (dualNet N e).ExactSpec (dualLen e g) (cornerOff N e cs) r) :
    ∃ C : N.toRot.dual.CutPath, C.cs = cs ∧ C.ct = ct ∧
      (∀ q, N.toRot.dual.IsWalk (C.v 0) q (C.v C.m) →
        C.pos (fun x => g x.fst x.snd) C.m ≤ (q.map fun x => g x.fst x.snd).sum) ∧
      (∀ (x : N.G.Dart) (t : ℕ), t < C.m → (C.e t = x ↔
        (dualNet N e).dsrcTop (Net.markLenW r (m1Flag N e))
          (Net.markOffB fun a => decide (a = idx N e corner ct)) (idx N e m1 x) = ((C.m - 1 - t : ℕ) : ℝ≥0∞))) ∧
      (dualNet N e).dsrcTop (Net.markLenW r (m1Flag N e))
        (Net.markOffB fun a => decide (a = idx N e corner ct)) (idx N e corner cs) = (C.m : ℝ≥0∞) := by
  set v := idx N e corner ct with hvdef
  set gd : N.G.Dart → ℕ := fun x => g x.fst x.snd with hgd
  have hoff : cornerOff N e cs = fun a => if a = idx N e corner cs then 0 else ⊤ := rfl
  have hdist : ((r v).1 : ℝ≥0∞) = ⨅ (q : List N.G.Dart)
      (_ : N.toRot.dual.IsWalk (N.toRot.dual.tail cs) q (N.toRot.dual.tail ct)),
        (((q.map gd).sum : ℕ) : ℝ≥0∞) := by
    rw [h.dist_eq v, hoff]
    exact dist_corner g cs ct
  have hv : (r v).1 ≠ ⊤ := by
    obtain ⟨q₀, hq₀⟩ := hw
    have h1 : ((r v).1 : ℝ≥0∞) ≠ ⊤ :=
      ne_top_of_le_ne_top (ENNReal.natCast_ne_top _) (hdist ▸ iInf₂_le q₀ hq₀)
    simpa using h1
  obtain ⟨k, h1, h2, h3, h4⟩ := h.chain v hv
  set y : ℕ → W := fun i => (Net.parOf r)^[i] v with hy
  have hroot : y k = idx N e corner cs := by
    have : cornerOff N e cs (y k) ≠ ⊤ := fun e' => hv (by rw [← h4, e', top_add])
    by_contra hne
    exact this (by simp [cornerOff, hne])
  have hφ : cornerOff N e cs (y k) = 0 := by simp [cornerOff, hroot]
  have hsum : ∑ i ∈ Finset.range k, dualLen e g (y (i + 1)) (y i) = (r v).1 := by
    rw [← h4, hφ, zero_add]
  have hstep : ∀ i < k, (dualNet N e).G.Adj (y (i + 1)) (y i) ∧ dualLen e g (y (i + 1)) (y i) ≠ ⊤ :=
    fun i hi => ⟨(h3 i hi).2, fun e' => hv (by
      rw [← hsum]; exact top_le_iff.1 (e' ▸ Finset.single_le_sum (f := fun i => dualLen e g (y (i + 1)) (y i)) (fun _ _ => bot_le)
        (Finset.mem_range.2 hi)))⟩
  obtain ⟨hq, hc⟩ := chainDarts_walk g (N.toRot.dual.tail cs) y k hstep k le_rfl
  rw [hroot, faceId_idx] at hq
  have hy0 : y 0 = v := rfl
  rw [hy0, hvdef, faceId_idx] at hq
  change N.toRot.dual.IsWalk (N.toRot.dual.tail cs) _ (N.toRot.dual.tail ct) at hq
  set q := chainDarts N e y k with hqdef
  have hmin : ∀ q', N.toRot.dual.IsWalk (N.toRot.dual.tail cs) q' (N.toRot.dual.tail ct) →
      (q.map gd).sum ≤ (q'.map gd).sum := by
    intro q' hq'
    have e0 : (((q.map gd).sum : ℕ) : ℕ∞) = (r v).1 := by rw [← hsum, ← hc]
    have e1 : (((q.map gd).sum : ℕ) : ℝ≥0∞) = ((r v).1 : ℝ≥0∞) := by rw [← e0]; exact (ENat.toENNReal_coe _).symm
    have e2 := hdist ▸ (iInf₂_le q' hq' : (⨅ (q : List N.G.Dart)
      (_ : N.toRot.dual.IsWalk (N.toRot.dual.tail cs) q (N.toRot.dual.tail ct)),
        (((q.map gd).sum : ℕ) : ℝ≥0∞)) ≤ _)
    exact_mod_cast e1 ▸ e2
  obtain ⟨hnd, hne⟩ := RotSystem.IsWalk.simple_of_shortest (fun d => hg d) hq hmin
  refine ⟨RotSystem.CutPath.ofSimple cs ct q hq hnd hne hf, rfl, rfl,
    RotSystem.CutPath.ofSimple_shortest gd hmin, ?_⟩
  -- counting
  set isT : W → Bool := fun a => decide (a = v) with hisT
  have hpar : ∀ i, i ≤ k → Net.ParSteps r v i := fun i hi j hj => (h3 j (by omega)).1
  have hparle : ∀ i, Net.ParSteps r v i → i ≤ k := by
    intro i hs
    by_contra hlt
    have := hs k (by omega)
    rw [show (r ((Net.parOf r)^[k] v)).2 = none from h1] at this
    cases this
  have hT : ∀ t t' i i', isT t = true → isT t' = true → Net.ParSteps r t i → Net.ParSteps r t' i' →
      (Net.parOf r)^[i] t = (Net.parOf r)^[i'] t' → t = t' := fun t t' _ _ ht ht' _ _ _ => by
    simp only [hisT, decide_eq_true_eq] at ht ht'
    rw [ht, ht']
  have hcnt : ∀ i, i ≤ k → (dualNet N e).dsrcTop (Net.markLenW r (m1Flag N e)) (Net.markOffB isT) (y i) =
      ((chainDarts N e y i).length : ℝ≥0∞) := by
    intro i hi
    rw [h.dsrcTop_sum (m1Flag N e) isT hT (by simp [hisT]) (hpar i hi), chainDarts_length]
    exact ENat.toENNReal_coe _
  have hoffc : ∀ a, (dualNet N e).dsrcTop (Net.markLenW r (m1Flag N e)) (Net.markOffB isT) a ≠ ⊤ →
      ∃ i ≤ k, y i = a := by
    intro a ha
    by_contra hno
    push Not at hno
    apply ha
    rw [h.dsrcTop_markW]
    refine top_le_iff.1 (le_iInf fun t => le_iInf fun ht => le_iInf fun i => le_iInf fun ⟨hs, hx⟩ => ?_)
    simp only [hisT, decide_eq_true_eq] at ht
    subst ht
    exact absurd hx (hno i (hparle i hs))
  refine ⟨fun x t ht => ?_, ?_⟩
  · simp only [RotSystem.CutPath.ofSimple_m, RotSystem.CutPath.ofSimple_e] at ht ⊢
    constructor
    · intro hx
      obtain ⟨i, hi, hm, hlen⟩ := chainDarts_mem (N := N) (e := e) y k t ht
      rw [List.getD_eq_getElem _ _ ht] at hx
      rw [hx] at hm
      rw [← m1Dart_eq_some hm, hcnt i hi.le]
      have hqk : (chainDarts N e y k).length = q.length := rfl
      congr 1
      omega
    · intro hx
      obtain ⟨i, hi, hyi⟩ := hoffc _ (by rw [hx]; exact ENNReal.natCast_ne_top _)
      have hlen : (chainDarts N e y i).length = q.length - 1 - t := by
        have := hcnt i hi
        rw [hyi, hx] at this
        exact_mod_cast this.symm
      have hik : i < k := by
        rcases Nat.lt_or_ge i k with h' | h'
        · exact h'
        · obtain rfl : i = k := le_antisymm hi h'
          rw [hroot] at hyi
          simp [idx] at hyi
      have hm : m1Dart N e (y i) = some x := by rw [hyi, m1Dart_idx]; rfl
      obtain ⟨B, hB⟩ := chainDarts_append (N := N) (e := e) y (i + 1) k hik
      rw [chainDarts_succ, hm] at hB
      simp only [Option.toList_some, List.singleton_append] at hB
      have hBl : B.length = t := by
        have := congrArg List.length hB
        simp only [List.length_append, List.length_cons] at this
        rw [← hqdef] at this
        omega
      rw [← hqdef] at hB
      rw [hB, ← hBl]
      simp
  · rw [← hroot, hcnt k le_rfl]
    rfl

end ChainCut

end SsspFlow.Congest
