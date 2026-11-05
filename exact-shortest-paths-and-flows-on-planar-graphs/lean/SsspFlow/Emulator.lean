import SsspFlow.LabelHypothesis
import SsspFlow.Compose
import SsspFlow.Bags

/-!
# One bag: from a metric to labels

A metric with the condition (M) on `k` corners has a planar disk (`RealizationBox`). Its weights,
scaled and rounded up, have distance labels (`DistanceLabelBox`) that give back the metric up to the
factor `(U + 4) / U`, if the metric is between `U` and `B` off the diagonal (`exists_labels`). Numbers
stay small: the rounding scale `s` needs only to reach the number of vertices of the disk.

`exists_bagOK` combines the two statements. It takes any feasible point: a metric with (M) close to
the given matrix `w`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped ENNReal

namespace SsspFlow

open FourColor
open Congest (RealizationBox)

namespace RotSystem

/-! ### Rounding the weights -/

section Round

variable {D : Type*} [Fintype D] [DecidableEq D] (R : RotSystem D)

/-- The least natural number at or above `y`. -/
noncomputable def ceilE (y : ℝ≥0∞) : ℕ := sInf {n : ℕ | y ≤ n}

theorem le_ceilE {y : ℝ≥0∞} (h : y ≠ ⊤) : y ≤ ceilE y := by
  obtain ⟨n, hn⟩ := ENNReal.exists_nat_gt h
  have h1 : ({n : ℕ | y ≤ n}).Nonempty := ⟨n, hn.le⟩
  exact Nat.sInf_mem h1

theorem ceilE_le_add {y : ℝ≥0∞} : (ceilE y : ℝ≥0∞) ≤ y + 1 := by
  rcases Nat.eq_zero_or_pos (ceilE y) with h | h
  · rw [h]
    simp
  · have h1 : ceilE y - 1 ∉ {n : ℕ | y ≤ n} := Nat.notMem_of_lt_sInf (by unfold ceilE at h ⊢; omega)
    have h2 : ((ceilE y - 1 : ℕ) : ℝ≥0∞) < y := not_le.1 h1
    have h3 : (ceilE y : ℝ≥0∞) = ((ceilE y - 1 : ℕ) : ℝ≥0∞) + 1 := by
      have : ceilE y = (ceilE y - 1) + 1 := by omega
      conv_lhs => rw [this]
      push_cast
      rfl
    rw [h3]
    gcongr

theorem ceilE_le {y : ℝ≥0∞} {n : ℕ} (h : y ≤ n) : ceilE y ≤ n :=
  Nat.sInf_le h

/-- Dart weights scaled by `s` and rounded up, and `⊤` above `2 * B`. -/
noncomputable def roundW (s B : ℕ) (g : D → ℝ≥0∞) (x : D) : ℕ∞ :=
  open Classical in
  if g x ≤ 2 * (B : ℝ≥0∞) then ((ceilE ((s : ℝ≥0∞) * g x) : ℕ) : ℕ∞) else ⊤

variable {s B : ℕ} {g : D → ℝ≥0∞}

private theorem mul_ne_top_of_le {x : D} (h : g x ≤ 2 * (B : ℝ≥0∞)) :
    (s : ℝ≥0∞) * g x ≠ ⊤ := by
  refine ENNReal.mul_ne_top (ENNReal.natCast_ne_top s) (ne_top_of_le_ne_top ?_ h)
  exact ENNReal.mul_ne_top (by norm_num) (ENNReal.natCast_ne_top B)

theorem le_roundW (x : D) : (s : ℝ≥0∞) * g x ≤ (roundW s B g x : ℝ≥0∞) := by
  unfold roundW
  split_ifs with h
  · rw [ENat.toENNReal_coe]
    exact le_ceilE (mul_ne_top_of_le h)
  · rw [ENat.toENNReal_top]
    exact le_top

theorem roundW_le {x : D} (h : g x ≤ 2 * (B : ℝ≥0∞)) :
    (roundW s B g x : ℝ≥0∞) ≤ (s : ℝ≥0∞) * g x + 1 := by
  unfold roundW
  rw [ite_eq_left h, ENat.toENNReal_coe]
  exact ceilE_le_add

theorem roundW_cases (x : D) : roundW s B g x = ⊤ ∨ roundW s B g x ≤ ((2 * s * B : ℕ) : ℕ∞) := by
  unfold roundW
  split_ifs with h
  · right
    refine ENat.natCast_le_natCast.2 (ceilE_le ?_)
    calc (s : ℝ≥0∞) * g x ≤ s * (2 * B) := by gcongr
      _ = ((2 * s * B : ℕ) : ℝ≥0∞) := by push_cast; ring
  · exact Or.inl rfl

private theorem mul_sum_le_round (ws : List D) :
    (s : ℝ≥0∞) * (ws.map g).sum ≤ (ws.map fun x => (roundW s B g x : ℝ≥0∞)).sum := by
  induction ws with
  | nil => simp
  | cons x ws ih =>
    simp only [List.map_cons, List.sum_cons, mul_add]
    exact add_le_add (le_roundW x) ih

theorem mul_walkDist_le (u v : R.Vertex) :
    (s : ℝ≥0∞) * R.walkDist g u v ≤ R.walkDist (fun x => (roundW s B g x : ℝ≥0∞)) u v := by
  refine le_iInf₂ fun ws hw => ?_
  exact (mul_le_mul_right (walkDist_le g hw) _).trans (mul_sum_le_round ws)

private theorem sum_round_le (q : List D) (h : ∀ x ∈ q, g x ≤ 2 * (B : ℝ≥0∞)) :
    (q.map fun x => (roundW s B g x : ℝ≥0∞)).sum ≤ (s : ℝ≥0∞) * (q.map g).sum + q.length := by
  induction q with
  | nil => simp
  | cons x q ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    have h1 := roundW_le (s := s) (h x (by simp))
    have h2 := ih fun y hy => h y (List.mem_cons_of_mem _ hy)
    calc (roundW s B g x : ℝ≥0∞) + (q.map fun x => (roundW s B g x : ℝ≥0∞)).sum
        ≤ ((s : ℝ≥0∞) * g x + 1) + ((s : ℝ≥0∞) * (q.map g).sum + q.length) := add_le_add h1 h2
      _ = (s : ℝ≥0∞) * (g x + (q.map g).sum) + ((q.length + 1 : ℕ) : ℝ≥0∞) := by
        push_cast
        ring

private theorem sum_le_of_sublist {q ws : List D} (h : q.Sublist ws) :
    (q.map g).sum ≤ (ws.map g).sum := by
  induction h with
  | slnil => exact le_rfl
  | cons x _ ih =>
    simp only [List.map_cons, List.sum_cons]
    exact ih.trans le_add_self
  | cons_cons x _ ih =>
    simp only [List.map_cons, List.sum_cons]
    exact add_le_add le_rfl ih

private theorem le_sum_of_mem {q : List D} {x : D} (h : x ∈ q) : g x ≤ (q.map g).sum := by
  induction q with
  | nil => simp at h
  | cons y q ih =>
    simp only [List.map_cons, List.sum_cons]
    rcases List.mem_cons.1 h with rfl | h
    · exact le_self_add
    · exact (ih h).trans le_add_self

private theorem length_le_numVertices {q : List D} (h : (q.map R.tail).Nodup) :
    q.length ≤ R.numVertices := by
  classical
  have : Fintype R.Vertex := Fintype.ofFinite _
  have h1 := h.length_le_card
  rw [List.length_map] at h1
  rwa [← R.natCard_vertex, Nat.card_eq_fintype_card]

/-- Rounding adds at most the number of vertices to a distance of at most `B`. -/
theorem walkDist_round_le (hs : 1 ≤ s) (hB : 1 ≤ B) {u v : R.Vertex}
    (h : R.walkDist g u v ≤ (B : ℝ≥0∞)) :
    R.walkDist (fun x => (roundW s B g x : ℝ≥0∞)) u v ≤
      (s : ℝ≥0∞) * R.walkDist g u v + R.numVertices := by
  have key : ∀ ws, R.IsWalk u ws v → (ws.map g).sum ≤ 2 * (B : ℝ≥0∞) →
      R.walkDist (fun x => (roundW s B g x : ℝ≥0∞)) u v ≤
        (s : ℝ≥0∞) * (ws.map g).sum + R.numVertices := by
    intro ws hw hle
    obtain ⟨q, hq, hqn, -, hsub⟩ := hw.exists_simple
    have h1 := sum_le_of_sublist (g := g) hsub
    have h2 : ∀ x ∈ q, g x ≤ 2 * (B : ℝ≥0∞) := fun x hx =>
      (le_sum_of_mem hx).trans (h1.trans hle)
    have h3 := sum_round_le (s := s) q h2
    have h4 : (q.length : ℝ≥0∞) ≤ R.numVertices := by
      exact_mod_cast length_le_numVertices R hqn
    have h5 := walkDist_le (fun x => (roundW s B g x : ℝ≥0∞)) hq
    refine h5.trans (h3.trans (add_le_add ?_ h4))
    gcongr
  have hlt : R.walkDist g u v < 2 * (B : ℝ≥0∞) := by
    refine lt_of_le_of_lt h ?_
    have h1 : (B : ℝ≥0∞) < ((2 * B : ℕ) : ℝ≥0∞) := by
      exact_mod_cast (by omega : B < 2 * B)
    simpa using h1
  simp only [walkDist, iInf_lt_iff] at hlt
  obtain ⟨ws₀, hw₀, hlt₀⟩ := hlt
  have h0 : (s : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast (by omega : s ≠ 0)
  have hrhs : (s : ℝ≥0∞) * R.walkDist g u v + R.numVertices =
      ⨅ (ws : List D) (_ : R.IsWalk u ws v), ((s : ℝ≥0∞) * (ws.map g).sum + R.numVertices) := by
    simp only [walkDist, ENNReal.mul_iInf_of_ne h0 (ENNReal.natCast_ne_top s), ENNReal.iInf_add]
  rw [hrhs]
  refine le_iInf₂ fun ws hw => ?_
  by_cases hle : (ws.map g).sum ≤ 2 * (B : ℝ≥0∞)
  · exact key ws hw hle
  · refine (key ws₀ hw₀ hlt₀.le).trans ?_
    have h1 : (ws₀.map g).sum ≤ (ws.map g).sum := hlt₀.le.trans (not_le.1 hle).le
    gcongr

end Round

end RotSystem

/-! ### Undoing the scale -/

/-- The value `q` divided by `s`, rounded up. -/
noncomputable def decode (s : ℕ) (q : ℕ∞) : ℕ∞ :=
  open Classical in if q = ⊤ then ⊤ else (((q.toNat + s - 1) / s : ℕ) : ℕ∞)

theorem le_mul_decode {s : ℕ} (hs : 1 ≤ s) (q : ℕ∞) :
    (q : ℝ≥0∞) ≤ (s : ℝ≥0∞) * (decode s q : ℝ≥0∞) := by
  unfold decode
  split_ifs with h
  · subst h
    have h0 : (s : ℝ≥0∞) ≠ 0 := by
      exact_mod_cast (by omega : s ≠ 0)
    simp [ENNReal.mul_top h0]
  · obtain ⟨n, rfl⟩ := ENat.ne_top_iff_exists.1 h
    simp only [ENat.toNat_natCast, ENat.toENNReal_coe]
    have h1 := Nat.div_add_mod (n + s - 1) s
    have h2 := Nat.mod_lt (n + s - 1) (by omega : 0 < s)
    have h3 : n ≤ s * ((n + s - 1) / s) := by omega
    exact_mod_cast h3

theorem mul_decode_le {s : ℕ} (hs : 1 ≤ s) (q : ℕ∞) :
    (s : ℝ≥0∞) * (decode s q : ℝ≥0∞) ≤ (q : ℝ≥0∞) + s := by
  unfold decode
  split_ifs with h
  · subst h
    simp
  · obtain ⟨n, rfl⟩ := ENat.ne_top_iff_exists.1 h
    simp only [ENat.toNat_natCast, ENat.toENNReal_coe]
    have h1 := Nat.div_add_mod (n + s - 1) s
    have h3 : s * ((n + s - 1) / s) ≤ n + s := by omega
    exact_mod_cast h3

/-! ### Labels of one disk -/

/-- The statement of `DistanceLabelBox` for one precision. -/
def LabelQuery (C c e : ℕ) (query : List ℕ → List ℕ → ℕ∞) : Prop :=
  ∀ (D : Type) [Fintype D] [DecidableEq D] (R : RotSystem D) (N : ℕ) (g : D → ℕ∞),
    R.Planar → (∀ x, g x = ⊤ ∨ g x ≤ N) →
    ∃ label : R.Vertex → List ℕ, ∀ u v,
      (label u).length ≤ C * Nat.log 2 (R.numVertices + N + 2) ^ c * e ∧
      (∀ x ∈ label u, x < (R.numVertices + N + 2) ^ c) ∧
      R.walkDist (fun x => (g x : ℝ≥0∞)) u v ≤ (query (label u) (label v) : ℝ≥0∞) ∧
      (query (label u) (label v) : ℝ≥0∞) ≤
        (1 + (e : ℝ≥0∞)⁻¹) * R.walkDist (fun x => (g x : ℝ≥0∞)) u v

/-- **Labels of one disk.** If the distances of the corners of a planar map are between `U` and `B`,
and `s` is at least the number of vertices, then rounding and distance labels give them back up to the
factor `(U + 4) / U`. -/
theorem exists_labels {C c U s B : ℕ} {query : List ℕ → List ℕ → ℕ∞}
    (hq : LabelQuery C c U query) (hU : 1 ≤ U) (hs : 1 ≤ s) (hB : 1 ≤ B) {m k : ℕ}
    (K : RotSystem (Fin m)) (g : Fin m → ℝ≥0∞) (l : Fin k → Fin m) (hP : K.Planar)
    (hV : K.numVertices ≤ s) {d : Fin k → Fin k → ℝ≥0∞}
    (hd : ∀ i j, K.walkDist g (K.tail (l i)) (K.tail (l j)) = d i j)
    (hdU : ∀ i j, i ≠ j → (U : ℝ≥0∞) ≤ d i j ∧ d i j ≤ (B : ℝ≥0∞)) :
    ∃ lab : Fin k → List ℕ,
      (∀ i, (lab i).length ≤ C * Nat.log 2 (s + 2 * s * B + 2) ^ c * U ∧
        ∀ x ∈ lab i, x < (s + 2 * s * B + 2) ^ c) ∧
      ∀ i j, i ≠ j → d i j ≤ (decode s (query (lab i) (lab j)) : ℝ≥0∞) ∧
        (U : ℝ≥0∞) * (decode s (query (lab i) (lab j)) : ℝ≥0∞) ≤ ((U : ℝ≥0∞) + 4) * d i j := by
  obtain ⟨label, hlab⟩ := hq (Fin m) K (2 * s * B) (RotSystem.roundW s B g) hP
    RotSystem.roundW_cases
  have hbase : K.numVertices + 2 * s * B + 2 ≤ s + 2 * s * B + 2 := by omega
  refine ⟨fun i => label (K.tail (l i)), fun i => ⟨?_, fun x hx => ?_⟩, fun i j hij => ?_⟩
  · refine (hlab _ (K.tail (l i))).1.trans ?_
    have h1 := Nat.log_mono_right (b := 2) hbase
    gcongr
  · exact ((hlab _ (K.tail (l i))).2.1 x hx).trans_le (Nat.pow_le_pow_left hbase c)
  · obtain ⟨-, -, hlo, hhi⟩ := hlab (K.tail (l i)) (K.tail (l j))
    set q := query (label (K.tail (l i))) (label (K.tail (l j))) with hqdef
    set W := K.walkDist (fun x => (RotSystem.roundW s B g x : ℝ≥0∞)) (K.tail (l i)) (K.tail (l j))
      with hW
    obtain ⟨hd1, hd2⟩ := hdU i j hij
    have h0 : (s : ℝ≥0∞) ≠ 0 := by
      exact_mod_cast (by omega : s ≠ 0)
    have hT : (s : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top s
    have hW1 : (s : ℝ≥0∞) * d i j ≤ W := by
      rw [← hd]
      exact RotSystem.mul_walkDist_le K _ _
    have hW2 : W ≤ (s : ℝ≥0∞) * d i j + s := by
      have h1 := RotSystem.walkDist_round_le K (g := g) hs hB (u := K.tail (l i))
        (v := K.tail (l j)) (by rw [hd]; exact hd2)
      rw [hd] at h1
      refine h1.trans ?_
      gcongr
    have hU0 : (U : ℝ≥0∞) ≠ 0 := by
      exact_mod_cast (by omega : U ≠ 0)
    have hUT : (U : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top U
    refine ⟨?_, ?_⟩
    · have h1 : (s : ℝ≥0∞) * d i j ≤ (s : ℝ≥0∞) * (decode s q : ℝ≥0∞) :=
        hW1.trans (hlo.trans (le_mul_decode hs q))
      exact (ENNReal.mul_le_mul_iff_right h0 hT).1 h1
    · have hUq : (U : ℝ≥0∞) * (q : ℝ≥0∞) ≤ ((U : ℝ≥0∞) + 1) * W := by
        calc (U : ℝ≥0∞) * (q : ℝ≥0∞) ≤ U * ((1 + (U : ℝ≥0∞)⁻¹) * W) := by gcongr
          _ = ((U : ℝ≥0∞) + 1) * W := by
            rw [← mul_assoc, mul_add, mul_one, ENNReal.mul_inv_cancel hU0 hUT]
      have h1 : (s : ℝ≥0∞) * ((U : ℝ≥0∞) * (decode s q : ℝ≥0∞)) ≤
          (s : ℝ≥0∞) * (((U : ℝ≥0∞) + 4) * d i j) := by
        have hUd : (3 : ℝ≥0∞) * U ≤ 3 * d i j := by gcongr
        have hone : (1 : ℝ≥0∞) ≤ U := by
          exact_mod_cast hU
        calc (s : ℝ≥0∞) * ((U : ℝ≥0∞) * (decode s q : ℝ≥0∞))
            = (U : ℝ≥0∞) * ((s : ℝ≥0∞) * (decode s q : ℝ≥0∞)) := by ring
          _ ≤ (U : ℝ≥0∞) * ((q : ℝ≥0∞) + s) := by
            gcongr
            exact mul_decode_le hs q
          _ = (U : ℝ≥0∞) * (q : ℝ≥0∞) + U * s := by ring
          _ ≤ ((U : ℝ≥0∞) + 1) * W + U * s := by gcongr
          _ ≤ ((U : ℝ≥0∞) + 1) * ((s : ℝ≥0∞) * d i j + s) + U * s := by gcongr
          _ = (s : ℝ≥0∞) * (((U : ℝ≥0∞) + 1) * d i j + (2 * U + 1)) := by ring
          _ ≤ (s : ℝ≥0∞) * (((U : ℝ≥0∞) + 1) * d i j + 3 * d i j) := by
            gcongr
            calc 2 * (U : ℝ≥0∞) + 1 ≤ 2 * U + U := by gcongr
              _ = 3 * U := by ring
              _ ≤ 3 * d i j := hUd
          _ = (s : ℝ≥0∞) * (((U : ℝ≥0∞) + 4) * d i j) := by ring
      exact (ENNReal.mul_le_mul_iff_right h0 hT).1 h1

/-! ### Metrics with (M) -/

/-- A matrix for `RealizationBox`: a positive finite metric with the crossing inequalities. -/
structure MongeMetric {k : ℕ} (d : Fin k → Fin k → ℝ≥0∞) : Prop where
  /-- Zero on the diagonal. -/
  self : ∀ i, d i i = 0
  /-- Positive and finite off the diagonal. -/
  pos : ∀ i j, i ≠ j → d i j ≠ 0 ∧ d i j ≠ ⊤
  /-- The triangle inequality. -/
  tri : ∀ i j l, d i l ≤ d i j + d j l
  /-- The crossing inequalities. -/
  monge : ∀ a b c f u v x z : Fin k, [a, b, c, f].Sublist (List.finRange k) →
    ((u = a ∧ v = c) ∨ (u = c ∧ v = a)) → ((x = b ∧ z = f) ∨ (x = f ∧ z = b)) →
    d u z + d x v ≤ d u v + d x z

/-- `d` is realized on a planar disk with at most `V` vertices. -/
def Realizes (V : ℕ) {k : ℕ} (d : Fin k → Fin k → ℝ≥0∞) : Prop :=
  ∃ (m : ℕ) (K : RotSystem (Fin m)) (g : Fin m → ℝ≥0∞) (l : Fin k → Fin m),
    K.numVertices ≤ V ∧ K.DiskDrawn (List.ofFn l) ∧
      ∀ i j, K.walkDist g (K.tail (l i)) (K.tail (l j)) = d i j

/-- Two corners give a metric with (M), since there are no four corners. -/
private theorem mongeMetric_two :
    MongeMetric (fun i j : Fin 2 => if i = j then (0 : ℝ≥0∞) else 1) where
  self i := by simp
  pos i j h := by simp [h]
  tri i j l := by
    fin_cases i <;> fin_cases j <;> fin_cases l <;> simp
  monge a b c f u v x z h := by
    have := h.length_le
    simp at this

/-- One corner on a disk. -/
private theorem DiskDrawn.singleton {m : ℕ} {K : RotSystem (Fin m)} {l : List (Fin m)}
    (h : K.DiskDrawn l) (x : Fin m) : K.DiskDrawn [x] where
  planar := h.planar
  connected := h.connected
  tails_nodup := by simp
  order := by
    rw [List.formPerm_singleton]
    have h1 : [x].toFinset = {x} := by simp
    rw [h1]
    exact firstReturn_singleton _ x

/-- Every metric with (M) on at least one corner is realized. -/
theorem realizes_of_box {C : ℕ} (hC : RealizationBox C) {k : ℕ} (hk : 1 ≤ k)
    {d : Fin k → Fin k → ℝ≥0∞} (hd : MongeMetric d) : Realizes (C * (k + 1) ^ 6) d := by
  by_cases h2 : 2 ≤ k
  · obtain ⟨m, K, g, l, h3, h4, h5⟩ := hC k h2 d hd.self hd.pos hd.tri hd.monge
    refine ⟨m, K, g, l, h3.trans ?_, h4, h5⟩
    gcongr
    omega
  · obtain rfl : k = 1 := by omega
    have h3 := mongeMetric_two
    obtain ⟨m, K, g, l, h4, h5, -⟩ := hC 2 le_rfl _ h3.self h3.pos h3.tri h3.monge
    refine ⟨m, K, g, fun _ => l 0, ?_, ?_, ?_⟩
    · refine h4.trans ?_
      norm_num
    · have h6 : List.ofFn (fun _ : Fin 1 => l 0) = [l 0] := by simp
      rw [h6]
      exact DiskDrawn.singleton h5 _
    · intro i j
      have hij : i = j := Subsingleton.elim i j
      subst hij
      rw [RotSystem.walkDist_self, hd.self]

/-- The outcome for one bag: labels and a metric with (M) close to `w`. -/
structure BagOK (query : List ℕ → List ℕ → ℕ∞) (V U s L W : ℕ) {k : ℕ}
    (w : Fin k → Fin k → ℝ≥0∞) (lab : Fin k → List ℕ) (m : Fin k → Fin k → ℝ≥0∞) : Prop where
  /-- The metric has (M). -/
  monge : MongeMetric m
  /-- The metric is realized. -/
  real : Realizes V m
  /-- The metric is at least `w`. -/
  lo : ∀ i j, w i j ≤ m i j
  /-- The metric is at most `(U + 4) / U` times `w`. -/
  hi : ∀ i j, (U : ℝ≥0∞) * m i j ≤ ((U : ℝ≥0∞) + 4) * w i j
  /-- The labels are short. -/
  len : ∀ i, (lab i).length ≤ L
  /-- The words of the labels are small. -/
  word : ∀ i, ∀ x ∈ lab i, x < W
  /-- The query gives at least the metric. -/
  val_lo : ∀ i j, i ≠ j → m i j ≤ (decode s (query (lab i) (lab j)) : ℝ≥0∞)
  /-- The query gives at most `(U + 4) / U` times the metric. -/
  val_hi : ∀ i j, i ≠ j →
    (U : ℝ≥0∞) * (decode s (query (lab i) (lab j)) : ℝ≥0∞) ≤ ((U : ℝ≥0∞) + 4) * m i j

/-- **One bag.** A feasible point gives labels. -/
theorem exists_bagOK {C Cl cl U s B : ℕ} (hC : RealizationBox C) {query : List ℕ → List ℕ → ℕ∞}
    (hq : LabelQuery Cl cl U query) (hU : 1 ≤ U) (hs : 1 ≤ s) (hB : 1 ≤ B) {k : ℕ} (hk : 1 ≤ k)
    (hks : C * (k + 1) ^ 6 ≤ s) {w m : Fin k → Fin k → ℝ≥0∞} (hm : MongeMetric m)
    (hlo : ∀ i j, w i j ≤ m i j) (hhi : ∀ i j, (U : ℝ≥0∞) * m i j ≤ ((U : ℝ≥0∞) + 4) * w i j)
    (hUB : ∀ i j, i ≠ j → (U : ℝ≥0∞) ≤ m i j ∧ m i j ≤ (B : ℝ≥0∞)) :
    ∃ lab, BagOK query s U s (Cl * Nat.log 2 (s + 2 * s * B + 2) ^ cl * U)
      ((s + 2 * s * B + 2) ^ cl) w lab m := by
  have hr := realizes_of_box hC hk hm
  obtain ⟨n, K, g, l, h1, h2, h3⟩ := hr
  have hV : K.numVertices ≤ s := h1.trans hks
  obtain ⟨lab, h4, h5⟩ := exists_labels hq hU hs hB K g l h2.planar hV h3 hUB
  exact ⟨lab, hm, ⟨n, K, g, l, hV, h2, h3⟩, hlo, hhi, fun i => (h4 i).1, fun i => (h4 i).2,
    fun i j hij => (h5 i j hij).1, fun i j hij => (h5 i j hij).2⟩

end SsspFlow
