import SsspFlow.WalkCut
import SsspFlow.Overlap

/-!
# Distances on one side of a walk cut

Let `W` be a `WalkCut` of the split `M = R.double.split Γ` along a walk `q 0, …, q (n - 1)` from the
vertex of `ka` to the vertex of `kb`, and let `M'` be the cut `R.double.split W.Γ'`. A walk of `M'`
is a walk of `M` (`isWalk_of_split_subset`). If the walk `q` is a shortest walk of `M` between its
ends, a walk of `M` between two darts of the side of `ka` gives a walk of `M'` between them that is
no longer (`WalkCut.reroute`). It follows the first walk up to its first vertex on `q`, runs along
the copies `(d, true)` of the edges of `q` to its last vertex on `q`, and follows the first walk from
there. So on the side of `ka` the distances of `M'` are the distances of `M`
(`WalkCut.walkDist_hi`). This is (INV) of Lemma O for the called side.
-/

set_option autoImplicit false

namespace SsspFlow

open FourColor
open scoped ENNReal

namespace RotSystem

section Walks

variable {E : Type*} [Fintype E] [DecidableEq E] {M : RotSystem E}

/-- **The first visit.** A walk that visits a set of vertices splits at its first visit. -/
theorem IsWalk.split_first (S : M.Vertex → Prop) {p : List E} : ∀ {u v : M.Vertex},
    M.IsWalk u p v → (S u ∨ ∃ x ∈ p, S (M.head x)) →
    ∃ p₁ p₂ s, p = p₁ ++ p₂ ∧ M.IsWalk u p₁ s ∧ M.IsWalk s p₂ v ∧ S s ∧
      ∀ x ∈ p₁, ¬ S (M.tail x) := by
  induction p with
  | nil =>
    intro u v hp hS
    obtain rfl : u = v := hp
    refine ⟨[], [], u, rfl, rfl, rfl, ?_, by simp⟩
    rcases hS with h | ⟨x, hx, _⟩
    · exact h
    · simp at hx
  | cons x p ih =>
    intro u v hp hS
    by_cases hu : S u
    · exact ⟨[], x :: p, u, rfl, rfl, hp, hu, by simp⟩
    · have hS' : S (M.head x) ∨ ∃ y ∈ p, S (M.head y) := by
        rcases hS with h | ⟨y, hy, hy'⟩
        · exact absurd h hu
        · rcases List.mem_cons.1 hy with rfl | hy
          · exact Or.inl hy'
          · exact Or.inr ⟨y, hy, hy'⟩
      obtain ⟨p₁, p₂, s, rfl, h1, h2, hs, hn⟩ := ih hp.2 hS'
      refine ⟨x :: p₁, p₂, s, rfl, ⟨hp.1, h1⟩, h2, hs, fun y hy => ?_⟩
      rcases List.mem_cons.1 hy with rfl | hy
      · rw [hp.1]
        exact hu
      · exact hn y hy

/-- **The last visit.** A walk that visits a set of vertices splits at its last visit. -/
theorem IsWalk.split_last (S : M.Vertex → Prop) {p : List E} : ∀ {u v : M.Vertex},
    M.IsWalk u p v → (S u ∨ ∃ x ∈ p, S (M.head x)) →
    ∃ p₁ p₂ s, p = p₁ ++ p₂ ∧ M.IsWalk u p₁ s ∧ M.IsWalk s p₂ v ∧ S s ∧
      ∀ x ∈ p₂, ¬ S (M.head x) := by
  induction p with
  | nil =>
    intro u v hp hS
    obtain rfl : u = v := hp
    refine ⟨[], [], u, rfl, rfl, rfl, ?_, by simp⟩
    rcases hS with h | ⟨x, hx, _⟩
    · exact h
    · simp at hx
  | cons x p ih =>
    intro u v hp hS
    by_cases hl : S (M.head x) ∨ ∃ y ∈ p, S (M.head y)
    · obtain ⟨p₁, p₂, s, rfl, h1, h2, hs, hn⟩ := ih hp.2 hl
      exact ⟨x :: p₁, p₂, s, rfl, ⟨hp.1, h1⟩, h2, hs, hn⟩
    · have hu : S u := by
        rcases hS with h | ⟨y, hy, hy'⟩
        · exact h
        · rcases List.mem_cons.1 hy with rfl | hy
          · exact absurd (Or.inl hy') hl
          · exact absurd (Or.inr ⟨y, hy, hy'⟩) hl
      refine ⟨[], x :: p, u, rfl, rfl, hp, hu, fun y hy h => ?_⟩
      rcases List.mem_cons.1 hy with rfl | hy
      · exact hl (Or.inl h)
      · exact hl (Or.inr ⟨y, hy, h⟩)

/-- Darts `f a, …, f (a + k - 1)` with `f j` from `V j` to `V (j + 1)` form a walk. -/
theorem isWalk_range' (V : ℕ → M.Vertex) (f : ℕ → E) (k : ℕ) : ∀ (a : ℕ),
    (∀ j, a ≤ j → j < a + k → M.tail (f j) = V j ∧ M.head (f j) = V (j + 1)) →
    M.IsWalk (V a) ((List.range' a k).map f) (V (a + k)) := by
  induction k with
  | zero => intro a _; rfl
  | succ k ih =>
    intro a h
    rw [List.range'_succ, List.map_cons]
    refine ⟨(h a le_rfl (by omega)).1, ?_⟩
    rw [(h a le_rfl (by omega)).2, show a + (k + 1) = a + 1 + k by omega]
    exact ih (a + 1) fun j h1 h2 => h j (by omega) (by omega)

end Walks

variable {D : Type*} [Fintype D] [DecidableEq D] {R : RotSystem D}

/-- A walk of the split at a larger set is a walk of the split. -/
theorem isWalk_of_split_subset {Γ Γ₀ : Finset (D × Bool)} (h : Γ ⊆ Γ₀) {p : List (D × Bool)} :
    ∀ {a b : D × Bool},
    (R.double.split Γ₀).IsWalk ((R.double.split Γ₀).tail a) p ((R.double.split Γ₀).tail b) →
      (R.double.split Γ).IsWalk ((R.double.split Γ).tail a) p ((R.double.split Γ).tail b) := by
  induction p with
  | nil =>
    intro a b hp
    exact ((R.double.split Γ).tail_eq_iff a b).2
      (fconnect_of_split_subset h (((R.double.split Γ₀).tail_eq_iff a b).1 hp))
  | cons x p ih =>
    intro a b hp
    exact ⟨((R.double.split Γ).tail_eq_iff x a).2
      (fconnect_of_split_subset h (((R.double.split Γ₀).tail_eq_iff x a).1 hp.1)),
      ih (a := R.double.rev x) hp.2⟩

/-- Distances do not shrink when more corners are split. -/
theorem walkDist_le_of_split_subset {Γ Γ₀ : Finset (D × Bool)} (h : Γ ⊆ Γ₀)
    (g : D × Bool → ℝ≥0∞) (a b : D × Bool) :
    (R.double.split Γ).walkDist g ((R.double.split Γ).tail a) ((R.double.split Γ).tail b) ≤
      (R.double.split Γ₀).walkDist g ((R.double.split Γ₀).tail a) ((R.double.split Γ₀).tail b) :=
  le_iInf₂ fun _ hp => walkDist_le g (isWalk_of_split_subset h hp)

namespace WalkCut

variable {Γ : Finset (D × Bool)} (W : R.WalkCut Γ)

/-- The vertices of the walk: the vertices of the corners `hc 0, …, hc n` of the split. -/
def OnWalk (v : (R.double.split Γ).Vertex) : Prop :=
  ∃ k, k ≤ W.n ∧ v = (R.double.split Γ).tail (W.hc k)

/-- The copies `(d, true)` of the edges `a, …, b - 1`. -/
def copySeg (a b : ℕ) : List (D × Bool) := (List.range' a (b - a)).map fun j => ((W.q j).1, true)

/-- The darts `q a, …, q (b - 1)`. -/
def qSeg (a b : ℕ) : List (D × Bool) := (List.range' a (b - a)).map W.q

theorem sum_copySeg (g : D → ℝ≥0∞) (a b : ℕ) :
    ((W.copySeg a b).map (g ∘ Prod.fst)).sum = ((W.qSeg a b).map (g ∘ Prod.fst)).sum := by
  simp only [copySeg, qSeg, List.map_map]
  rfl

theorem qSeg_append {a b c : ℕ} (hab : a ≤ b) (hbc : b ≤ c) :
    W.qSeg a b ++ W.qSeg b c = W.qSeg a c := by
  simp only [qSeg]
  rw [← List.map_append]
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hab
  obtain ⟨l, rfl⟩ := Nat.exists_eq_add_of_le hbc
  rw [show a + k - a = k by omega, show a + k + l - (a + k) = l by omega,
    show a + k + l - a = k + l by omega, List.range'_append_1]

section Side

variable (hR : R.Planar) (hC : R.Connected) (hS : R.double.SkeletonConnected Γ)
include hR hC hS

theorem tail_q {k : ℕ} (hk : k < W.n) :
    (R.double.split Γ).tail (W.q k) = (R.double.split Γ).tail (W.hc k) :=
  ((R.double.split Γ).tail_eq_iff _ _).2 (W.fconnect_hc hR hC hS hk)

theorem tail_hc_n : (R.double.split Γ).tail (W.hc W.n) = (R.double.split Γ).tail W.kb := by
  have hF := W.final hR hC hS
  rw [W.hc_eq_rc W.pos]
  exact ((R.double.split Γ).tail_eq_iff _ _).2 hF.2.2.2.2

theorem head_q {k : ℕ} (hk : k < W.n) :
    (R.double.split Γ).head (W.q k) = (R.double.split Γ).tail (W.hc (k + 1)) := by
  rcases Nat.lt_or_ge (k + 1) W.n with h | h
  · rw [← W.tail_q hR hC hS h]
    exact ((R.double.split Γ).tail_eq_iff _ _).2 (W.walk k h)
  · obtain rfl : k = W.n - 1 := by omega
    rw [show W.n - 1 + 1 = W.n by have := W.pos; omega, W.tail_hc_n hR hC hS]
    exact ((R.double.split Γ).tail_eq_iff _ _).2 W.stop

/-- A dart off the walk is at a vertex that does not change. -/
theorem tail_cut_iff {z : D × Bool} (hz : ¬ W.OnWalk ((R.double.split Γ).tail z)) (y : D × Bool) :
    (R.double.split W.Γ').tail z = (R.double.split W.Γ').tail y ↔
      (R.double.split Γ).tail z = (R.double.split Γ).tail y := by
  rw [(R.double.split W.Γ').tail_eq_iff, (R.double.split Γ).tail_eq_iff]
  refine W.fconnect_cut_iff (fun k hk h => hz ⟨k, hk.le, ?_⟩) (fun h => hz ⟨W.n, le_rfl, ?_⟩)
  · rw [← W.tail_q hR hC hS hk]
    exact ((R.double.split Γ).tail_eq_iff _ _).2 h
  · rw [W.tail_hc_n hR hC hS]
    exact ((R.double.split Γ).tail_eq_iff _ _).2 h

/-- A dart at a vertex of the walk on the side of `ka` lies at the part `hc k` of that vertex. -/
theorem tail_cut_of_on {k : ℕ} (hk : k ≤ W.n) {z : D × Bool}
    (hz : (R.double.split Γ).tail z = (R.double.split Γ).tail (W.hc k))
    (hg : (R.double.split W.Γ').toHypermap.gcomp W.ka z) :
    (R.double.split W.Γ').tail z = (R.double.split W.Γ').tail (W.hc k) := by
  refine ((R.double.split W.Γ').tail_eq_iff _ _).2 ?_
  rcases hk.lt_or_eq with hk | rfl
  · rw [← W.tail_q hR hC hS hk] at hz
    exact W.part_hi hR hC hS hk (((R.double.split Γ).tail_eq_iff _ _).1 hz) hg
  · rw [W.tail_hc_n hR hC hS] at hz
    rw [W.hc_eq_rc W.pos]
    exact W.part_hi_last hR hC hS (((R.double.split Γ).tail_eq_iff _ _).1 hz) hg

/-- A walk off the walk of the cut is a walk of the cut. -/
theorem lift_off {p : List (D × Bool)} : ∀ {a b : D × Bool},
    (R.double.split Γ).IsWalk ((R.double.split Γ).tail a) p ((R.double.split Γ).tail b) →
    ¬ W.OnWalk ((R.double.split Γ).tail a) →
    (∀ x ∈ p, ¬ W.OnWalk ((R.double.split Γ).head x)) →
    (R.double.split W.Γ').IsWalk ((R.double.split W.Γ').tail a) p
      ((R.double.split W.Γ').tail b) := by
  induction p with
  | nil =>
    intro a b hp ha _
    exact (W.tail_cut_iff hR hC hS ha b).2 hp
  | cons x p ih =>
    intro a b hp ha hoff
    have hx : ¬ W.OnWalk ((R.double.split Γ).tail x) := by rw [hp.1]; exact ha
    exact ⟨(W.tail_cut_iff hR hC hS hx a).2 hp.1,
      ih (a := R.double.rev x) hp.2 (hoff x (by simp)) fun y hy => hoff y (by simp [hy])⟩

/-- A walk to a vertex of the walk of the cut that meets it only at its end, from a dart of the side
of `ka`, is a walk of the cut to the part of that vertex on the side of `ka`. -/
theorem lift_first {k : ℕ} (hk : k ≤ W.n) {p : List (D × Bool)} : ∀ {a : D × Bool},
    (R.double.split Γ).IsWalk ((R.double.split Γ).tail a) p ((R.double.split Γ).tail (W.hc k)) →
    (∀ x ∈ p, ¬ W.OnWalk ((R.double.split Γ).tail x)) →
    (R.double.split W.Γ').toHypermap.gcomp W.ka a →
    (R.double.split W.Γ').IsWalk ((R.double.split W.Γ').tail a) p
      ((R.double.split W.Γ').tail (W.hc k)) := by
  induction p with
  | nil =>
    intro a hp _ ha
    exact W.tail_cut_of_on hR hC hS hk hp ha
  | cons x p ih =>
    intro a hp hoff ha
    have hx : (R.double.split W.Γ').tail x = (R.double.split W.Γ').tail a :=
      (W.tail_cut_iff hR hC hS (hoff x (by simp)) a).2 hp.1
    have hax : (R.double.split W.Γ').toHypermap.gcomp a x :=
      (R.double.split W.Γ').toHypermap.gcomp_of_cnode
        (((R.double.split W.Γ').tail_eq_iff a x).1 hx.symm)
    refine ⟨hx, ih (a := R.double.rev x) hp.2 (fun y hy => hoff y (by simp [hy])) ?_⟩
    exact connect_trans ha (connect_trans hax
      (connect_of_rel ((R.double.split W.Γ').toHypermap.glinkE x)))

/-- A walk from a vertex of the walk of the cut that meets it only at its start, to a dart of the
side of `ka`, is a walk of the cut from the part of that vertex on the side of `ka`. -/
theorem lift_last {k : ℕ} (hk : k ≤ W.n) {p : List (D × Bool)} {b : D × Bool}
    (hp : (R.double.split Γ).IsWalk ((R.double.split Γ).tail (W.hc k)) p
      ((R.double.split Γ).tail b))
    (hoff : ∀ x ∈ p, ¬ W.OnWalk ((R.double.split Γ).head x))
    (hb : (R.double.split W.Γ').toHypermap.gcomp W.ka b) :
    (R.double.split W.Γ').IsWalk ((R.double.split W.Γ').tail (W.hc k)) p
      ((R.double.split W.Γ').tail b) := by
  have h := W.lift_first hR hC hS hk hp.reverse (fun x hx => ?_) hb
  · have e : (R.double.split Γ).reverseCycle p = (R.double.split W.Γ').reverseCycle p := rfl
    have h' := h.reverse
    rwa [e, reverseCycle_reverseCycle] at h'
  · simp only [reverseCycle, List.mem_reverse, List.mem_map] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact hoff y hy

theorem isWalk_copySeg {a b : ℕ} (hab : a ≤ b) (hb : b ≤ W.n) :
    (R.double.split W.Γ').IsWalk ((R.double.split W.Γ').tail (W.hc a)) (W.copySeg a b)
      ((R.double.split W.Γ').tail (W.hc b)) := by
  have h := isWalk_range' (fun j => (R.double.split W.Γ').tail (W.hc j))
    (fun j => ((W.q j).1, true)) (b - a) a fun j _ h2 =>
      ⟨((R.double.split W.Γ').tail_eq_iff _ _).2 (W.fconnect_copy hR hC hS (by omega)), rfl⟩
  rwa [show a + (b - a) = b by omega] at h

theorem isWalk_qSeg {a b : ℕ} (hab : a ≤ b) (hb : b ≤ W.n) :
    (R.double.split Γ).IsWalk ((R.double.split Γ).tail (W.hc a)) (W.qSeg a b)
      ((R.double.split Γ).tail (W.hc b)) := by
  have h := isWalk_range' (fun j => (R.double.split Γ).tail (W.hc j)) W.q (b - a) a
    fun j _ h2 => ⟨W.tail_q hR hC hS (by omega), W.head_q hR hC hS (by omega)⟩
  rwa [show a + (b - a) = b by omega] at h

variable (g : D → ℝ≥0∞)
  (hQ : ∀ p, (R.double.split Γ).IsWalk ((R.double.split Γ).tail W.ka) p
      ((R.double.split Γ).tail W.kb) →
    ((W.qSeg 0 W.n).map (g ∘ Prod.fst)).sum ≤ (p.map (g ∘ Prod.fst)).sum)
  (hfin : ((W.qSeg 0 W.n).map (g ∘ Prod.fst)).sum ≠ ⊤)
include hQ hfin

/-- A part of a shortest walk is a shortest walk between its ends. -/
theorem qSeg_short {a b : ℕ} (hab : a ≤ b) (hb : b ≤ W.n) {r : List (D × Bool)}
    (hr : (R.double.split Γ).IsWalk ((R.double.split Γ).tail (W.hc a)) r
      ((R.double.split Γ).tail (W.hc b))) :
    ((W.qSeg a b).map (g ∘ Prod.fst)).sum ≤ (r.map (g ∘ Prod.fst)).sum := by
  have hsplit : W.qSeg 0 W.n = W.qSeg 0 a ++ W.qSeg a b ++ W.qSeg b W.n := by
    rw [W.qSeg_append (Nat.zero_le a) hab, W.qSeg_append (Nat.zero_le b) hb]
  have hw : (R.double.split Γ).IsWalk ((R.double.split Γ).tail W.ka)
      (W.qSeg 0 a ++ r ++ W.qSeg b W.n) ((R.double.split Γ).tail W.kb) := by
    rw [← W.tail_hc_n hR hC hS]
    exact ((W.isWalk_qSeg hR hC hS (Nat.zero_le a) (hab.trans hb)).append hr).append
      (W.isWalk_qSeg hR hC hS hb le_rfl)
  have hle := hQ _ hw
  rw [hsplit] at hle hfin
  simp only [List.map_append, List.sum_append] at hle hfin
  have h1 : ((W.qSeg 0 a).map (g ∘ Prod.fst)).sum ≠ ⊤ := fun h => hfin (by simp [h])
  have h3 : ((W.qSeg b W.n).map (g ∘ Prod.fst)).sum ≠ ⊤ := fun h => hfin (by simp [h])
  exact (ENNReal.add_le_add_iff_left h1).1 ((ENNReal.add_le_add_iff_right h3).1 hle)

/-- **Rerouting along the copy of the walk.** If the walk of the cut is a shortest walk between its
ends, a walk of the split between two darts of the side of `ka` gives a walk of the cut between them
that is no longer. -/
theorem reroute (hg : ∀ x, g (R.rev x) = g x) {a b : D × Bool}
    (ha : (R.double.split W.Γ').toHypermap.gcomp W.ka a)
    (hb : (R.double.split W.Γ').toHypermap.gcomp W.ka b) {p : List (D × Bool)}
    (hp : (R.double.split Γ).IsWalk ((R.double.split Γ).tail a) p ((R.double.split Γ).tail b)) :
    ∃ p', (R.double.split W.Γ').IsWalk ((R.double.split W.Γ').tail a) p'
      ((R.double.split W.Γ').tail b) ∧
      (p'.map (g ∘ Prod.fst)).sum ≤ (p.map (g ∘ Prod.fst)).sum := by
  have hg' : ∀ x, (g ∘ Prod.fst) ((R.double.split Γ).rev x) = (g ∘ Prod.fst) x :=
    fun x => hg x.1
  by_cases hvis : W.OnWalk ((R.double.split Γ).tail a) ∨
      ∃ x ∈ p, W.OnWalk ((R.double.split Γ).head x)
  · obtain ⟨p₁, p₂, s₁, rfl, h1, h2, ⟨k₁, hk₁, rfl⟩, hn1⟩ := hp.split_first W.OnWalk hvis
    obtain ⟨p₂', p₃, s₂, rfl, h2', h3, ⟨k₂, hk₂, rfl⟩, hn3⟩ :=
      h2.split_last W.OnWalk (Or.inl ⟨k₁, hk₁, rfl⟩)
    have l1 := W.lift_first hR hC hS hk₁ h1 hn1 ha
    have l3 := W.lift_last hR hC hS hk₂ h3 hn3 hb
    rcases le_total k₁ k₂ with h12 | h21
    · refine ⟨p₁ ++ W.copySeg k₁ k₂ ++ p₃,
        (l1.append (W.isWalk_copySeg hR hC hS h12 hk₂)).append l3, ?_⟩
      have hs := W.qSeg_short hR hC hS g hQ hfin h12 hk₂ h2'
      simp only [List.map_append, List.sum_append, W.sum_copySeg]
      calc _ ≤ (p₁.map (g ∘ Prod.fst)).sum + (p₂'.map (g ∘ Prod.fst)).sum +
            (p₃.map (g ∘ Prod.fst)).sum := by gcongr
        _ = _ := by ring
    · refine ⟨p₁ ++ (R.double.split W.Γ').reverseCycle (W.copySeg k₂ k₁) ++ p₃,
        (l1.append (W.isWalk_copySeg hR hC hS h21 hk₁).reverse).append l3, ?_⟩
      have hs := W.qSeg_short hR hC hS g hQ hfin h21 hk₁ h2'.reverse
      rw [sum_map_reverseCycle _ hg'] at hs
      have e : ((R.double.split W.Γ').reverseCycle (W.copySeg k₂ k₁)).map (g ∘ Prod.fst) =
          ((R.double.split Γ).reverseCycle (W.copySeg k₂ k₁)).map (g ∘ Prod.fst) := rfl
      simp only [List.map_append, List.sum_append, e, sum_map_reverseCycle _ hg', W.sum_copySeg]
      calc _ ≤ (p₁.map (g ∘ Prod.fst)).sum + (p₂'.map (g ∘ Prod.fst)).sum +
            (p₃.map (g ∘ Prod.fst)).sum := by gcongr
        _ = _ := by ring
  · push Not at hvis
    exact ⟨p, W.lift_off hR hC hS hp hvis.1 hvis.2, le_rfl⟩

/-- **(INV) for the called side.** If the walk of the cut is a shortest walk between its ends, the
distance of the cut between two darts of the side of `ka` is their distance before the cut. -/
theorem walkDist_hi (hg : ∀ x, g (R.rev x) = g x) {a b : D × Bool}
    (ha : (R.double.split W.Γ').toHypermap.gcomp W.ka a)
    (hb : (R.double.split W.Γ').toHypermap.gcomp W.ka b) :
    (R.double.split W.Γ').walkDist (g ∘ Prod.fst) ((R.double.split W.Γ').tail a)
      ((R.double.split W.Γ').tail b) =
    (R.double.split Γ).walkDist (g ∘ Prod.fst) ((R.double.split Γ).tail a)
      ((R.double.split Γ).tail b) := by
  refine le_antisymm (le_iInf₂ fun p hp => ?_) (walkDist_le_of_split_subset W.subset_Γ' _ a b)
  obtain ⟨p', hp', hle⟩ := W.reroute hR hC hS g hQ hfin hg ha hb hp
  exact (walkDist_le _ hp').trans hle

end Side

end WalkCut

end RotSystem

end SsspFlow
