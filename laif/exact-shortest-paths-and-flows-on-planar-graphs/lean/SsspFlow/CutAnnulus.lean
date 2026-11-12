import SsspFlow.CutMap

/-!
# Lemma S1 on the cut

The level-one annulus `A_1` of Theorem D as an `Annulus` (`WitnessInterval.lean`) on the cut
`C.cut` of `CutMap.lean`, and Lemma S1 for it, from the map, the path and the weights alone.

The darts of `R` carry weights `g` with `g (rev x) = g x`, and `P = p_0 … p_m` is a shortest path of
`R` from `p_0` to `p_m` whose darts have positive weights. A dart of the cut has the weight of the
dart of `R` it copies. An edge of the annulus joins two distinct vertices of the cut that a dart
joins, with the least weight of such a dart, and the copies of `p_t` lie at the position `pos t`,
the length of `p_0 … p_t`.

* `RotSystem.exists_isWalk_le`: a walk of `adjGraph` is a walk of darts of at most its length.
* `CutPath.short`: (P), a walk of the cut between copies of `p_u` and `p_v` is at least as long as
  `P` between them, since it is a walk of `R`.
* `CutPath.copy`: (B^σ), each copy of `P` is a walk of the cut of the length of `P`.
* `CutPath.witness_interval`: Lemma S1 for the cut.
-/

set_option autoImplicit false

namespace SsspFlow

open FourColor SimpleGraph

theorem Recursion.wlen_reverse {V : Type*} {G : SimpleGraph V} (w : Sym2 V → ℕ) {a b : V}
    (p : G.Walk a b) : wlen w p.reverse = wlen w p := by
  simp [wlen, Walk.edges_reverse, List.sum_reverse]

theorem Recursion.wlen_single {V : Type*} {G : SimpleGraph V} (w : Sym2 V → ℕ) {u v : V}
    (h : G.Adj u v) : wlen w (Walk.cons h Walk.nil) = w s(u, v) :=
  rfl

namespace RotSystem

variable {D : Type*} [Fintype D] [DecidableEq D] (R : RotSystem D)

/-- The least weight of a dart that joins the two ends of `s`. -/
noncomputable def edgeWeight (g : D → ℕ) (s : Sym2 R.Vertex) : ℕ :=
  sInf {n | ∃ x, s(R.tail x, R.head x) = s ∧ g x = n}

theorem edgeWeight_le (g : D → ℕ) {x : D} {u v : R.Vertex} (hx : R.tail x = u)
    (hy : R.head x = v) : R.edgeWeight g s(u, v) ≤ g x :=
  Nat.sInf_le ⟨x, by rw [hx, hy], rfl⟩

/-- Some dart from `u` to `v` has the weight of the edge. -/
theorem exists_dart_edgeWeight (g : D → ℕ) (hg : ∀ x, g (R.rev x) = g x) {u v : R.Vertex}
    (h : R.adjGraph.Adj u v) :
    ∃ x, R.tail x = u ∧ R.head x = v ∧ g x = R.edgeWeight g s(u, v) := by
  obtain ⟨x₀, hx₀, hy₀⟩ := h.2
  obtain ⟨x, hx, hgx⟩ := Nat.sInf_mem (s := {n | ∃ x, s(R.tail x, R.head x) = s(u, v) ∧ g x = n})
    ⟨g x₀, x₀, by rw [hx₀, hy₀], rfl⟩
  rcases Sym2.eq_iff.1 hx with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨x, h1, h2, hgx⟩
  · exact ⟨R.rev x, h2, by rw [R.head_rev, h1], (hg x).trans hgx⟩

/-- A walk of `adjGraph` is a walk of darts of at most its length. -/
theorem exists_isWalk_le (g : D → ℕ) (hg : ∀ x, g (R.rev x) = g x) : ∀ {u v : R.Vertex}
    (p : R.adjGraph.Walk u v),
    ∃ q : List D, R.IsWalk u q v ∧ (q.map g).sum ≤ Recursion.wlen (R.edgeWeight g) p
  | _, _, .nil => ⟨[], rfl, by simp [Recursion.wlen]⟩
  | _, _, .cons h p => by
      obtain ⟨q, hq, hs⟩ := exists_isWalk_le g hg p
      obtain ⟨x, hx, hy, hgx⟩ := R.exists_dart_edgeWeight g hg h
      refine ⟨x :: q, ⟨hx, by rw [hy]; exact hq⟩, ?_⟩
      simp only [Recursion.wlen, Walk.edges_cons, List.map_cons, List.sum_cons] at hs ⊢
      omega

namespace CutPath

variable {R} (C : R.CutPath) (g : D → ℕ)

/-- The length of `p_0 … p_t`; past `p_m` each step has length `1`. -/
def pos : ℕ → ℕ
  | 0 => 0
  | t + 1 => pos t + if t < C.m then g (C.e t) else 1

theorem pos_succ {t : ℕ} (ht : t < C.m) : C.pos g (t + 1) = C.pos g t + g (C.e t) := by
  simp [pos, ht]

theorem pos_strictMono (hpos : ∀ t, t < C.m → 1 ≤ g (C.e t)) : StrictMono (C.pos g) :=
  strictMono_nat_of_lt_succ fun t => by
    show C.pos g t < C.pos g t + if t < C.m then g (C.e t) else 1
    split_ifs with h
    · have := hpos t h
      omega
    · omega

/-- The `n` darts of `P` from `p_a` on. -/
theorem isWalk_seg {a n : ℕ} (h : a + n ≤ C.m) :
    R.IsWalk (C.v a) ((List.range' a n).map C.e) (C.v (a + n)) := by
  induction n generalizing a with
  | zero => exact rfl
  | succ n ih =>
    rw [List.range'_succ, List.map_cons]
    refine ⟨C.tail_e a (by omega), ?_⟩
    rw [C.head_e a (by omega), show a + (n + 1) = a + 1 + n by omega]
    exact ih (by omega)

theorem pos_seg {a n : ℕ} (h : a + n ≤ C.m) :
    C.pos g a + (((List.range' a n).map C.e).map g).sum = C.pos g (a + n) := by
  induction n generalizing a with
  | zero => simp
  | succ n ih =>
    rw [List.range'_succ, List.map_cons, List.map_cons, List.sum_cons,
      show a + (n + 1) = a + 1 + n by omega, ← ih (a := a + 1) (by omega),
      C.pos_succ g (t := a) (by omega)]
    omega

/-- The parts of a shortest path are shortest. -/
theorem le_of_isWalk (hP : ∀ q, R.IsWalk (C.v 0) q (C.v C.m) → C.pos g C.m ≤ (q.map g).sum)
    {u v : ℕ} (huv : u ≤ v) (hv : v ≤ C.m) {q : List D} (hq : R.IsWalk (C.v u) q (C.v v)) :
    C.pos g v ≤ C.pos g u + (q.map g).sum := by
  have h1 := C.isWalk_seg (a := 0) (n := u) (by omega)
  have h2 := C.isWalk_seg (a := v) (n := C.m - v) (by omega)
  have e1 := C.pos_seg g (a := 0) (n := u) (by omega)
  have e2 := C.pos_seg g (a := v) (n := C.m - v) (by omega)
  rw [Nat.zero_add] at h1 e1
  rw [show v + (C.m - v) = C.m by omega] at h2 e2
  have h := hP _ ((h1.append hq).append h2)
  simp only [List.map_append, List.sum_append] at h
  have h0 : C.pos g 0 = 0 := rfl
  omega

theorem short_le (hg : ∀ x, g (R.rev x) = g x)
    (hP : ∀ q, R.IsWalk (C.v 0) q (C.v C.m) → C.pos g C.m ≤ (q.map g).sum) {σ τ : Fin 2}
    {u v : ℕ} (huv : u ≤ v) (hv : v ≤ C.m)
    (p : C.cut.adjGraph.Walk (C.cut.tail (C.k σ u)) (C.cut.tail (C.k τ v))) :
    C.pos g v ≤ C.pos g u + Recursion.wlen (C.cut.edgeWeight (g ∘ Prod.fst)) p := by
  obtain ⟨q, hq, hs⟩ := C.cut.exists_isWalk_le (g ∘ Prod.fst) (fun x => hg x.1) p
  have hq' := C.isWalk_fst hq
  rw [C.tail_k (σ := σ) (t := u) (by omega), C.tail_k (σ := τ) hv] at hq'
  have h := C.le_of_isWalk g hP huv hv hq'
  rw [List.map_map] at h
  omega

/-- **(P)**: a walk of the cut between copies of `p_u` and `p_v` is at least as long as `P` between
them. -/
theorem short (hg : ∀ x, g (R.rev x) = g x) (hpos : ∀ t, t < C.m → 1 ≤ g (C.e t))
    (hP : ∀ q, R.IsWalk (C.v 0) q (C.v C.m) → C.pos g C.m ≤ (q.map g).sum) (σ τ : Fin 2)
    {u v : ℕ} (hu : u ≤ C.m) (hv : v ≤ C.m)
    (p : C.cut.adjGraph.Walk (C.cut.tail (C.k σ u)) (C.cut.tail (C.k τ v))) :
    Recursion.dP (C.pos g) u v ≤ Recursion.wlen (C.cut.edgeWeight (g ∘ Prod.fst)) p := by
  have hm := (C.pos_strictMono g hpos).monotone
  unfold Recursion.dP
  rcases le_total u v with huv | huv
  · have h1 := C.short_le g hg hP huv hv p
    have h2 := hm huv
    omega
  · have h1 := C.short_le g hg hP huv hu p.reverse
    rw [Recursion.wlen_reverse] at h1
    have h2 := hm huv
    omega

/-- The copy `σ` of `P` from `p_u` to `p_v`. -/
theorem exists_copyWalk (σ : Fin 2) {u : ℕ} (v : ℕ) (huv : u ≤ v) (hv : v ≤ C.m) :
    ∃ p : C.cut.adjGraph.Walk (C.cut.tail (C.k σ u)) (C.cut.tail (C.k σ v)),
      C.pos g u + Recursion.wlen (C.cut.edgeWeight (g ∘ Prod.fst)) p ≤ C.pos g v := by
  induction v, huv using Nat.le_induction with
  | base => exact ⟨Walk.nil, by simp [Recursion.wlen]⟩
  | succ v huv ih =>
    obtain ⟨p, hp⟩ := ih (by omega)
    obtain ⟨x, hx1, hxt, hxh⟩ := C.exists_copyDart σ (show v < C.m by omega)
    have hne : C.cut.tail (C.k σ v) ≠ C.cut.tail (C.k σ (v + 1)) := fun h =>
      absurd ((C.k_eq_iff (by omega) hv).1 (C.cut_tail_inj (C.k_mem (by omega)) (C.k_mem hv) h)).2
        (by omega)
    have hadj : C.cut.adjGraph.Adj (C.cut.tail (C.k σ v)) (C.cut.tail (C.k σ (v + 1))) :=
      ⟨hne, x, hxt, hxh⟩
    refine ⟨p.append (Walk.cons hadj Walk.nil), ?_⟩
    have hw := C.cut.edgeWeight_le (g ∘ Prod.fst) hxt hxh
    rw [Function.comp_apply, hx1] at hw
    rw [Recursion.wlen_append, Recursion.wlen_single, C.pos_succ g (t := v) (by omega)]
    omega

/-- **(B^σ)**: each copy of `P` is a walk of the cut of the length of `P`. -/
theorem copy (hg : ∀ x, g (R.rev x) = g x) (hpos : ∀ t, t < C.m → 1 ≤ g (C.e t))
    (hP : ∀ q, R.IsWalk (C.v 0) q (C.v C.m) → C.pos g C.m ≤ (q.map g).sum) (σ : Fin 2)
    {u v : ℕ} (hu : u ≤ C.m) (hv : v ≤ C.m) :
    ∃ p : C.cut.adjGraph.Walk (C.cut.tail (C.k σ u)) (C.cut.tail (C.k σ v)),
      Recursion.wlen (C.cut.edgeWeight (g ∘ Prod.fst)) p = Recursion.dP (C.pos g) u v := by
  have hm := (C.pos_strictMono g hpos).monotone
  rcases le_total u v with huv | huv
  · obtain ⟨p, hp⟩ := C.exists_copyWalk g σ v huv hv
    have h1 := C.short_le g hg hP huv hv p
    have h2 := hm huv
    exact ⟨p, by unfold Recursion.dP; omega⟩
  · obtain ⟨p, hp⟩ := C.exists_copyWalk g σ u huv hu
    have h1 := C.short_le g hg hP huv hu p
    have h2 := hm huv
    refine ⟨p.reverse, ?_⟩
    rw [Recursion.wlen_reverse]
    unfold Recursion.dP
    omega

/-- The level-one annulus on the cut. -/
noncomputable def annulus (hg : ∀ x, g (R.rev x) = g x) (hpos : ∀ t, t < C.m → 1 ≤ g (C.e t))
    (hP : ∀ q, R.IsWalk (C.v 0) q (C.v C.m) → C.pos g C.m ≤ (q.map g).sum) :
    Recursion.Annulus C.cut.Vertex where
  G := C.cut.adjGraph
  w := C.cut.edgeWeight (g ∘ Prod.fst)
  m := C.m
  pos := C.pos g
  c σ t := C.cut.tail (C.k σ t)
  mono := C.pos_strictMono g hpos
  copy σ _ _ hu hv := C.copy g hg hpos hP σ hu hv
  short σ τ _ _ hu hv p := C.short g hg hpos hP σ τ hu hv p

/-- **Lemma S1 on the cut.** Let `R` be planar and connected, and `P` a shortest path of `R` from
`p_0` to `p_m` with positive weights. A shortest walk of the cut between the two copies of `p_i`
meets the copies of `p_t` exactly for `t` in an interval `[i1, i2]` around `i`, and each `t` strictly
inside has the largest `λ` on `[i1, t]` or on `[t, i2]`. -/
theorem witness_interval (hR : R.Planar) (hc : R.Connected) (hg : ∀ x, g (R.rev x) = g x)
    (hpos : ∀ t, t < C.m → 1 ≤ g (C.e t))
    (hP : ∀ q, R.IsWalk (C.v 0) q (C.v C.m) → C.pos g C.m ≤ (q.map g).sum) {i : ℕ} (hi : i ≤ C.m)
    (W : C.cut.adjGraph.Walk (C.cut.tail (C.k 0 i)) (C.cut.tail (C.k 1 i)))
    (hW : Recursion.wlen (C.cut.edgeWeight (g ∘ Prod.fst)) W = (C.annulus g hg hpos hP).lam i) :
    ∃ i1 i2, IsLeast ((C.annulus g hg hpos hP).copies W) i1 ∧
      IsGreatest ((C.annulus g hg hpos hP).copies W) i2 ∧ i1 ≤ i ∧ i ≤ i2 ∧
      ∀ t, i1 < t → t < i2 →
        (∀ q, i1 ≤ q → q ≤ t → (C.annulus g hg hpos hP).lam q ≤ (C.annulus g hg hpos hP).lam t) ∨
        (∀ q, t ≤ q → q ≤ i2 → (C.annulus g hg hpos hP).lam q ≤ (C.annulus g hg hpos hP).lam t) :=
  (C.annulus g hg hpos hP).witness_interval_of_faceDrawn le_rfl C.k (fun _ _ _ => rfl)
    (C.faceDrawn hR hc) hi W hW

end CutPath

end RotSystem

end SsspFlow
