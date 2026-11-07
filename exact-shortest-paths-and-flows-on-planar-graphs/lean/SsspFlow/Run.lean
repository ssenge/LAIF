import SsspFlow.Pieces
import SsspFlow.CutAnnulus

/-!
# A run of the recursion

A run of the recursion ShortestCycle of [18, Alg. 3] on a live annulus with the index range `[j, k]`
(`CutPath.Run`). A leaf has `k ≤ j + 1` and computes the lengths at `j` and `k`. Any other annulus
computes a shortest walk `P_i` from `κ0(i)` to `κ1(i)` for `i = ⌊(j + k)/2⌋`, the least and the
greatest index `i1` and `i2` of a copy of the path at a vertex of `P_i`, read in the cut
(`CutPath.idx`), and a step of `P_i`. It computes the lengths at `i`, `max i1 j` and `min i2 k`.
Each side has an overlap, if `P_i` passes through a corner of its bound, and then the overlap rule
computes the length through that corner for every index between the end of the range and `i`; or it
is called as the child annulus on its side of the step; or its range is empty. The bound of the side
of `κ0(x_a)` is `κ0(x_a), L_a, κ1(y_a)`, and that of the side of `κ0(x_b)` is `κ0(x_b), L_b, κ1(y_b)`;
the two end corners belong to the bound also where no bounding path exists.

Every computed length is `λ_t` of its index `t` (`Run.vals_eq`): in the annulus by (INV), and through
the corner of an overlap by (C23). Lemma S1 holds for the image of `P_i` in the cut (`Live.dom`), so
a run gives a tree of the index model of `Recursion.lean` with the same computed indices
(`Run.toRec`, `Run.computed_eq`), and by Lemma S2 the least computed length of a run on the cut is
the least `λ_t` (`Run.isLeast`). A run on the cut exists (`nonempty_run`): a side without overlap
avoids its bound, so its child is a live annulus. `recursion_cut` collects these facts.
-/

set_option autoImplicit false

universe u

namespace SsspFlow

open FourColor SimpleGraph
open scoped ENNReal

noncomputable section

namespace RotSystem

section Bridge

variable {E : Type*} [Fintype E] [DecidableEq E] {M : RotSystem E}

/-- A walk of darts gives a walk of the simple graph of the map, through the same vertices and of at
most its length. -/
theorem IsWalk.exists_adjWalk (g : E → ℕ) {p : List E} : ∀ {u v : M.Vertex}, M.IsWalk u p v →
    ∃ W : M.adjGraph.Walk u v, Recursion.wlen (M.edgeWeight g) W ≤ (p.map g).sum ∧
      ∀ z, z ∈ W.support ↔ z = u ∨ z ∈ p.map M.head := by
  induction p with
  | nil =>
    intro u v h
    obtain rfl : u = v := h
    exact ⟨.nil, by simp [Recursion.wlen], fun z => by simp⟩
  | cons x p ih =>
    intro u v h
    obtain ⟨hx, hw⟩ : M.tail x = u ∧ M.IsWalk (M.head x) p v := h
    obtain ⟨W, hW, hs⟩ := ih hw
    by_cases hl : u = M.head x
    · refine ⟨W.copy hl.symm rfl, ?_, fun z => ?_⟩
      · rw [Recursion.wlen_copy, List.map_cons, List.sum_cons]
        omega
      · rw [Walk.support_copy, hs z, List.map_cons, List.mem_cons, ← hl]
        tauto
    · have hadj : M.adjGraph.Adj u (M.head x) := ⟨hl, x, hx, rfl⟩
      refine ⟨.cons hadj W, ?_, fun z => ?_⟩
      · have := M.edgeWeight_le g hx rfl
        simp only [Recursion.wlen, Walk.edges_cons, List.map_cons, List.sum_cons] at hW ⊢
        omega
      · rw [SimpleGraph.Walk.support_cons, List.mem_cons, hs z, List.map_cons, List.mem_cons]

/-- The tail of each dart of a walk is a vertex of the walk. -/
theorem IsWalk.tail_mem {p : List E} : ∀ {u v : M.Vertex}, M.IsWalk u p v → ∀ y ∈ p,
    M.tail y = u ∨ ∃ y' ∈ p, M.head y' = M.tail y := by
  induction p with
  | nil => intro u v _ y hy; simp at hy
  | cons x p ih =>
    intro u v h y hy
    rcases List.mem_cons.1 hy with rfl | hy
    · exact Or.inl h.1
    · rcases ih h.2 y hy with e | ⟨y', hy', e⟩
      · exact Or.inr ⟨x, List.mem_cons_self, e.symm⟩
      · exact Or.inr ⟨y', List.mem_cons_of_mem _ hy', e⟩

end Bridge

/-- A sum of natural weights read in `ℝ≥0∞`. -/
theorem sum_cast_fst {α : Type*} (g₀ : α → ℕ) (p : List (α × Bool)) :
    (p.map ((Nat.cast ∘ g₀ : α → ℝ≥0∞) ∘ Prod.fst)).sum = ((p.map (g₀ ∘ Prod.fst)).sum : ℝ≥0∞) := by
  rw [Nat.cast_list_sum, List.map_map]
  rfl

variable {D : Type u} [Fintype D] [DecidableEq D] {R : RotSystem D}

namespace CutPath

variable (C : R.CutPath)

/-- A walk of the cut joins any two corners of `Γ`. -/
theorem exists_walk (hR : R.Planar) (hC : R.Connected) {a b : D × Bool} (ha : a ∈ C.Γ)
    (hb : b ∈ C.Γ) : ∃ p, C.cut.IsWalk (C.cut.tail a) p (C.cut.tail b) := by
  have hbd : R.double.Boundary C.Γ (Recursion.copyCorners C.k C.m) :=
    ⟨C.nodup, fun c hc => List.mem_toFinset.2 hc, fun c _ => by rw [C.psi_eq]⟩
  exact (C.cut.gcomp_iff a b).1 ((hbd.gcomp_iff (R.double_planar hR hC) (R.double_connected hC)
    C.Γ_nonempty C.skeletonConnected (List.mem_toFinset.1 ha) hb).2 (List.mem_toFinset.1 hb))

/-- The indices `r ≤ m` of the copies `p_r^σ` at the vertices of a walk `p` from the tail of `a`,
read in the cut. -/
def idx (a : D × Bool) (p : List (D × Bool)) : Set ℕ :=
  {r | r ≤ C.m ∧ ∃ σ, C.cut.tail (C.k σ r) = C.cut.tail a ∨
    ∃ y ∈ p, C.cut.head y = C.cut.tail (C.k σ r)}

section Annulus

variable (g₀ : D → ℕ) (hg₀ : ∀ x, g₀ (R.rev x) = g₀ x) (hpos : ∀ t, t < C.m → 1 ≤ g₀ (C.e t))
  (hP : ∀ q, R.IsWalk (C.v 0) q (C.v C.m) → C.pos g₀ C.m ≤ (q.map g₀).sum)

/-- `λ_t` as a distance of darts in the cut is `λ_t` of the level-one annulus. -/
theorem lamD_eq (hR : R.Planar) (hC : R.Connected) {t : ℕ} (ht : t ≤ C.m) :
    C.lamD (Nat.cast ∘ g₀) t = ((C.annulus g₀ hg₀ hpos hP).lam t : ℝ≥0∞) := by
  refine le_antisymm ?_ ?_
  · obtain ⟨p₀, hp₀⟩ := C.exists_walk hR hC (C.k_mem (σ := 0) ht) (C.k_mem (σ := 1) ht)
    obtain ⟨W₀, -, -⟩ := hp₀.exists_adjWalk (g₀ ∘ Prod.fst)
    obtain ⟨W, hW⟩ := (C.annulus g₀ hg₀ hpos hP).exists_lam W₀
    obtain ⟨q, hq, hs⟩ := C.cut.exists_isWalk_le (g₀ ∘ Prod.fst) (fun x => hg₀ x.1) W
    calc C.lamD (Nat.cast ∘ g₀) t ≤ (q.map ((Nat.cast ∘ g₀ : D → ℝ≥0∞) ∘ Prod.fst)).sum :=
          walkDist_le _ hq
      _ = ((q.map (g₀ ∘ Prod.fst)).sum : ℝ≥0∞) := sum_cast_fst g₀ q
      _ ≤ _ := by rw [← hW]; exact_mod_cast hs
  · unfold lamD walkDist
    refine le_iInf₂ fun p hp => ?_
    obtain ⟨W, hW, -⟩ := hp.exists_adjWalk (g₀ ∘ Prod.fst)
    rw [sum_cast_fst]
    exact_mod_cast ((C.annulus g₀ hg₀ hpos hP).lam_le W).trans hW

/-- `λ` of the level-one annulus, constant past `m`. -/
def lamC (q : ℕ) : ℕ := (C.annulus g₀ hg₀ hpos hP).lam (min q C.m)

end Annulus

namespace Live

section Basic

variable {C} {g : D → ℝ≥0∞} {Γ : Finset (D × Bool)} (L : C.Live g Γ)

/-- The distance in the live annulus from `κ0(t)` to `κ1(t)`. -/
def d (t : ℕ) : ℝ≥0∞ :=
  (R.double.split Γ).walkDist (g ∘ Prod.fst) ((R.double.split Γ).tail (L.κ0 t))
    ((R.double.split Γ).tail (L.κ1 t))

/-- A shortest walk of finite length in the live annulus from `κ0(i)` to `κ1(i)`. -/
def Shortest (i : ℕ) (p : List (D × Bool)) : Prop :=
  (R.double.split Γ).IsWalk ((R.double.split Γ).tail (L.κ0 i)) p
      ((R.double.split Γ).tail (L.κ1 i)) ∧
    (∀ p', (R.double.split Γ).IsWalk ((R.double.split Γ).tail (L.κ0 i)) p'
      ((R.double.split Γ).tail (L.κ1 i)) →
      (p.map (g ∘ Prod.fst)).sum ≤ (p'.map (g ∘ Prod.fst)).sum) ∧
    (p.map (g ∘ Prod.fst)).sum ≠ ⊤

/-- The vertex of the corner `z` lies on the walk `p` from `κ0(i)`. -/
def Visits (i : ℕ) (p : List (D × Bool)) (z : D × Bool) : Prop :=
  (R.double.split Γ).tail z = (R.double.split Γ).tail (L.κ0 i) ∨
    ∃ y ∈ p, (R.double.split Γ).head y = (R.double.split Γ).tail z

variable {L} in
theorem Shortest.sum_eq {i : ℕ} {p : List (D × Bool)} (h : L.Shortest i p) :
    (p.map (g ∘ Prod.fst)).sum = L.d i :=
  le_antisymm (by unfold d walkDist; exact le_iInf₂ fun p' hp' => h.2.1 p' hp') (walkDist_le _ h.1)

/-- The boundary of a live annulus is drawn on one face of its split. -/
theorem faceDrawn (hR : R.Planar) (hC : R.Connected) :
    (R.double.split Γ).FaceDrawn
      (cornerSeg L.κ0 L.xa L.xb ++ L.Lb ++ (cornerSeg L.κ1 L.ya L.yb).reverse ++ L.La) :=
  L.bound.faceDrawn (R.double.split_planar (R.double_planar hR hC) (R.double_connected hC)
    (C.Γ_nonempty.mono L.sub) L.skel).1

theorem mem_idx {i : ℕ} (h1 : L.xa ≤ i) (h2 : i ≤ L.xb) (p : List (D × Bool)) :
    i ∈ C.idx (L.κ0 i) p :=
  ⟨h2.trans L.xb_le, 0, Or.inl ((C.cut.tail_eq_iff _ _).2 (L.piece0 i h1 h2)).symm⟩

include L in
theorem cut_tail_eq {a b : D × Bool}
    (h : (R.double.split Γ).tail a = (R.double.split Γ).tail b) : C.cut.tail a = C.cut.tail b :=
  (C.cut.tail_eq_iff _ _).2
    (fconnect_of_split_subset L.sub (((R.double.split Γ).tail_eq_iff _ _).1 h))

/-- A copy at a vertex of the walk is an index of `idx`. -/
theorem mem_idx_of {i r : ℕ} {σ : Fin 2} {p : List (D × Bool)} {z : D × Bool} (hr : r ≤ C.m)
    (hz : fconnect C.cut.rot z (C.k σ r)) (hv : L.Visits i p z) : r ∈ C.idx (L.κ0 i) p := by
  have e := (C.cut.tail_eq_iff _ _).2 hz
  refine ⟨hr, σ, ?_⟩
  rcases hv with h | ⟨y, hy, h⟩
  · exact Or.inl (e.symm.trans (L.cut_tail_eq h))
  · exact Or.inr ⟨y, hy, (L.cut_tail_eq (a := R.double.rev y) h).trans e⟩

/-- The vertex of a dart of the walk is a vertex of the walk. -/
theorem visits_of_mem {i : ℕ} {p : List (D × Bool)}
    (hp : (R.double.split Γ).IsWalk ((R.double.split Γ).tail (L.κ0 i)) p
      ((R.double.split Γ).tail (L.κ1 i)))
    {y z : D × Bool} (hy : y ∈ p) (hz : (R.double.split Γ).tail z = (R.double.split Γ).tail y) :
    L.Visits i p z := by
  rcases hp.tail_mem y hy with h | ⟨y', hy', h⟩
  · exact Or.inl (hz.trans h)
  · exact Or.inr ⟨y', hy', h.trans hz.symm⟩

end Basic

section Annulus

variable {C} {g₀ : D → ℕ} (hg₀ : ∀ x, g₀ (R.rev x) = g₀ x) (hpos : ∀ t, t < C.m → 1 ≤ g₀ (C.e t))
  (hP : ∀ q, R.IsWalk (C.v 0) q (C.v C.m) → C.pos g₀ C.m ≤ (q.map g₀).sum)
  {Γ : Finset (D × Bool)} (L : C.Live (Nat.cast ∘ g₀) Γ)

/-- **Lemma S1 in a live annulus.** Let `p` be a shortest walk of a live annulus from `κ0(i)` to
`κ1(i)`, and `i1` and `i2` the least and the greatest index of a copy of the path at a vertex of `p`.
Every index `t` strictly between them has the largest `λ` on `[i1, t]` or on `[t, i2]`. -/
theorem dom (hR : R.Planar) (hC : R.Connected) {i : ℕ} (h1 : L.xa ≤ i) (h2 : i ≤ L.xb)
    (h3 : L.ya ≤ i) (h4 : i ≤ L.yb) {p : List (D × Bool)} (hp : L.Shortest i p) {i1 i2 : ℕ}
    (hi1 : IsLeast (C.idx (L.κ0 i) p) i1) (hi2 : IsGreatest (C.idx (L.κ0 i) p) i2) :
    ∀ t, i1 < t → t < i2 →
      (∀ q, i1 ≤ q → q ≤ t →
        (C.annulus g₀ hg₀ hpos hP).lam q ≤ (C.annulus g₀ hg₀ hpos hP).lam t) ∨
      (∀ q, t ≤ q → q ≤ i2 →
        (C.annulus g₀ hg₀ hpos hP).lam q ≤ (C.annulus g₀ hg₀ hpos hP).lam t) := by
  have hi : i ≤ C.m := h2.trans L.xb_le
  have e0 : C.cut.tail (L.κ0 i) = C.cut.tail (C.k 0 i) :=
    (C.cut.tail_eq_iff _ _).2 (L.piece0 i h1 h2)
  have e1 : C.cut.tail (L.κ1 i) = C.cut.tail (C.k 1 i) :=
    (C.cut.tail_eq_iff _ _).2 (L.piece1 i h3 h4)
  have hq : C.cut.IsWalk (C.cut.tail (C.k 0 i)) p (C.cut.tail (C.k 1 i)) := by
    rw [← e0, ← e1]
    exact isWalk_of_split_subset L.sub hp.1
  obtain ⟨W, hW, hs⟩ := hq.exists_adjWalk (g₀ ∘ Prod.fst)
  have hle : (p.map (g₀ ∘ Prod.fst)).sum ≤ (C.annulus g₀ hg₀ hpos hP).lam i := by
    have e := hp.sum_eq
    rw [sum_cast_fst, show L.d i = C.lamD (Nat.cast ∘ g₀) i from L.dist i h1 h3 h2 h4,
      C.lamD_eq g₀ hg₀ hpos hP hR hC hi] at e
    exact_mod_cast e.le
  have hWl : Recursion.wlen (C.cut.edgeWeight (g₀ ∘ Prod.fst)) W =
      (C.annulus g₀ hg₀ hpos hP).lam i :=
    le_antisymm (hW.trans hle) ((C.annulus g₀ hg₀ hpos hP).lam_le W)
  obtain ⟨j1, j2, hj1, hj2, -, -, hdom⟩ := C.witness_interval g₀ hR hC hg₀ hpos hP hi W hWl
  have hcop : (C.annulus g₀ hg₀ hpos hP).copies W = C.idx (L.κ0 i) p := by
    ext r
    show (r ≤ C.m ∧ ∃ σ, C.cut.tail (C.k σ r) ∈ W.support) ↔
      (r ≤ C.m ∧ ∃ σ, C.cut.tail (C.k σ r) = C.cut.tail (L.κ0 i) ∨
        ∃ y ∈ p, C.cut.head y = C.cut.tail (C.k σ r))
    simp only [hs, List.mem_map, e0]
  rw [hcop] at hj1 hj2
  obtain rfl := hi1.unique hj1
  obtain rfl := hi2.unique hj2
  exact hdom

/-- Lemma S1 in a live annulus for `λ` held constant past `m`. -/
theorem domC (hR : R.Planar) (hC : R.Connected) {i : ℕ} (h1 : L.xa ≤ i) (h2 : i ≤ L.xb)
    (h3 : L.ya ≤ i) (h4 : i ≤ L.yb) {p : List (D × Bool)} (hp : L.Shortest i p) {i1 i2 : ℕ}
    (hi1 : IsLeast (C.idx (L.κ0 i) p) i1) (hi2 : IsGreatest (C.idx (L.κ0 i) p) i2) :
    ∀ t, i1 < t → t < i2 →
      (∀ q, i1 ≤ q → q ≤ t → C.lamC g₀ hg₀ hpos hP q ≤ C.lamC g₀ hg₀ hpos hP t) ∨
      (∀ q, t ≤ q → q ≤ i2 → C.lamC g₀ hg₀ hpos hP q ≤ C.lamC g₀ hg₀ hpos hP t) := by
  intro t ht1 ht2
  have hm : i2 ≤ C.m := hi2.1.1
  unfold lamC
  rcases L.dom hg₀ hpos hP hR hC h1 h2 h3 h4 hp hi1 hi2 t ht1 ht2 with h | h
  · refine Or.inl fun q hq1 hq2 => ?_
    rw [min_eq_left (by omega : q ≤ C.m), min_eq_left (by omega : t ≤ C.m)]
    exact h q hq1 hq2
  · refine Or.inr fun q hq1 hq2 => ?_
    rw [min_eq_left (by omega : q ≤ C.m), min_eq_left (by omega : t ≤ C.m)]
    exact h q hq1 hq2

/-- A live annulus has a simple shortest walk from `κ0(i)` to `κ1(i)`. -/
theorem exists_shortest (hR : R.Planar) (hC : R.Connected) {i : ℕ} (h1 : L.xa ≤ i)
    (h2 : i ≤ L.xb) (h3 : L.ya ≤ i) (h4 : i ≤ L.yb) :
    ∃ p, L.Shortest i p ∧ (p.map (R.double.split Γ).tail).Nodup ∧
      ∀ z ∈ p, (R.double.split Γ).tail z ≠ (R.double.split Γ).tail (L.κ1 i) := by
  classical
  have hc0 : L.κ0 i ∈ liveBoundary L.κ0 L.κ1 L.xa L.xb L.ya L.yb L.La L.Lb := by
    unfold liveBoundary
    simp only [List.mem_append]
    exact Or.inl (Or.inl (Or.inl (mem_cornerSeg.2 ⟨i, h1, h2, rfl⟩)))
  have hc1 : L.κ1 i ∈ liveBoundary L.κ0 L.κ1 L.xa L.xb L.ya L.yb L.La L.Lb := by
    unfold liveBoundary
    simp only [List.mem_append, List.mem_reverse]
    exact Or.inl (Or.inr (mem_cornerSeg.2 ⟨i, h3, h4, rfl⟩))
  obtain ⟨p₀, hp₀⟩ := ((R.double.split Γ).gcomp_iff _ _).1
    ((L.bound.gcomp_iff (R.double_planar hR hC) (R.double_connected hC) ⟨_, L.bound.sub _ hc0⟩
      L.skel hc0 (L.bound.sub _ hc1)).2 hc1)
  have hex : ∃ n, ∃ p, (R.double.split Γ).IsWalk ((R.double.split Γ).tail (L.κ0 i)) p
      ((R.double.split Γ).tail (L.κ1 i)) ∧ (p.map (g₀ ∘ Prod.fst)).sum = n := ⟨_, p₀, hp₀, rfl⟩
  obtain ⟨p₁, hp₁, e₁⟩ := Nat.find_spec hex
  obtain ⟨q, hq, hnd, hne, hsub⟩ := hp₁.exists_simple
  have hle : ∀ p', (R.double.split Γ).IsWalk ((R.double.split Γ).tail (L.κ0 i)) p'
      ((R.double.split Γ).tail (L.κ1 i)) →
      (q.map (g₀ ∘ Prod.fst)).sum ≤ (p'.map (g₀ ∘ Prod.fst)).sum := fun p' hp' => by
    have a1 : (q.map (g₀ ∘ Prod.fst)).sum ≤ (p₁.map (g₀ ∘ Prod.fst)).sum :=
      (hsub.map (g₀ ∘ Prod.fst)).sum_le_sum fun _ _ => Nat.zero_le _
    have a2 := Nat.find_min' hex ⟨p', hp', rfl⟩
    omega
  refine ⟨q, ⟨hq, fun p' hp' => ?_, ?_⟩, hnd, hne⟩
  · rw [sum_cast_fst, sum_cast_fst]
    exact_mod_cast hle p' hp'
  · rw [sum_cast_fst]
    exact ENNReal.natCast_ne_top _

end Annulus

end Live

section Run

variable {C} {g : D → ℝ≥0∞}

mutual
/-- **A run of the recursion** on a live annulus with the index range `[j, k]`. A leaf has
`k ≤ j + 1`. Any other annulus has a shortest walk `p` from `κ0(i)` to `κ1(i)` for
`i = ⌊(j + k)/2⌋`, the least and the greatest index `i1` and `i2` of a copy of the path at a vertex
of `p`, a step of `p`, and its two sides with the ranges `[j, i1]` and `[i2, k]`. -/
inductive Run (hR : R.Planar) (hC : R.Connected) (hg : ∀ x, g (R.rev x) = g x) :
    (Γ : Finset (D × Bool)) → C.Live g Γ → ℕ → ℕ → Type u
  | leaf {Γ : Finset (D × Bool)} {L : C.Live g Γ} {j k : ℕ} (hjk : j ≤ k) (hk : k ≤ j + 1)
      (hxa : L.xa ≤ j) (hya : L.ya ≤ j) (hxb : k ≤ L.xb) (hyb : k ≤ L.yb) : Run hR hC hg Γ L j k
  | node {Γ : Finset (D × Bool)} {L : C.Live g Γ} {j k : ℕ} (hjk : j + 2 ≤ k)
      (hxa : L.xa ≤ j) (hya : L.ya ≤ j) (hxb : k ≤ L.xb) (hyb : k ≤ L.yb)
      (p : List (D × Bool)) (hp : L.Shortest ((j + k) / 2) p) (i1 i2 : ℕ)
      (h1 : IsLeast (C.idx (L.κ0 ((j + k) / 2)) p) i1)
      (h2 : IsGreatest (C.idx (L.κ0 ((j + k) / 2)) p) i2) (S : L.Step)
      (sub : ∃ p₁ p₃, p = p₁ ++ (List.range S.n).map S.q ++ p₃)
      (left : SideA hR hC hg Γ L p ((j + k) / 2) S j i1)
      (right : SideB hR hC hg Γ L p ((j + k) / 2) S i2 k) : Run hR hC hg Γ L j k
/-- The side of `κ0(x_a)` of a step of the walk `p` from `κ0(i)`, with the range `[lo, hi]`. -/
inductive SideA (hR : R.Planar) (hC : R.Connected) (hg : ∀ x, g (R.rev x) = g x) :
    (Γ : Finset (D × Bool)) → (L : C.Live g Γ) → List (D × Bool) → ℕ → L.Step → ℕ → ℕ → Type u
  /-- The walk passes through the vertex of a corner `c` of `κ0(x_a), L_a, κ1(y_a)`. -/
  | overlap {Γ : Finset (D × Bool)} {L : C.Live g Γ} {p : List (D × Bool)} {i : ℕ}
      {S : L.Step} {lo hi : ℕ} (c : D × Bool) (hc : c = L.κ0 L.xa ∨ c ∈ L.La ∨ c = L.κ1 L.ya)
      (P₁ P₂ : List (D × Bool)) (hs : p = P₁ ++ P₂)
      (h1 : (R.double.split Γ).IsWalk ((R.double.split Γ).tail (L.κ0 i)) P₁
        ((R.double.split Γ).tail c))
      (h2 : (R.double.split Γ).IsWalk ((R.double.split Γ).tail c) P₂
        ((R.double.split Γ).tail (L.κ1 i))) : SideA hR hC hg Γ L p i S lo hi
  /-- The side is called: the side of `κ1(y)` of the cut along the step, a live annulus. -/
  | child {Γ : Finset (D × Bool)} {L : C.Live g Γ} {p : List (D × Bool)} {i : ℕ}
      {S : L.Step} {lo hi : ℕ}
      (noA : ∀ j, 0 < j → j < S.n → ∀ c ∈ L.La, ¬ fconnect (R.double.split Γ).rot (S.q j) c)
      (hdeg : L.hiB S.x S.y ≠ [] ∨ 1 < S.n ∨ ((S.rq 0).1, false) ∉ Γ)
      (r : Run hR hC hg (L.loCut hR hC S noA hdeg).Γ' (L.lo hR hC S noA hdeg hg) lo hi) :
      SideA hR hC hg Γ L p i S lo hi
  /-- The range is empty and the side is not called. -/
  | empty {Γ : Finset (D × Bool)} {L : C.Live g Γ} {p : List (D × Bool)} {i : ℕ}
      {S : L.Step} {lo hi : ℕ} (h : hi < lo) : SideA hR hC hg Γ L p i S lo hi
/-- The side of `κ0(x_b)` of a step of the walk `p` from `κ0(i)`, with the range `[lo, hi]`. -/
inductive SideB (hR : R.Planar) (hC : R.Connected) (hg : ∀ x, g (R.rev x) = g x) :
    (Γ : Finset (D × Bool)) → (L : C.Live g Γ) → List (D × Bool) → ℕ → L.Step → ℕ → ℕ → Type u
  /-- The walk passes through the vertex of a corner `c` of `κ0(x_b), L_b, κ1(y_b)`. -/
  | overlap {Γ : Finset (D × Bool)} {L : C.Live g Γ} {p : List (D × Bool)} {i : ℕ}
      {S : L.Step} {lo hi : ℕ} (c : D × Bool) (hc : c = L.κ0 L.xb ∨ c ∈ L.Lb ∨ c = L.κ1 L.yb)
      (P₁ P₂ : List (D × Bool)) (hs : p = P₁ ++ P₂)
      (h1 : (R.double.split Γ).IsWalk ((R.double.split Γ).tail (L.κ0 i)) P₁
        ((R.double.split Γ).tail c))
      (h2 : (R.double.split Γ).IsWalk ((R.double.split Γ).tail c) P₂
        ((R.double.split Γ).tail (L.κ1 i))) : SideB hR hC hg Γ L p i S lo hi
  /-- The side is called: the side of `κ0(x)` of the cut along the step, a live annulus. -/
  | child {Γ : Finset (D × Bool)} {L : C.Live g Γ} {p : List (D × Bool)} {i : ℕ}
      {S : L.Step} {lo hi : ℕ}
      (noB : ∀ j, 0 < j → j < S.n → ∀ c ∈ L.Lb, ¬ fconnect (R.double.split Γ).rot (S.q j) c)
      (hdeg : L.hiA S.x S.y ≠ [] ∨ 1 < S.n ∨ ((S.q 0).1, false) ∉ Γ)
      (r : Run hR hC hg (L.hiCut hR hC S noB hdeg).Γ' (L.hi hR hC S noB hdeg hg) lo hi) :
      SideB hR hC hg Γ L p i S lo hi
  /-- The range is empty and the side is not called. -/
  | empty {Γ : Finset (D × Bool)} {L : C.Live g Γ} {p : List (D × Bool)} {i : ℕ}
      {S : L.Step} {lo hi : ℕ} (h : hi < lo) : SideB hR hC hg Γ L p i S lo hi
end

section Vals

variable {hR : R.Planar} {hC : R.Connected} {hg : ∀ x, g (R.rev x) = g x}

mutual
/-- The computed pairs of an index and a length. A leaf computes the lengths at `j` and `k`, any
other annulus those at `i`, `max i1 j` and `min i2 k`, all in its annulus. -/
def Run.vals : {Γ : Finset (D × Bool)} → {L : C.Live g Γ} → {j k : ℕ} →
    Run hR hC hg Γ L j k → Set (ℕ × ℝ≥0∞)
  | _, L, j, k, .leaf .. => {(j, L.d j), (k, L.d k)}
  | _, L, j, k, .node _ _ _ _ _ _ _ i1 i2 _ _ _ _ left right =>
    {((j + k) / 2, L.d ((j + k) / 2)), (max i1 j, L.d (max i1 j)), (min i2 k, L.d (min i2 k))} ∪
      left.vals ∪ right.vals
/-- The computed pairs of the side of `κ0(x_a)`. The overlap rule computes the length through the
corner of the overlap for each index of `[lo, i]`. -/
def SideA.vals : {Γ : Finset (D × Bool)} → {L : C.Live g Γ} → {p : List (D × Bool)} → {i : ℕ} →
    {S : L.Step} → {lo hi : ℕ} → SideA hR hC hg Γ L p i S lo hi → Set (ℕ × ℝ≥0∞)
  | Γ, L, _, i, _, lo, _, .overlap c _ _ _ _ _ _ =>
    {v | ∃ μ, lo ≤ μ ∧ μ ≤ i ∧ v = (μ,
      (R.double.split Γ).walkDist (g ∘ Prod.fst) ((R.double.split Γ).tail (L.κ0 μ))
        ((R.double.split Γ).tail c) +
      (R.double.split Γ).walkDist (g ∘ Prod.fst) ((R.double.split Γ).tail c)
        ((R.double.split Γ).tail (L.κ1 μ)))}
  | _, _, _, _, _, _, _, .child _ _ r => r.vals
  | _, _, _, _, _, _, _, .empty _ => ∅
/-- The computed pairs of the side of `κ0(x_b)`. The overlap rule computes the length through the
corner of the overlap for each index of `[i, hi]`. -/
def SideB.vals : {Γ : Finset (D × Bool)} → {L : C.Live g Γ} → {p : List (D × Bool)} → {i : ℕ} →
    {S : L.Step} → {lo hi : ℕ} → SideB hR hC hg Γ L p i S lo hi → Set (ℕ × ℝ≥0∞)
  | Γ, L, _, i, _, _, hi, .overlap c _ _ _ _ _ _ =>
    {v | ∃ μ, i ≤ μ ∧ μ ≤ hi ∧ v = (μ,
      (R.double.split Γ).walkDist (g ∘ Prod.fst) ((R.double.split Γ).tail (L.κ0 μ))
        ((R.double.split Γ).tail c) +
      (R.double.split Γ).walkDist (g ∘ Prod.fst) ((R.double.split Γ).tail c)
        ((R.double.split Γ).tail (L.κ1 μ)))}
  | _, _, _, _, _, _, _, .child _ _ r => r.vals
  | _, _, _, _, _, _, _, .empty _ => ∅
end

mutual
/-- **(INV) and (C23) for a run.** Every computed length is `λ_t` of its index `t`. -/
theorem Run.vals_eq : ∀ {Γ : Finset (D × Bool)} {L : C.Live g Γ} {j k : ℕ}
    (r : Run hR hC hg Γ L j k), ∀ v ∈ r.vals, v.2 = C.lamD g v.1
  | _, L, j, k, .leaf _ _ hxa hya hxb hyb => by
    intro v hv
    simp only [Run.vals, Set.mem_insert_iff, Set.mem_singleton_iff] at hv
    rcases hv with rfl | rfl
    · exact L.dist j hxa hya (by omega) (by omega)
    · exact L.dist k (by omega) (by omega) hxb hyb
  | _, L, j, k, .node hjk hxa hya hxb hyb p hp i1 i2 h1 h2 _ _ left right => by
    have hm := L.mem_idx (i := (j + k) / 2) (by omega) (by omega) p
    have hi1 := h1.2 hm
    have hi2 := h2.2 hm
    intro v hv
    simp only [Run.vals, Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff] at hv
    rcases hv with ((rfl | rfl | rfl) | hv) | hv
    · exact L.dist ((j + k) / 2) (by omega) (by omega) (by omega) (by omega)
    · exact L.dist (max i1 j) (by omega) (by omega) (by omega) (by omega)
    · exact L.dist (min i2 k) (by omega) (by omega) (by omega) (by omega)
    · exact SideA.vals_eq left hxa hya (by omega) (by omega) hp v hv
    · exact SideB.vals_eq right (by omega) (by omega) hxb hyb hp v hv
/-- (C23) on the side of `κ0(x_a)`. -/
theorem SideA.vals_eq : ∀ {Γ : Finset (D × Bool)} {L : C.Live g Γ} {p : List (D × Bool)} {i : ℕ}
    {S : L.Step} {lo hi : ℕ} (s : SideA hR hC hg Γ L p i S lo hi), L.xa ≤ lo → L.ya ≤ lo →
    i ≤ L.xb → i ≤ L.yb → L.Shortest i p → ∀ v ∈ s.vals, v.2 = C.lamD g v.1
  | _, L, _, i, _, lo, _, .overlap c hc P₁ P₂ hs e1 e2, hxa, hya, hxb, hyb, hp => by
    subst hs
    intro v hv
    simp only [SideA.vals, Set.mem_ofPred_eq] at hv
    obtain ⟨μ, hμ1, hμ2, rfl⟩ := hv
    show _ + _ = C.lamD g μ
    rw [(L.faceDrawn hR hC).overlap_a (g ∘ Prod.fst) (fun z => hg z.1) (by omega) (by omega) hμ2
      hxb hyb hc e1 e2 hp.2.2 hp.2.1]
    exact L.dist μ (by omega) (by omega) (by omega) (by omega)
  | _, _, _, _, _, _, _, .child _ _ r, _, _, _, _, _ => by
    intro v hv
    simp only [SideA.vals] at hv
    exact Run.vals_eq r v hv
  | _, _, _, _, _, _, _, .empty _, _, _, _, _, _ => by
    intro v hv
    simp [SideA.vals] at hv
/-- (C23) on the side of `κ0(x_b)`. -/
theorem SideB.vals_eq : ∀ {Γ : Finset (D × Bool)} {L : C.Live g Γ} {p : List (D × Bool)} {i : ℕ}
    {S : L.Step} {lo hi : ℕ} (s : SideB hR hC hg Γ L p i S lo hi), L.xa ≤ i → L.ya ≤ i →
    hi ≤ L.xb → hi ≤ L.yb → L.Shortest i p → ∀ v ∈ s.vals, v.2 = C.lamD g v.1
  | _, L, _, i, _, _, hi, .overlap c hc P₁ P₂ hs e1 e2, hxa, hya, hxb, hyb, hp => by
    subst hs
    intro v hv
    simp only [SideB.vals, Set.mem_ofPred_eq] at hv
    obtain ⟨μ, hμ1, hμ2, rfl⟩ := hv
    show _ + _ = C.lamD g μ
    rw [(L.faceDrawn hR hC).overlap_b (g ∘ Prod.fst) (fun z => hg z.1) hxa hya hμ1 (by omega)
      (by omega) hc e1 e2 hp.2.2 hp.2.1]
    exact L.dist μ (by omega) (by omega) (by omega) (by omega)
  | _, _, _, _, _, _, _, .child _ _ r, _, _, _, _, _ => by
    intro v hv
    simp only [SideB.vals] at hv
    exact Run.vals_eq r v hv
  | _, _, _, _, _, _, _, .empty _, _, _, _, _, _ => by
    intro v hv
    simp [SideB.vals] at hv
end

end Vals

section Rec

variable (g₀ : D → ℕ) (hg₀ : ∀ x, g₀ (R.rev x) = g₀ x) (hpos : ∀ t, t < C.m → 1 ≤ g₀ (C.e t))
  (hP : ∀ q, R.IsWalk (C.v 0) q (C.v C.m) → C.pos g₀ C.m ≤ (q.map g₀).sum)
  {hR : R.Planar} {hC : R.Connected}
  {hgc : ∀ x, (Nat.cast ∘ g₀ : D → ℝ≥0∞) (R.rev x) = (Nat.cast ∘ g₀ : D → ℝ≥0∞) x}

mutual
/-- The tree of the index model of a run. Lemma S1 for the image of each computed walk in the cut
gives the field `dom` of its node. -/
def Run.toRec : {Γ : Finset (D × Bool)} → {L : C.Live (Nat.cast ∘ g₀) Γ} → {j k : ℕ} →
    Run hR hC hgc Γ L j k → Recursion.Rec (C.lamC g₀ hg₀ hpos hP) j k
  | _, _, _, _, .leaf hjk hk _ _ _ _ => .leaf hjk hk
  | _, L, j, k, .node hjk hxa hya hxb hyb p hp i1 i2 h1 h2 _ _ left right =>
    .node ((j + k) / 2) i1 i2 (by omega) (by omega)
      (h1.2 (L.mem_idx (by omega) (by omega) p)) (h2.2 (L.mem_idx (by omega) (by omega) p))
      (L.domC hg₀ hpos hP hR hC (by omega) (by omega) (by omega) (by omega) hp h1 h2)
      left.toRec right.toRec
/-- The tree of the side of `κ0(x_a)`. -/
def SideA.toRec : {Γ : Finset (D × Bool)} → {L : C.Live (Nat.cast ∘ g₀) Γ} →
    {p : List (D × Bool)} → {i : ℕ} → {S : L.Step} → {lo hi : ℕ} →
    SideA hR hC hgc Γ L p i S lo hi → Recursion.Side (C.lamC g₀ hg₀ hpos hP) lo hi
  | _, _, _, _, _, _, _, .overlap .. => .overlap
  | _, _, _, _, _, _, _, .child _ _ r => .child r.toRec
  | _, _, _, _, _, _, _, .empty h => .empty h
/-- The tree of the side of `κ0(x_b)`. -/
def SideB.toRec : {Γ : Finset (D × Bool)} → {L : C.Live (Nat.cast ∘ g₀) Γ} →
    {p : List (D × Bool)} → {i : ℕ} → {S : L.Step} → {lo hi : ℕ} →
    SideB hR hC hgc Γ L p i S lo hi → Recursion.Side (C.lamC g₀ hg₀ hpos hP) lo hi
  | _, _, _, _, _, _, _, .overlap .. => .overlap
  | _, _, _, _, _, _, _, .child _ _ r => .child r.toRec
  | _, _, _, _, _, _, _, .empty h => .empty h
end

mutual
/-- A run and its tree compute the same indices. -/
theorem Run.computed_eq : ∀ {Γ : Finset (D × Bool)} {L : C.Live (Nat.cast ∘ g₀) Γ} {j k : ℕ}
    (r : Run hR hC hgc Γ L j k),
    ((r.toRec g₀ hg₀ hpos hP).computed : Set ℕ) = Prod.fst '' r.vals
  | _, _, _, _, .leaf .. => by
    simp only [Run.toRec, Recursion.Rec.computed, Run.vals, Finset.coe_insert,
      Finset.coe_singleton, Set.image_insert_eq, Set.image_singleton]
  | _, _, _, _, .node _ _ _ _ _ _ _ _ _ _ _ _ _ left right => by
    simp only [Run.toRec, Recursion.Rec.computed, Run.vals, Finset.coe_union, Finset.coe_insert,
      Finset.coe_singleton, Set.image_union, Set.image_insert_eq, Set.image_singleton,
      SideA.computed_eq left, SideB.computed_eq right]
/-- The side of `κ0(x_a)` and its tree compute the same indices. -/
theorem SideA.computed_eq : ∀ {Γ : Finset (D × Bool)} {L : C.Live (Nat.cast ∘ g₀) Γ}
    {p : List (D × Bool)} {i : ℕ} {S : L.Step} {lo hi : ℕ} (s : SideA hR hC hgc Γ L p i S lo hi),
    ((s.toRec g₀ hg₀ hpos hP).computed (Finset.Icc lo i) : Set ℕ) = Prod.fst '' s.vals
  | _, _, _, _, _, _, _, .overlap .. => by
    ext μ
    simp only [SideA.toRec, Recursion.Side.computed, SideA.vals, Finset.coe_Icc, Set.mem_Icc,
      Set.mem_image, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨_, ⟨μ, h1, h2, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨μ', h1, h2, rfl⟩, rfl⟩
      exact ⟨h1, h2⟩
  | _, _, _, _, _, _, _, .child _ _ r => by
    simp only [SideA.toRec, Recursion.Side.computed, SideA.vals]
    exact Run.computed_eq r
  | _, _, _, _, _, _, _, .empty _ => by
    simp [SideA.toRec, Recursion.Side.computed, SideA.vals]
/-- The side of `κ0(x_b)` and its tree compute the same indices. -/
theorem SideB.computed_eq : ∀ {Γ : Finset (D × Bool)} {L : C.Live (Nat.cast ∘ g₀) Γ}
    {p : List (D × Bool)} {i : ℕ} {S : L.Step} {lo hi : ℕ} (s : SideB hR hC hgc Γ L p i S lo hi),
    ((s.toRec g₀ hg₀ hpos hP).computed (Finset.Icc i hi) : Set ℕ) = Prod.fst '' s.vals
  | _, _, _, _, _, _, _, .overlap .. => by
    ext μ
    simp only [SideB.toRec, Recursion.Side.computed, SideB.vals, Finset.coe_Icc, Set.mem_Icc,
      Set.mem_image, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨_, ⟨μ, h1, h2, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨μ', h1, h2, rfl⟩, rfl⟩
      exact ⟨h1, h2⟩
  | _, _, _, _, _, _, _, .child _ _ r => by
    simp only [SideB.toRec, Recursion.Side.computed, SideB.vals]
    exact Run.computed_eq r
  | _, _, _, _, _, _, _, .empty _ => by
    simp [SideB.toRec, Recursion.Side.computed, SideB.vals]
end

include hg₀ hpos hP in
/-- **Lemma S2 for a run on the cut.** Some index `t` has the least `λ_t`, and it is the least
computed length. -/
theorem Run.isLeast (r : Run hR hC hgc C.Γ (C.liveOne (Nat.cast ∘ g₀)) 0 C.m) :
    ∃ t ≤ C.m, (∀ q ≤ C.m, C.lamD (Nat.cast ∘ g₀) t ≤ C.lamD (Nat.cast ∘ g₀) q) ∧
      IsLeast (Prod.snd '' r.vals) (C.lamD (Nat.cast ∘ g₀) t) := by
  obtain ⟨t, ht, hmin⟩ := (Finset.range (C.m + 1)).exists_min_image
    (C.annulus g₀ hg₀ hpos hP).lam ⟨0, by simp⟩
  have htm : t ≤ C.m := by
    rw [Finset.mem_range] at ht
    omega
  have hΛ : ∀ q, (C.annulus g₀ hg₀ hpos hP).lam t ≤ C.lamC g₀ hg₀ hpos hP q := fun q =>
    hmin _ (Finset.mem_range.2 (by omega))
  have hlt : C.lamC g₀ hg₀ hpos hP t = (C.annulus g₀ hg₀ hpos hP).lam t := by
    unfold lamC
    rw [min_eq_left htm]
  have hrec := (r.toRec g₀ hg₀ hpos hP).isLeast hΛ (Nat.zero_le t) htm hlt
  rw [r.computed_eq g₀ hg₀ hpos hP] at hrec
  have hle : ∀ v ∈ r.vals, v.1 ≤ C.m := fun v hv => by
    have h' : v.1 ∈ ((r.toRec g₀ hg₀ hpos hP).computed : Set ℕ) := by
      rw [r.computed_eq g₀ hg₀ hpos hP]
      exact ⟨v, hv, rfl⟩
    exact (Finset.mem_Icc.1 ((r.toRec g₀ hg₀ hpos hP).computed_subset h')).2
  have hval : ∀ v ∈ r.vals, v.2 = (C.lamC g₀ hg₀ hpos hP v.1 : ℝ≥0∞) := fun v hv => by
    rw [r.vals_eq v hv, C.lamD_eq g₀ hg₀ hpos hP hR hC (hle v hv)]
    unfold lamC
    rw [min_eq_left (hle v hv)]
  have himg : Prod.snd '' r.vals =
      (Nat.cast : ℕ → ℝ≥0∞) '' (C.lamC g₀ hg₀ hpos hP '' (Prod.fst '' r.vals)) := by
    rw [Set.image_image, Set.image_image]
    exact Set.image_congr hval
  refine ⟨t, htm, fun q hq => ?_, ?_⟩
  · rw [C.lamD_eq g₀ hg₀ hpos hP hR hC htm, C.lamD_eq g₀ hg₀ hpos hP hR hC hq]
    exact_mod_cast hmin q (Finset.mem_range.2 (by omega))
  · rw [himg, C.lamD_eq g₀ hg₀ hpos hP hR hC htm]
    exact Nat.mono_cast.map_isLeast hrec

end Rec

section Exists

variable {g₀ : D → ℕ} (hR : R.Planar) (hC : R.Connected)
  (hgc : ∀ x, (Nat.cast ∘ g₀ : D → ℝ≥0∞) (R.rev x) = (Nat.cast ∘ g₀ : D → ℝ≥0∞) x)

/-- **A run exists** on a live annulus for every range of indices of both of its copies of the
path. -/
theorem exists_run (n : ℕ) : ∀ {Γ : Finset (D × Bool)} (L : C.Live (Nat.cast ∘ g₀) Γ) {j k : ℕ},
    k - j < n → j ≤ k → L.xa ≤ j → L.ya ≤ j → k ≤ L.xb → k ≤ L.yb →
    Nonempty (Run hR hC hgc Γ L j k) := by
  induction n with
  | zero => intro Γ L j k h; omega
  | succ n ih =>
    intro Γ L j k hn hjk hxa hya hxb hyb
    by_cases hk : k ≤ j + 1
    · exact ⟨.leaf hjk hk hxa hya hxb hyb⟩
    have h1 : L.xa ≤ (j + k) / 2 := by omega
    have h2 : (j + k) / 2 ≤ L.xb := by omega
    have h3 : L.ya ≤ (j + k) / 2 := by omega
    have h4 : (j + k) / 2 ≤ L.yb := by omega
    obtain ⟨q, hq, hnd, hne⟩ := L.exists_shortest hR hC h1 h2 h3 h4
    obtain ⟨S, p₁, p₃, hsub⟩ := L.exists_step hR hC h1 h2 h3 h4 hq.1 hnd hne hq.2.1 hq.2.2
    have hmem : ∀ j', j' < S.n → S.q j' ∈ q := fun j' hj' => by
      rw [hsub]
      exact List.mem_append_left _
        (List.mem_append_right _ (List.mem_map.2 ⟨j', List.mem_range.2 hj', rfl⟩))
    have vx : L.Visits ((j + k) / 2) q (L.κ0 S.x) :=
      L.visits_of_mem hq.1 (hmem 0 S.pos) (((R.double.split Γ).tail_eq_iff _ _).2 S.start).symm
    have vy : L.Visits ((j + k) / 2) q (L.κ1 S.y) :=
      Or.inr ⟨S.q (S.n - 1), hmem _ (by have := S.pos; omega),
        ((R.double.split Γ).tail_eq_iff _ _).2 S.stop⟩
    have hm := L.mem_idx h1 h2 q
    have hbdd : BddAbove (C.idx (L.κ0 ((j + k) / 2)) q) := ⟨C.m, fun r hr => hr.1⟩
    have hI1 : IsLeast (C.idx (L.κ0 ((j + k) / 2)) q) (sInf (C.idx (L.κ0 ((j + k) / 2)) q)) :=
      ⟨Nat.sInf_mem ⟨_, hm⟩, fun r hr => Nat.sInf_le hr⟩
    have hI2 : IsGreatest (C.idx (L.κ0 ((j + k) / 2)) q) (sSup (C.idx (L.κ0 ((j + k) / 2)) q)) :=
      ⟨Nat.sSup_mem ⟨_, hm⟩ hbdd, fun r hr => le_csSup hbdd hr⟩
    have mx := L.mem_idx_of (S.hxb.trans L.xb_le) (L.piece0 S.x S.hxa S.hxb) vx
    have my := L.mem_idx_of (S.hyb.trans L.yb_le) (L.piece1 S.y S.hya S.hyb) vy
    have ex1 := hI1.2 mx
    have ey1 := hI1.2 my
    have ex2 := hI2.2 mx
    have ey2 := hI2.2 my
    have em1 := hI1.2 hm
    have em2 := hI2.2 hm
    have left : Nonempty (SideA hR hC hgc Γ L q ((j + k) / 2) S j
        (sInf (C.idx (L.κ0 ((j + k) / 2)) q))) := by
      by_cases hA : ∃ c, (c = L.κ0 L.xa ∨ c ∈ L.La ∨ c = L.κ1 L.ya) ∧
          L.Visits ((j + k) / 2) q c
      · obtain ⟨c, hc, hv⟩ := hA
        obtain ⟨P₁, P₂, s, hs, e1, e2, rfl, -⟩ := hq.1.split_first
          (fun w => w = (R.double.split Γ).tail c) (hv.imp Eq.symm id)
        exact ⟨.overlap c hc P₁ P₂ hs e1 e2⟩
      · by_cases hj : j ≤ sInf (C.idx (L.κ0 ((j + k) / 2)) q)
        · have noA : ∀ j', 0 < j' → j' < S.n → ∀ c ∈ L.La,
              ¬ fconnect (R.double.split Γ).rot (S.q j') c := fun j' _ hj' c hc hf =>
            hA ⟨c, Or.inr (Or.inl hc), L.visits_of_mem hq.1 (hmem j' hj')
              (((R.double.split Γ).tail_eq_iff _ _).2 hf).symm⟩
          have hx : S.x ≠ L.xa := fun e => hA ⟨L.κ0 L.xa, Or.inl rfl, e ▸ vx⟩
          have hdeg : L.hiB S.x S.y ≠ [] ∨ 1 < S.n ∨ ((S.rq 0).1, false) ∉ Γ :=
            Or.inl (List.ne_nil_of_mem (a := L.κ0 L.xa) (by
              simp only [Live.hiB, List.mem_append, List.mem_map, List.mem_range'_1]
              exact Or.inr ⟨L.xa, ⟨le_rfl, by have := S.hxa; omega⟩, rfl⟩))
          obtain ⟨r⟩ := ih (L.lo hR hC S noA hdeg hgc) (j := j)
            (k := sInf (C.idx (L.κ0 ((j + k) / 2)) q)) (by omega) hj hxa hya ex1 ey1
          exact ⟨.child noA hdeg r⟩
        · exact ⟨.empty (by omega)⟩
    have right : Nonempty (SideB hR hC hgc Γ L q ((j + k) / 2) S
        (sSup (C.idx (L.κ0 ((j + k) / 2)) q)) k) := by
      by_cases hB : ∃ c, (c = L.κ0 L.xb ∨ c ∈ L.Lb ∨ c = L.κ1 L.yb) ∧
          L.Visits ((j + k) / 2) q c
      · obtain ⟨c, hc, hv⟩ := hB
        obtain ⟨P₁, P₂, s, hs, e1, e2, rfl, -⟩ := hq.1.split_first
          (fun w => w = (R.double.split Γ).tail c) (hv.imp Eq.symm id)
        exact ⟨.overlap c hc P₁ P₂ hs e1 e2⟩
      · by_cases hj : sSup (C.idx (L.κ0 ((j + k) / 2)) q) ≤ k
        · have noB : ∀ j', 0 < j' → j' < S.n → ∀ c ∈ L.Lb,
              ¬ fconnect (R.double.split Γ).rot (S.q j') c := fun j' _ hj' c hc hf =>
            hB ⟨c, Or.inr (Or.inl hc), L.visits_of_mem hq.1 (hmem j' hj')
              (((R.double.split Γ).tail_eq_iff _ _).2 hf).symm⟩
          have hx : S.x ≠ L.xb := fun e => hB ⟨L.κ0 L.xb, Or.inl rfl, e ▸ vx⟩
          have hdeg : L.hiA S.x S.y ≠ [] ∨ 1 < S.n ∨ ((S.q 0).1, false) ∉ Γ :=
            Or.inl (List.ne_nil_of_mem (a := L.κ0 L.xb) (by
              simp only [Live.hiA, List.mem_append]
              exact Or.inl (Or.inl (mem_cornerSeg.2
                ⟨L.xb, by have := S.hxb; omega, le_rfl, rfl⟩))))
          obtain ⟨r⟩ := ih (L.hi hR hC S noB hdeg hgc)
            (j := sSup (C.idx (L.κ0 ((j + k) / 2)) q)) (k := k) (by omega) hj ex2 ey2 hxb hyb
          exact ⟨.child noB hdeg r⟩
        · exact ⟨.empty (by omega)⟩
    obtain ⟨l⟩ := left
    obtain ⟨rr⟩ := right
    exact ⟨.node (by omega) hxa hya hxb hyb q hq _ _ hI1 hI2 S ⟨p₁, p₃, hsub⟩ l rr⟩

/-- A run on the cut exists. -/
theorem nonempty_run : Nonempty (Run hR hC hgc C.Γ (C.liveOne (Nat.cast ∘ g₀)) 0 C.m) :=
  exists_run hR hC hgc (C.m + 1) (C.liveOne _) (j := 0) (k := C.m) (by omega) (Nat.zero_le _)
    le_rfl le_rfl le_rfl le_rfl

variable (hg₀ : ∀ x, g₀ (R.rev x) = g₀ x) (hpos : ∀ t, t < C.m → 1 ≤ g₀ (C.e t))
  (hP : ∀ q, R.IsWalk (C.v 0) q (C.v C.m) → C.pos g₀ C.m ≤ (q.map g₀).sum)

include hg₀ hpos hP in
/-- **The recursion on the cut.** Let the map be planar and connected, the weights symmetric and
positive on the path, and the path shortest. A run of the recursion on the cut exists. Every run
computes only lengths `λ_t` of its indices `t`, some index `t` has the least `λ_t`, and that is the
least computed length. -/
theorem recursion_cut :
    Nonempty (Run hR hC hgc C.Γ (C.liveOne (Nat.cast ∘ g₀)) 0 C.m) ∧
      ∀ r : Run hR hC hgc C.Γ (C.liveOne (Nat.cast ∘ g₀)) 0 C.m,
        (∀ v ∈ r.vals, v.2 = C.lamD (Nat.cast ∘ g₀) v.1) ∧
        ∃ t ≤ C.m, (∀ q ≤ C.m, C.lamD (Nat.cast ∘ g₀) t ≤ C.lamD (Nat.cast ∘ g₀) q) ∧
          IsLeast (Prod.snd '' r.vals) (C.lamD (Nat.cast ∘ g₀) t) :=
  ⟨nonempty_run hR hC hgc, fun r => ⟨r.vals_eq, r.isLeast g₀ hg₀ hpos hP⟩⟩

end Exists

end Run

end CutPath

end RotSystem

end

end SsspFlow
