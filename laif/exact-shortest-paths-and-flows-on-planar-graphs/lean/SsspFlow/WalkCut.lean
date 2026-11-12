import SsspFlow.EdgeCut

/-!
# Cutting along a walk

A `WalkCut Γ` is a walk `q 0, …, q (n - 1)` of darts of `R.double` in the split
`R.double.split Γ`, from the vertex of a corner `ka` to the vertex of another corner `kb` of one
boundary `ka, a_1, …, a_p, kb, b_1, …, b_q`. Its vertices are distinct, its edges are distinct edges
of `R`, an edge has both digon corners in `Γ` or none, the first edge is used through its copy
`(d, true)` if its digon corners are in `Γ`, and the vertices after the first carry no corner of
`ka, a_1, …, a_p`. They may carry corners of `b_1, …, b_q`, and the walk may run along edges whose
digon corners are in `Γ`.

Cutting the walk adds the digon corners of all its edges to `Γ` (`WalkCut.Γ'`). Let `r_j` be the
digon corner of the `j`-th edge at its head. Then the side of `ka` has the boundary
`ka, a_1, …, a_p, r_n, …, r_1` (`WalkCut.boundary_hi`), as for a chord of a disk, and the corners on
it are the corners in the component of `ka` (`WalkCut.gcomp_hi_iff`). The copies `(d, true)` of the
edges form a walk on this side (`WalkCut.isWalk_hi`). Every vertex of the walk has exactly one part
on this side, the vertex of `ka` or of `r_j` (`WalkCut.part_hi`, `WalkCut.part_hi_last`), and the
other vertices do not change (`WalkCut.fconnect_cut_iff`).

If moreover the vertices after the first carry no corner of `kb, b_1, …, b_q`, and the last edge is
used through its copy `(d, false)` if its digon corners are in `Γ`, the walk read backwards is a
`WalkCut` from `kb` to `ka` (`WalkCut.reverse`) that cuts the same edges (`WalkCut.reverse_Γ'`).
Let `m_j` be the digon corner of the `j`-th edge at its tail. Then the side of `kb` has the boundary
`kb, b_1, …, b_q, m_1, …, m_n` (`WalkCut.boundary_lo`, `WalkCut.gcomp_lo_iff`), the copies
`(d, false)` of the edges form a walk on it (`WalkCut.isWalk_lo`), every vertex of the walk has
exactly one part on it (`WalkCut.part_lo`, `WalkCut.part_lo_last`), and the two sides are different
components (`WalkCut.not_gcomp`).

The proof cuts one edge at a time (`EdgeCut`, `WalkCut.state`). An edge into a vertex without
corners is a slit, an edge into a vertex with a corner is a chord, and an edge whose digon corners
are in `Γ` moves the boundary along. In the chord case the rest of the walk joins the next vertex to
`kb`, so the walk goes on from the part of the next vertex on the side of `kb`.
-/

set_option autoImplicit false

namespace SsspFlow

open FourColor

namespace RotSystem

variable {D : Type*} [Fintype D] [DecidableEq D] {R : RotSystem D}

/-- The two darts over a dart whose digon corner is not a corner lie at one vertex of the split. -/
theorem fconnect_digon {Γ : Finset (D × Bool)} {d : D} (h : (d, false) ∉ Γ) (b : Bool) :
    fconnect (R.double.split Γ).rot (d, false) (d, b) := by
  cases b with
  | false => exact connect_refl _
  | true =>
    have := fconnect1 (R.double.split Γ).rot (d, false)
    rwa [R.double.split_rot_of_not_mem h] at this

/-- The split at a larger set refines the split. -/
theorem fconnect_of_split_subset {Γ Γ₀ : Finset (D × Bool)} (h : Γ ⊆ Γ₀) {x y : D × Bool}
    (hxy : fconnect (R.double.split Γ₀).rot x y) : fconnect (R.double.split Γ).rot x y := by
  rw [← R.double.split_split h] at hxy
  exact (R.double.split Γ).fconnect_of_fconnect_split hxy

/-- The first return of the rotation to `Γ` is the corner of the vertex of the split after the
dart. -/
theorem nodeReturn_eq_of_fconnect (M : RotSystem D) {Γ : Finset D} {x c : D} (hx : x ∈ Γ)
    (hc : c ∈ Γ) (h : fconnect (M.split Γ).rot (M.rot x) c) : M.nodeReturn Γ x = c := by
  obtain ⟨c', hc'⟩ := exists_trail hc h
  obtain rfl := M.eq_of_fconnect_split hc'.mem hc (connect_trans (fconnect_symm hc'.to_fconnect) h)
  exact firstReturn_eq_of_trail _ hx (hc'.congr fun w hw => (M.split_rot_of_not_mem hw).symm)

variable (R) in
/-- A walk of the split from the vertex of `ka` to the vertex of `kb`, for a boundary
`ka, a_1, …, a_p, kb, b_1, …, b_q`. -/
structure WalkCut (Γ : Finset (D × Bool)) where
  /-- The number of edges. -/
  n : ℕ
  /-- The darts. -/
  q : ℕ → D × Bool
  /-- The corner at the first vertex. -/
  ka : D × Bool
  /-- The corner at the last vertex. -/
  kb : D × Bool
  /-- The corners of the boundary after `ka`. -/
  A : List (D × Bool)
  /-- The corners of the boundary after `kb`. -/
  B : List (D × Bool)
  pos : 0 < n
  bound : R.double.Boundary Γ ((ka :: A) ++ (kb :: B))
  start : fconnect (R.double.split Γ).rot (q 0) ka
  walk : ∀ j, j + 1 < n → fconnect (R.double.split Γ).rot (R.double.rev (q j)) (q (j + 1))
  stop : fconnect (R.double.split Γ).rot (R.double.rev (q (n - 1))) kb
  simple : ∀ i j, i < n → j < n → fconnect (R.double.split Γ).rot (q i) (q j) → i = j
  simple_last : ∀ i, i < n → ¬ fconnect (R.double.split Γ).rot (q i) kb
  edges : ∀ i j, i < n → j < n → ((q i).1 = (q j).1 ∨ (q i).1 = R.rev (q j).1) → i = j
  pair : ∀ j, j < n → (((q j).1, false) ∈ Γ ↔ (R.rev (q j).1, false) ∈ Γ)
  first : ((q 0).1, false) ∈ Γ → (q 0).2 = true
  avoid : ∀ j, 0 < j → j < n → ∀ c ∈ ka :: A, ¬ fconnect (R.double.split Γ).rot (q j) c

namespace WalkCut

variable {Γ : Finset (D × Bool)} (W : R.WalkCut Γ)

/-- The digon corner of the `j`-th edge at its tail. -/
def mc (j : ℕ) : D × Bool := ((W.q j).1, false)

/-- The digon corner of the `j`-th edge at its head. -/
def rc (j : ℕ) : D × Bool := (R.rev (W.q j).1, false)

/-- The corners after cutting the first `j` edges. -/
def Γs (j : ℕ) : Finset (D × Bool) :=
  Γ ∪ (Finset.range j).image W.mc ∪ (Finset.range j).image W.rc

/-- The corners after the cut. -/
def Γ' : Finset (D × Bool) := W.Γs W.n

/-- The corner of the part of the `j`-th vertex on the side of `ka`. -/
def hc : ℕ → D × Bool
  | 0 => W.ka
  | j + 1 => W.rc j

/-- The corners `hc j, …, hc 0`. -/
def T : ℕ → List (D × Bool)
  | 0 => [W.ka]
  | j + 1 => W.hc (j + 1) :: T j

/-- The corners `r_n, …, r_1`. -/
def rs : List (D × Bool) := (List.range W.n).map fun i => W.hc (W.n - i)

theorem mem_Γs {j : ℕ} {z : D × Bool} :
    z ∈ W.Γs j ↔ z ∈ Γ ∨ ∃ i, i < j ∧ (z = W.mc i ∨ z = W.rc i) := by
  simp only [Γs, Finset.mem_union, Finset.mem_image, Finset.mem_range]
  constructor
  · rintro ((h | ⟨i, hi, rfl⟩) | ⟨i, hi, rfl⟩)
    · exact Or.inl h
    · exact Or.inr ⟨i, hi, Or.inl rfl⟩
    · exact Or.inr ⟨i, hi, Or.inr rfl⟩
  · rintro (h | ⟨i, hi, rfl | rfl⟩)
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr ⟨i, hi, rfl⟩)
    · exact Or.inr ⟨i, hi, rfl⟩

theorem subset_Γs (j : ℕ) : Γ ⊆ W.Γs j := fun _ h => W.mem_Γs.2 (Or.inl h)

theorem Γs_mono {j k : ℕ} (h : j ≤ k) : W.Γs j ⊆ W.Γs k := fun z hz => by
  rcases W.mem_Γs.1 hz with hz | ⟨i, hi, hz⟩
  · exact W.mem_Γs.2 (Or.inl hz)
  · exact W.mem_Γs.2 (Or.inr ⟨i, by omega, hz⟩)

theorem Γs_zero : W.Γs 0 = Γ := by simp [Γs]

theorem Γs_succ (j : ℕ) : W.Γs (j + 1) = insert (W.mc j) (insert (W.rc j) (W.Γs j)) := by
  ext z
  simp only [Finset.mem_insert, W.mem_Γs]
  constructor
  · rintro (h | ⟨i, hi, h⟩)
    · exact Or.inr (Or.inr (Or.inl h))
    · rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
      · exact Or.inr (Or.inr (Or.inr ⟨i, hi, h⟩))
      · rcases h with h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
  · rintro (h | h | h | ⟨i, hi, h⟩)
    · exact Or.inr ⟨j, by omega, Or.inl h⟩
    · exact Or.inr ⟨j, by omega, Or.inr h⟩
    · exact Or.inl h
    · exact Or.inr ⟨i, by omega, h⟩

theorem mc_inj {i j : ℕ} (hi : i < W.n) (hj : j < W.n) (h : W.mc i = W.mc j) : i = j := by
  have h1 := congrArg Prod.fst h
  exact W.edges i j hi hj (Or.inl h1)

theorem rc_inj {i j : ℕ} (hi : i < W.n) (hj : j < W.n) (h : W.rc i = W.rc j) : i = j := by
  have h1 : R.rev (W.q i).1 = R.rev (W.q j).1 := congrArg Prod.fst h
  have h2 := congrArg R.rev h1
  rw [R.rev_rev, R.rev_rev] at h2
  exact W.edges i j hi hj (Or.inl h2)

theorem mc_ne_rc {i j : ℕ} (hi : i < W.n) (hj : j < W.n) : W.mc i ≠ W.rc j := by
  intro h
  have h0 := congrArg Prod.fst h
  have h1 : (W.q i).1 = R.rev (W.q j).1 := h0
  obtain rfl := W.edges i j hi hj (Or.inr h1)
  exact R.rev_ne _ h1.symm

theorem mc_not_mem_Γs {j : ℕ} (hj : j < W.n) (hnew : W.mc j ∉ Γ) : W.mc j ∉ W.Γs j := by
  intro h
  rcases W.mem_Γs.1 h with h | ⟨i, hi, h | h⟩
  · exact hnew h
  · exact absurd (W.mc_inj hj (by omega) h) (by omega)
  · exact W.mc_ne_rc hj (by omega) h

theorem rc_not_mem_Γs {j : ℕ} (hj : j < W.n) (hnew : W.rc j ∉ Γ) : W.rc j ∉ W.Γs j := by
  intro h
  rcases W.mem_Γs.1 h with h | ⟨i, hi, h | h⟩
  · exact hnew h
  · exact W.mc_ne_rc (by omega) hj h.symm
  · exact absurd (W.rc_inj hj (by omega) h) (by omega)

theorem fconnect_mc {Γ₀ : Finset (D × Bool)} (j : ℕ) (h : W.mc j ∉ Γ₀) :
    fconnect (R.double.split Γ₀).rot (W.mc j) (W.q j) :=
  fconnect_digon h (W.q j).2

theorem fconnect_rc {Γ₀ : Finset (D × Bool)} (j : ℕ) (h : W.rc j ∉ Γ₀) :
    fconnect (R.double.split Γ₀).rot (W.rc j) (R.double.rev (W.q j)) :=
  fconnect_digon h (!(W.q j).2)

/-- The later vertices do not change. -/
theorem unchanged {j k : ℕ} (hjk : j < k) (hk : k < W.n) {y : D × Bool} :
    fconnect (R.double.split (W.Γs j)).rot (W.q k) y ↔ fconnect (R.double.split Γ).rot (W.q k) y :=
  R.double.fconnect_split_split_iff (W.subset_Γs j) fun w hw hw0 h => by
    obtain ⟨i, hi, rfl | rfl⟩ := (W.mem_Γs.1 hw).resolve_left hw0
    · exact absurd (W.simple k i hk (by omega) (connect_trans h (W.fconnect_mc i hw0)))
        (by omega)
    · exact absurd (W.simple k (i + 1) hk (by omega)
        (connect_trans h (connect_trans (W.fconnect_rc i hw0) (W.walk i (by omega))))) (by omega)

/-- The last vertex does not change before the last edge is cut. -/
theorem unchanged_kb {j : ℕ} (hj : j < W.n) {y : D × Bool} :
    fconnect (R.double.split (W.Γs j)).rot W.kb y ↔ fconnect (R.double.split Γ).rot W.kb y :=
  R.double.fconnect_split_split_iff (W.subset_Γs j) fun w hw hw0 h => by
    obtain ⟨i, hi, rfl | rfl⟩ := (W.mem_Γs.1 hw).resolve_left hw0
    · exact W.simple_last i (by omega) (fconnect_symm (connect_trans h (W.fconnect_mc i hw0)))
    · exact W.simple_last (i + 1) (by omega) (fconnect_symm (connect_trans h
        (connect_trans (W.fconnect_rc i hw0) (W.walk i (by omega)))))

@[simp] theorem hc_zero : W.hc 0 = W.ka := rfl

@[simp] theorem hc_succ (j : ℕ) : W.hc (j + 1) = W.rc j := rfl

theorem T_zero : W.T 0 = [W.ka] := rfl

theorem T_succ (j : ℕ) : W.T (j + 1) = W.hc (j + 1) :: W.T j := rfl

theorem T_head (j : ℕ) : W.T j = W.hc j :: (W.T j).tail := by
  cases j <;> rfl

theorem mem_T {j : ℕ} {c : D × Bool} : c ∈ W.T j ↔ ∃ i, i ≤ j ∧ c = W.hc i := by
  induction j with
  | zero =>
    constructor
    · intro h
      exact ⟨0, le_refl 0, by simpa [T_zero] using h⟩
    · rintro ⟨i, hi, rfl⟩
      obtain rfl : i = 0 := by omega
      simp [T_zero]
  | succ j ih =>
    rw [T_succ, List.mem_cons, ih]
    constructor
    · rintro (rfl | ⟨i, hi, rfl⟩)
      · exact ⟨j + 1, le_refl _, rfl⟩
      · exact ⟨i, by omega, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      rcases Nat.lt_or_ge i (j + 1) with h | h
      · exact Or.inr ⟨i, by omega, rfl⟩
      · obtain rfl : i = j + 1 := by omega
        exact Or.inl rfl

theorem T_eq (j : ℕ) : W.T j = (List.range j).map (fun i => W.hc (j - i)) ++ [W.ka] := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [T_succ, ih, List.range_succ_eq_map]
    simp [Function.comp_def, Nat.add_sub_add_right]

theorem T_n : W.T W.n = W.rs ++ [W.ka] := W.T_eq W.n

theorem ka_mem : W.ka ∈ Γ := W.bound.sub _ (List.mem_append_left _ List.mem_cons_self)

theorem kb_mem : W.kb ∈ Γ := W.bound.sub _ (List.mem_append_right _ List.mem_cons_self)

theorem subset_Γ' : Γ ⊆ W.Γ' := W.subset_Γs W.n

theorem hc_mem (j : ℕ) : W.hc j ∈ W.Γs j := by
  cases j with
  | zero => exact W.subset_Γs 0 W.ka_mem
  | succ i => exact W.mem_Γs.2 (Or.inr ⟨i, Nat.lt_succ_self i, Or.inr rfl⟩)

theorem hc_eq_rc {k : ℕ} (hk : 0 < k) : W.hc k = W.rc (k - 1) := by
  cases k with
  | zero => omega
  | succ k => rfl

theorem mem_rs {c : D × Bool} : c ∈ W.rs ↔ ∃ m, m < W.n ∧ c = W.rc m := by
  simp only [rs, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact ⟨W.n - i - 1, by omega, W.hc_eq_rc (by omega)⟩
  · rintro ⟨m, hm, rfl⟩
    refine ⟨W.n - (m + 1), by omega, ?_⟩
    rw [W.hc_eq_rc (by omega)]
    congr 2
    omega

/-- The digon corner at the tail of a new edge lies at its vertex. -/
theorem not_fconnect_mc {i j : ℕ} (hi : i < W.n) (hj : j < W.n) (hij : i ≠ j) (hnew : W.mc j ∉ Γ) :
    ¬ fconnect (R.double.split Γ).rot (W.q i) (W.mc j) := fun h =>
  hij (W.simple i j hi hj (connect_trans h (W.fconnect_mc j hnew)))

/-- The digon corner at the head of a new edge lies at the next vertex. -/
theorem not_fconnect_rc {i j : ℕ} (hi : i < W.n) (hj : j < W.n) (hij : i ≠ j + 1)
    (hnew : W.rc j ∉ Γ) : ¬ fconnect (R.double.split Γ).rot (W.q i) (W.rc j) := fun h => by
  have h1 := connect_trans h (W.fconnect_rc j hnew)
  rcases Nat.lt_or_ge (j + 1) W.n with hj1 | hj1
  · exact hij (W.simple i (j + 1) hi hj1 (connect_trans h1 (W.walk j hj1)))
  · have e : W.n - 1 = j := by omega
    exact W.simple_last i hi (connect_trans h1 (by rw [← e]; exact W.stop))

/-- The rest of the walk joins its vertices to the vertex of `kb`. -/
theorem gcomp_kb {j : ℕ} (hj : j < W.n) : ∀ m k, k + m = W.n - 1 → j ≤ k →
    (R.double.split (W.Γs j)).toHypermap.gcomp (W.q k) W.kb := by
  intro m
  induction m with
  | zero =>
    intro k hk _
    obtain rfl : k = W.n - 1 := by omega
    refine connect_trans (connect_of_rel ((R.double.split (W.Γs j)).toHypermap.glinkE _)) ?_
    exact (R.double.split (W.Γs j)).toHypermap.gcomp_of_cnode
      (fconnect_symm ((W.unchanged_kb hj).2 (fconnect_symm W.stop)))
  | succ m ih =>
    intro k hk hjk
    refine connect_trans (connect_of_rel ((R.double.split (W.Γs j)).toHypermap.glinkE _)) ?_
    refine connect_trans ((R.double.split (W.Γs j)).toHypermap.gcomp_of_cnode ?_)
      (ih (k + 1) (by omega) (by omega))
    exact fconnect_symm ((W.unchanged (by omega) (by omega)).2 (fconnect_symm (W.walk k (by omega))))

/-- **The other vertices stay.** A vertex of the split off the walk is a vertex of the cut. -/
theorem fconnect_cut_iff {z y : D × Bool}
    (hq : ∀ k, k < W.n → ¬ fconnect (R.double.split Γ).rot z (W.q k))
    (hkb : ¬ fconnect (R.double.split Γ).rot z W.kb) :
    fconnect (R.double.split W.Γ').rot z y ↔ fconnect (R.double.split Γ).rot z y :=
  R.double.fconnect_split_split_iff W.subset_Γ' fun w hw hw0 h => by
    obtain ⟨i, hi, rfl | rfl⟩ := (W.mem_Γs.1 hw).resolve_left hw0
    · exact hq i hi (connect_trans h (W.fconnect_mc i hw0))
    · rcases Nat.lt_or_ge (i + 1) W.n with h1 | h1
      · exact hq (i + 1) h1 (connect_trans h (connect_trans (W.fconnect_rc i hw0) (W.walk i h1)))
      · have e : W.n - 1 = i := by omega
        exact hkb (connect_trans h (connect_trans (W.fconnect_rc i hw0) (by rw [← e]; exact W.stop)))

/-! ### One edge at a time -/

/-- The state after cutting the first `j` edges: a boundary `hc j, …, hc 1, ka, a_1, …, a_p, kb, …`,
the `j`-th vertex at `hc j`, connected corners, the parts `hc i` of the vertices, and the copies
`(d, true)` of the edges cut so far at the parts of their tails. -/
def State (j : ℕ) : Prop :=
  (∃ Bj : List (D × Bool), R.double.Boundary (W.Γs j) (W.T j ++ W.A ++ W.kb :: Bj)) ∧
    fconnect (R.double.split (W.Γs j)).rot (W.q j) (W.hc j) ∧
    R.double.SkeletonConnected (W.Γs j) ∧
    (∀ i, i ≤ j → fconnect (R.double.split Γ).rot (W.q i) (W.hc i)) ∧
    (∀ i, i < j → fconnect (R.double.split (W.Γs j)).rot ((W.q i).1, true) (W.hc i))

/-- The state after the cut. -/
def Final : Prop :=
  R.double.Boundary W.Γ' (W.T W.n ++ W.A) ∧
    R.double.SkeletonConnected W.Γ' ∧
    (∀ i, i < W.n → fconnect (R.double.split Γ).rot (W.q i) (W.hc i)) ∧
    (∀ i, i < W.n → fconnect (R.double.split W.Γ').rot ((W.q i).1, true) (W.hc i)) ∧
    fconnect (R.double.split Γ).rot (W.rc (W.n - 1)) W.kb

theorem state_zero (hS : R.double.SkeletonConnected Γ) : W.State 0 := by
  refine ⟨⟨W.B, ?_⟩, ?_, ?_, fun i hi => ?_, fun i hi => absurd hi (Nat.not_lt_zero i)⟩
  · rw [W.Γs_zero]
    exact W.bound
  · rw [W.Γs_zero]
    exact W.start
  · rw [W.Γs_zero]
    exact hS
  · obtain rfl : i = 0 := by omega
    exact W.start

/-- The copies at the earlier vertices stay when a new edge is cut. -/
theorem stays {j : ℕ} (hj : j < W.n) (hnew : W.mc j ∉ Γ) {i : ℕ} (hi : i < j)
    (hqi : fconnect (R.double.split Γ).rot (W.q i) (W.hc i)) {z y : D × Bool}
    (hz : fconnect (R.double.split (W.Γs j)).rot z (W.hc i)) :
    fconnect (R.double.split (W.Γs (j + 1))).rot z y ↔ fconnect (R.double.split (W.Γs j)).rot z y := by
  have hrc : W.rc j ∉ Γ := fun h => hnew ((W.pair j hj).2 h)
  have key : ∀ w, fconnect (R.double.split (W.Γs j)).rot z w →
      fconnect (R.double.split Γ).rot (W.q i) w := fun w h =>
    connect_trans hqi (fconnect_of_split_subset (W.subset_Γs j) (connect_trans (fconnect_symm hz) h))
  refine R.double.fconnect_split_split_iff (W.Γs_mono (Nat.le_succ j)) fun w hw hw0 h => ?_
  rw [W.Γs_succ, Finset.mem_insert, Finset.mem_insert] at hw
  rcases hw with rfl | rfl | hw
  · exact W.not_fconnect_mc (by omega) hj (by omega) hnew (key _ h)
  · exact W.not_fconnect_rc (by omega) hj (by omega) hrc (key _ h)
  · exact hw0 hw

/-- An edge whose digon corners are corners leaves the part `hc j` through its copy `(d, true)`. -/
theorem snd_eq_true {j : ℕ} (hj : j < W.n) (hold : W.mc j ∈ Γ)
    (h2 : fconnect (R.double.split (W.Γs j)).rot (W.q j) (W.hc j)) : (W.q j).2 = true := by
  cases j with
  | zero => exact W.first hold
  | succ i =>
    by_contra hf
    have hq : W.q (i + 1) = W.mc (i + 1) :=
      Prod.ext rfl (show (W.q (i + 1)).2 = false by simpa using hf)
    rw [hq] at h2
    exact W.mc_ne_rc hj (by omega)
      (R.double.eq_of_fconnect_split (W.subset_Γs _ hold) (W.hc_mem _) h2)

/-- An edge whose digon corners are corners already: the boundary moves along it. -/
theorem step_old {j : ℕ} (hj : j < W.n) (hs : W.State j) (hold : W.mc j ∈ Γ) :
    (j + 1 < W.n → W.State (j + 1)) ∧ (j + 1 = W.n → W.Final) := by
  obtain ⟨⟨Bj, hb⟩, h2, hS, h4, h5⟩ := hs
  have hrc : W.rc j ∈ Γ := (W.pair j hj).1 hold
  have ht : (W.q j).2 = true := W.snd_eq_true hj hold h2
  have hq : ((W.q j).1, true) = W.q j := Prod.ext rfl ht.symm
  have hrev : R.double.rev (W.q j) = W.rc j := by
    show (R.rev (W.q j).1, !(W.q j).2) = (R.rev (W.q j).1, false)
    rw [ht]
    rfl
  have hΓ : W.Γs (j + 1) = W.Γs j := by
    rw [W.Γs_succ, Finset.insert_eq_of_mem (W.subset_Γs j hrc),
      Finset.insert_eq_of_mem (W.subset_Γs j hold)]
  have hψ : R.double.psi (W.Γs j) (W.rc j) = W.hc j := by
    show R.double.nodeReturn (W.Γs j) (R.double.faceReturn (W.Γs j) (W.rc j)) = W.hc j
    have hf : R.double.faceReturn (W.Γs j) (W.rc j) = W.mc j := by
      refine firstReturn_eq_of_trail _ (W.subset_Γs j hrc) ?_
      show Trail R.double.facePerm (W.Γs j) (R.double.facePerm (R.rev (W.q j).1, false)) (W.mc j)
      rw [R.double_face_false, R.rev_rev]
      exact Trail.here (W.subset_Γs j hold)
    rw [hf]
    refine R.double.nodeReturn_eq_of_fconnect (W.subset_Γs j hold) (W.hc_mem j) ?_
    show fconnect (R.double.split (W.Γs j)).rot (R.double.rot ((W.q j).1, false)) (W.hc j)
    rw [R.double_rot_false, hq]
    exact h2
  have hT := W.T_head j
  have h5' : ∀ i, i < j + 1 → fconnect (R.double.split (W.Γs (j + 1))).rot ((W.q i).1, true) (W.hc i) := by
    intro i hi
    rw [hΓ]
    rcases Nat.lt_or_ge i j with h | h
    · exact h5 i h
    · have e : i = j := by omega
      rw [e, hq]
      exact h2
  rcases List.eq_nil_or_concat' Bj with rfl | ⟨B', c, rfl⟩
  · have hb' : R.double.Boundary (W.Γs j) ((W.hc j :: ((W.T j).tail ++ W.A)) ++ [W.kb]) := by
      have h := hb
      rw [hT] at h
      simpa only [List.cons_append, List.append_assoc] using h
    have hlast : R.double.psi (W.Γs j) W.kb = W.hc j := by
      simpa using hb'.psi_append_last (by simp) (by simp)
    have hk : W.rc j = W.kb := (R.double.psi (W.Γs j)).injective (hψ.trans hlast.symm)
    have hn : j + 1 = W.n := by
      by_contra hne
      exact W.simple_last (j + 1) (by omega)
        (fconnect_symm (by rw [← hk, ← hrev]; exact W.walk j (by omega)))
    refine ⟨fun h => by omega, fun _ => ?_⟩
    unfold Final Γ'
    rw [← hn]
    refine ⟨?_, by rw [hΓ]; exact hS, fun i hi => h4 i (by omega), h5', ?_⟩
    · have h := Boundary.append_comm (P := W.T j ++ W.A) (Q := [W.kb])
        (by simpa only [List.append_assoc] using hb)
      rw [hΓ, W.T_succ, W.hc_succ, hk]
      exact h
    · rw [Nat.add_sub_cancel, hk]
  · have hb' : R.double.Boundary (W.Γs j) ((W.hc j :: ((W.T j).tail ++ W.A ++ W.kb :: B')) ++ [c]) := by
      have h := hb
      rw [hT] at h
      simpa only [List.cons_append, List.append_assoc] using h
    have hlast : R.double.psi (W.Γs j) c = W.hc j := by
      simpa using hb'.psi_append_last (by simp) (by simp)
    have hk : W.rc j = c := (R.double.psi (W.Γs j)).injective (hψ.trans hlast.symm)
    have hn : j + 1 < W.n := by
      by_contra hne
      have e1 : W.n - 1 = j := by omega
      have hs := W.stop
      rw [e1, hrev, hk] at hs
      have hcΓ : c ∈ Γ := hk ▸ hrc
      have e := R.double.eq_of_fconnect_split hcΓ W.kb_mem hs
      exact (List.nodup_cons.1 hb.nodup.of_append_right).1
        (List.mem_append_right B' (List.mem_singleton.2 e.symm))
    refine ⟨fun _ => ⟨⟨B', ?_⟩, ?_, by rw [hΓ]; exact hS, fun i hi => ?_, h5'⟩, fun h => by omega⟩
    · have h := Boundary.append_comm (P := W.T j ++ W.A ++ W.kb :: B') (Q := [c])
        (by simpa only [List.append_assoc, List.cons_append] using hb)
      rw [hΓ, W.T_succ, W.hc_succ, hk]
      exact h
    · rw [hΓ, W.hc_succ]
      exact (W.unchanged (Nat.lt_succ_self j) hn).2
        (fconnect_symm (by rw [← hrev]; exact W.walk j hn))
    · rcases Nat.lt_or_ge i (j + 1) with h | h
      · exact h4 i (by omega)
      · have e : i = j + 1 := by omega
        rw [e, W.hc_succ]
        exact fconnect_symm (by rw [← hrev]; exact W.walk j hn)

/-- The `j`-th edge, if it is new, as a cut of one edge after the first `j`. -/
def edgeCut {j : ℕ} (hj : j < W.n) (hnew : W.mc j ∉ Γ)
    (h2 : fconnect (R.double.split (W.Γs j)).rot (W.q j) (W.hc j)) : R.EdgeCut (W.Γs j) where
  d := (W.q j).1
  k1 := W.hc j
  k1_mem := W.hc_mem j
  new_m := W.mc_not_mem_Γs hj hnew
  new_r := W.rc_not_mem_Γs hj fun h => hnew ((W.pair j hj).2 h)
  tail := connect_trans (W.fconnect_mc j (W.mc_not_mem_Γs hj hnew)) h2

/-- A new edge: a slit if its head carries no corner, a chord otherwise. -/
theorem step_new (hR : R.Planar) (hC : R.Connected) {j : ℕ} (hj : j < W.n) (hs : W.State j)
    (hnew : W.mc j ∉ Γ) : (j + 1 < W.n → W.State (j + 1)) ∧ (j + 1 = W.n → W.Final) := by
  obtain ⟨⟨Bj, hb⟩, h2, hS, h4, h5⟩ := hs
  have hrc : W.rc j ∉ Γ := fun h => hnew ((W.pair j hj).2 h)
  have hr' := W.rc_not_mem_Γs hj hrc
  let E := W.edgeCut hj hnew h2
  have hE : E.Γ' = W.Γs (j + 1) := (W.Γs_succ j).symm
  have hcut : E.cut = R.double.split (W.Γs (j + 1)) := congrArg R.double.split hE
  have hEk : E.k1 = W.hc j := rfl
  have hEm : E.m = W.mc j := rfl
  have hEr : E.r = W.rc j := rfl
  have hrv : fconnect (R.double.split (W.Γs j)).rot (W.rc j) (R.double.rev (W.q j)) :=
    W.fconnect_rc j hr'
  have hT := W.T_head j
  have hS' : R.double.SkeletonConnected (W.Γs (j + 1)) := hE ▸ E.skeletonConnected hS
  have h5' : ∀ i, i < j → fconnect (R.double.split (W.Γs (j + 1))).rot ((W.q i).1, true) (W.hc i) :=
    fun i hi => (W.stays hj hnew hi (h4 i (by omega)) (h5 i hi)).2 (h5 i hi)
  have hcopy : ¬ fconnect (R.double.split (W.Γs j)).rot E.r E.k1 →
      ∀ i, i < j + 1 → fconnect (R.double.split (W.Γs (j + 1))).rot ((W.q i).1, true) (W.hc i) := by
    intro hr i hi
    rcases Nat.lt_or_ge i j with h | h
    · exact h5' i h
    · have e : i = j := by omega
      rw [e]
      have h1 := fconnect1 E.cut.rot E.k1
      rw [E.cut_rot_k1 hr, hcut] at h1
      exact fconnect_symm h1
  have hnext : j + 1 < W.n → fconnect (R.double.split (W.Γs j)).rot (W.q (j + 1)) (W.rc j) :=
    fun hn => connect_trans ((W.unchanged (Nat.lt_succ_self j) hn).2 (fconnect_symm (W.walk j hn)))
      (fconnect_symm hrv)
  have h4' : j + 1 < W.n → ∀ i, i ≤ j + 1 → fconnect (R.double.split Γ).rot (W.q i) (W.hc i) := by
    intro hn i hi
    rcases Nat.lt_or_ge i (j + 1) with h | h
    · exact h4 i (by omega)
    · have e : i = j + 1 := by omega
      rw [e, W.hc_succ]
      exact fconnect_symm (connect_trans (W.fconnect_rc j hrc) (W.walk j hn))
  by_cases hfree : E.HeadFree
  · have hn : j + 1 < W.n := by
      by_contra hne
      have e1 : W.n - 1 = j := by omega
      have hs := (W.unchanged_kb hj).2 (fconnect_symm W.stop)
      rw [e1] at hs
      exact hfree W.kb (W.subset_Γs j W.kb_mem) (connect_trans hrv (fconnect_symm hs))
    refine ⟨fun _ => ⟨⟨Bj ++ [W.mc j], ?_⟩, ?_, hS', h4' hn, hcopy (E.r_not_k1_of_free hfree)⟩,
      fun h => by omega⟩
    · have hb' : R.double.Boundary (W.Γs j) (E.k1 :: ((W.T j).tail ++ W.A ++ W.kb :: Bj)) := by
        have h := hb
        rw [hT] at h
        exact h
      have h1 := E.boundary_slit hfree hb'
      rw [hE] at h1
      have h3 := Boundary.append_comm
        (P := (W.hc j :: ((W.T j).tail ++ W.A ++ W.kb :: Bj)) ++ [W.mc j]) (Q := [W.rc j])
        (by simpa [hEk, hEm, hEr] using h1)
      rw [W.T_succ, W.hc_succ, hT]
      simpa using h3
    · rw [W.hc_succ, ← hcut]
      exact (E.cut_head_free hfree).2 (hnext hn)
  · obtain ⟨c, hcΓ, hcr⟩ : ∃ c ∈ W.Γs j, fconnect (R.double.split (W.Γs j)).rot E.r c := by
      by_contra h
      push Not at h
      exact hfree h
    have hcl : c ∈ W.T j ++ W.A ++ W.kb :: Bj := by
      refine (hb.gcomp_iff (R.double_planar hR hC) (R.double_connected hC) ⟨_, W.hc_mem j⟩ hS
        (x := W.hc j) ?_ hcΓ).1 ?_
      · rw [hT]
        exact List.mem_cons_self
      · refine connect_trans
          ((R.double.split (W.Γs j)).toHypermap.gcomp_of_cnode (fconnect_symm h2)) ?_
        refine connect_trans (connect_of_rel ((R.double.split (W.Γs j)).toHypermap.glinkE _)) ?_
        exact (R.double.split (W.Γs j)).toHypermap.gcomp_of_cnode
          (connect_trans (fconnect_symm hrv) hcr)
    rcases Nat.lt_or_ge (j + 1) W.n with hn | hn
    · have hcq : fconnect (R.double.split Γ).rot (W.q (j + 1)) c :=
        fconnect_of_split_subset (W.subset_Γs j) (connect_trans (hnext hn) hcr)
      have hcB : c ∈ Bj := by
        rcases List.mem_append.1 hcl with h | h
        · rcases List.mem_append.1 h with h | h
          · obtain ⟨i, hi, rfl⟩ := W.mem_T.1 h
            exact absurd (W.simple i (j + 1) (by omega) hn
              (connect_trans (h4 i hi) (fconnect_symm hcq))) (by omega)
          · exact absurd hcq (W.avoid (j + 1) (Nat.succ_pos j) hn c (List.mem_cons_of_mem _ h))
        rcases List.mem_cons.1 h with rfl | h
        · exact absurd hcq (W.simple_last (j + 1) hn)
        · exact h
      obtain ⟨B1, B2, rfl⟩ := List.append_of_mem hcB
      have hb' : R.double.Boundary (W.Γs j)
          ((E.k1 :: ((W.T j).tail ++ W.A ++ W.kb :: B1)) ++ (c :: B2)) := by
        have h := hb
        rw [hT] at h
        simpa only [List.cons_append, List.append_assoc, hEk] using h
      obtain ⟨-, -, hn3⟩ := List.nodup_append.1 hb'.nodup
      have hne : E.k1 ≠ c := hn3 _ List.mem_cons_self _ List.mem_cons_self
      have hhi := E.boundary_hi hcΓ hcr hb'
      have hlo := E.boundary_lo hcΓ hcr hb'
      rw [hE] at hhi hlo
      have hz : fconnect (R.double.split (W.Γs (j + 1))).rot (W.q (j + 1)) (W.rc j) := by
        rcases E.cut_head hcΓ hne (connect_trans (hnext hn) hcr) with h | h
        · rw [← hcut]
          exact h
        · exfalso
          rw [hcut] at h
          have hg : (R.double.split (W.Γs (j + 1))).toHypermap.gcomp c W.kb :=
            connect_trans ((R.double.split (W.Γs (j + 1))).toHypermap.gcomp_of_cnode
              (fconnect_symm h)) (W.gcomp_kb hn (W.n - 1 - (j + 1)) (j + 1) (by omega) le_rfl)
          have hkb := (hlo.gcomp_iff (R.double_planar hR hC) (R.double_connected hC)
            ⟨_, W.hc_mem (j + 1)⟩ hS' (x := c) (by simp) (W.subset_Γs _ W.kb_mem)).1 hg
          rcases List.mem_append.1 hkb with h | h
          · rw [List.mem_singleton] at h
            exact E.m_not_mem (h ▸ W.subset_Γs j W.kb_mem)
          · exact hn3 W.kb (by simp) W.kb h rfl
      refine ⟨fun _ => ⟨⟨B1, ?_⟩, hz, hS', h4' hn, hcopy (E.r_not_k1_of_k2 hcΓ hcr hne)⟩,
        fun h => by omega⟩
      have h3 := Boundary.append_comm hhi
      rw [W.T_succ, W.hc_succ, hT]
      simpa [hEk, hEr] using h3
    · have hn1 : j + 1 = W.n := by omega
      have e1 : W.n - 1 = j := by omega
      have hkb : fconnect (R.double.split (W.Γs j)).rot E.r W.kb := by
        have hs := (W.unchanged_kb hj).2 (fconnect_symm W.stop)
        rw [e1] at hs
        exact connect_trans hrv (fconnect_symm hs)
      obtain rfl : c = W.kb := R.double.eq_of_fconnect_split hcΓ (W.subset_Γs j W.kb_mem)
        (connect_trans (fconnect_symm hcr) hkb)
      have hb' : R.double.Boundary (W.Γs j) ((E.k1 :: ((W.T j).tail ++ W.A)) ++ (W.kb :: Bj)) := by
        have h := hb
        rw [hT] at h
        simpa only [List.cons_append, List.append_assoc, hEk] using h
      obtain ⟨-, -, hn3⟩ := List.nodup_append.1 hb'.nodup
      have hne : E.k1 ≠ W.kb := hn3 _ List.mem_cons_self _ List.mem_cons_self
      have hhi := E.boundary_hi hcΓ hcr hb'
      rw [hE] at hhi
      refine ⟨fun h => by omega, fun _ => ?_⟩
      unfold Final Γ'
      rw [← hn1]
      refine ⟨?_, hS', fun i hi => h4 i (by omega), hcopy (E.r_not_k1_of_k2 hcΓ hcr hne), ?_⟩
      · have h3 := Boundary.append_comm hhi
        rw [W.T_succ, W.hc_succ, hT]
        simpa [hEk, hEr] using h3
      · rw [Nat.add_sub_cancel]
        exact connect_trans (W.fconnect_rc j hrc) (by rw [← e1]; exact W.stop)

theorem step (hR : R.Planar) (hC : R.Connected) {j : ℕ} (hj : j < W.n) (hs : W.State j) :
    (j + 1 < W.n → W.State (j + 1)) ∧ (j + 1 = W.n → W.Final) := by
  by_cases hold : W.mc j ∈ Γ
  · exact W.step_old hj hs hold
  · exact W.step_new hR hC hj hs hold

/-- **The cut, one edge at a time.** -/
theorem state (hR : R.Planar) (hC : R.Connected) (hS : R.double.SkeletonConnected Γ) :
    ∀ j, j < W.n → W.State j
  | 0, _ => W.state_zero hS
  | j + 1, hj => (W.step hR hC (by omega) (state hR hC hS j (by omega))).1 hj

theorem final (hR : R.Planar) (hC : R.Connected) (hS : R.double.SkeletonConnected Γ) : W.Final :=
  (W.step hR hC (by have := W.pos; omega) (W.state hR hC hS (W.n - 1) (by have := W.pos; omega))).2
    (by have := W.pos; omega)

/-! ### The side of `ka` -/

/-- The copies `(d, true)` of the edges. -/
def copy : List (D × Bool) := (List.range W.n).map fun j => ((W.q j).1, true)

/-- A dart lies at the vertex of the cut of the first corner of the cut after it. -/
theorem fconnect_cut_of_fconnect {z g : D × Bool} (hg : g ∈ W.Γ')
    (h : fconnect (R.double.split Γ).rot z g) :
    ∃ c ∈ W.Γ', fconnect (R.double.split Γ).rot z c ∧ fconnect (R.double.split W.Γ').rot z c := by
  obtain ⟨c, hc⟩ := exists_trail hg h
  refine ⟨c, hc.mem, hc.to_fconnect, ?_⟩
  rw [← R.double.split_split W.subset_Γ']
  exact (hc.congr fun w hw => (R.double.split Γ).split_rot_of_not_mem hw).to_fconnect

section Side

variable (hR : R.Planar) (hC : R.Connected) (hS : R.double.SkeletonConnected Γ)
include hR hC hS

/-- **The side of `ka`.** After the cut the boundary through `ka` is `ka, a_1, …, a_p, r_n, …,
r_1`. -/
theorem boundary_hi : R.double.Boundary W.Γ' ((W.ka :: W.A) ++ W.rs) := by
  have h := (W.final hR hC hS).1
  rw [W.T_n] at h
  exact Boundary.append_comm (P := W.rs) (Q := W.ka :: W.A) (by simpa using h)

/-- The corners in the component of `ka` are the corners of its boundary. -/
theorem gcomp_hi_iff {y : D × Bool} (hy : y ∈ W.Γ') :
    (R.double.split W.Γ').toHypermap.gcomp W.ka y ↔ y ∈ (W.ka :: W.A) ++ W.rs :=
  (W.boundary_hi hR hC hS).gcomp_iff (R.double_planar hR hC) (R.double_connected hC)
    ⟨W.ka, W.subset_Γ' W.ka_mem⟩ (W.final hR hC hS).2.1
    (List.mem_append_left _ List.mem_cons_self) hy

/-- The corner `hc k` lies at the `k`-th vertex of the walk. -/
theorem fconnect_hc {k : ℕ} (hk : k < W.n) : fconnect (R.double.split Γ).rot (W.q k) (W.hc k) :=
  (W.final hR hC hS).2.2.1 k hk

/-- The copy `(d, true)` of the `k`-th edge starts at the part `hc k` of its tail. -/
theorem fconnect_copy {k : ℕ} (hk : k < W.n) :
    fconnect (R.double.split W.Γ').rot ((W.q k).1, true) (W.hc k) :=
  (W.final hR hC hS).2.2.2.1 k hk

/-- An edge whose digon corners are corners is used through its copy `(d, true)`. -/
theorem old_true {j : ℕ} (hj : j < W.n) (hold : W.mc j ∈ Γ) : (W.q j).2 = true :=
  W.snd_eq_true hj hold (W.state hR hC hS j hj).2.1

/-- **The walk on the side of `ka`.** The copies `(d, true)` of the edges form a walk of the cut
from the vertex of `ka` to the vertex of `r_n`. -/
theorem isWalk_hi : (R.double.split W.Γ').IsWalk ((R.double.split W.Γ').tail W.ka) W.copy
    ((R.double.split W.Γ').tail (W.rc (W.n - 1))) := by
  have hF := W.final hR hC hS
  have e1 : W.n - 1 + 1 = W.n := by have := W.pos; omega
  have h := isWalk_map_range (R.double.split W.Γ') (fun j => ((W.q j).1, true)) (W.n - 1)
    (u := (R.double.split W.Γ').tail W.ka) (v := (R.double.split W.Γ').tail (W.rc (W.n - 1)))
    (((R.double.split W.Γ').tail_eq_iff _ _).2 (hF.2.2.2.1 0 W.pos)) rfl
    fun j hj => (((R.double.split W.Γ').tail_eq_iff _ _).2 (hF.2.2.2.1 (j + 1) (by omega))).symm
  rw [e1] at h
  exact h

/-- **One part of each vertex on the side of `ka`.** A dart at the `k`-th vertex of the walk in the
component of `ka` lies at the vertex of the cut of `hc k`. -/
theorem part_hi {k : ℕ} (hk : k < W.n) {z : D × Bool}
    (hz : fconnect (R.double.split Γ).rot z (W.q k))
    (hg : (R.double.split W.Γ').toHypermap.gcomp W.ka z) :
    fconnect (R.double.split W.Γ').rot z (W.hc k) := by
  have hF := W.final hR hC hS
  obtain ⟨c, hcΓ, hzc, hzc'⟩ := W.fconnect_cut_of_fconnect
    (W.Γs_mono (le_of_lt hk) (W.hc_mem k)) (connect_trans hz (hF.2.2.1 k hk))
  have hqc : fconnect (R.double.split Γ).rot (W.q k) c := connect_trans (fconnect_symm hz) hzc
  have hc := (W.gcomp_hi_iff hR hC hS hcΓ).1
    (connect_trans hg ((R.double.split W.Γ').toHypermap.gcomp_of_cnode hzc'))
  suffices e : c = W.hc k by rw [← e]; exact hzc'
  rcases List.mem_append.1 hc with h | h
  · rcases Nat.eq_zero_or_pos k with rfl | hk0
    · exact R.double.eq_of_fconnect_split (W.bound.sub c (List.mem_append_left _ h)) W.ka_mem
        (connect_trans (fconnect_symm hqc) W.start)
    · exact absurd hqc (W.avoid k hk0 hk c h)
  · obtain ⟨m, hm, rfl⟩ := W.mem_rs.1 h
    rcases Nat.lt_or_ge (m + 1) W.n with h1 | h1
    · obtain rfl := W.simple k (m + 1) hk h1 (connect_trans hqc (fconnect_symm (hF.2.2.1 (m + 1) h1)))
      rfl
    · have e : W.n - 1 = m := by omega
      exact absurd (connect_trans hqc (by rw [← e]; exact hF.2.2.2.2)) (W.simple_last k hk)

/-- **One part of the last vertex on the side of `ka`.** A dart at the vertex of `kb` in the
component of `ka` lies at the vertex of the cut of `r_n`. -/
theorem part_hi_last {z : D × Bool} (hz : fconnect (R.double.split Γ).rot z W.kb)
    (hg : (R.double.split W.Γ').toHypermap.gcomp W.ka z) :
    fconnect (R.double.split W.Γ').rot z (W.rc (W.n - 1)) := by
  have hF := W.final hR hC hS
  obtain ⟨c, hcΓ, hzc, hzc'⟩ := W.fconnect_cut_of_fconnect (W.subset_Γ' W.kb_mem) hz
  have hbc : fconnect (R.double.split Γ).rot W.kb c := connect_trans (fconnect_symm hz) hzc
  have hc := (W.gcomp_hi_iff hR hC hS hcΓ).1
    (connect_trans hg ((R.double.split W.Γ').toHypermap.gcomp_of_cnode hzc'))
  suffices e : c = W.rc (W.n - 1) by rw [← e]; exact hzc'
  rcases List.mem_append.1 hc with h | h
  · obtain rfl := R.double.eq_of_fconnect_split W.kb_mem (W.bound.sub c (List.mem_append_left _ h)) hbc
    obtain ⟨-, -, hn3⟩ := List.nodup_append.1 W.bound.nodup
    exact absurd rfl (hn3 _ h _ List.mem_cons_self)
  · obtain ⟨m, hm, rfl⟩ := W.mem_rs.1 h
    rcases Nat.lt_or_ge (m + 1) W.n with h1 | h1
    · exact absurd (connect_trans (hF.2.2.1 (m + 1) h1) (fconnect_symm hbc))
        (W.simple_last (m + 1) h1)
    · rw [show W.n - 1 = m by omega]

end Side

/-! ### The side of `kb` -/

/-- The heads of distinct edges lie at distinct vertices. -/
theorem rev_inj {a b : ℕ} (ha : a < W.n) (hb : b < W.n)
    (h : fconnect (R.double.split Γ).rot (R.double.rev (W.q a)) (R.double.rev (W.q b))) :
    a = b := by
  rcases Nat.lt_or_ge (a + 1) W.n with ha1 | ha1 <;> rcases Nat.lt_or_ge (b + 1) W.n with hb1 | hb1
  · have := W.simple (a + 1) (b + 1) ha1 hb1
      (connect_trans (fconnect_symm (W.walk a ha1)) (connect_trans h (W.walk b hb1)))
    omega
  · have e : W.n - 1 = b := by omega
    have hb' : fconnect (R.double.split Γ).rot (R.double.rev (W.q b)) W.kb := by
      rw [← e]
      exact W.stop
    exact absurd (connect_trans (fconnect_symm (W.walk a ha1)) (connect_trans h hb'))
      (W.simple_last (a + 1) ha1)
  · have e : W.n - 1 = a := by omega
    have ha' : fconnect (R.double.split Γ).rot (R.double.rev (W.q a)) W.kb := by
      rw [← e]
      exact W.stop
    exact absurd (connect_trans (fconnect_symm (W.walk b hb1)) (connect_trans (fconnect_symm h) ha'))
      (W.simple_last (b + 1) hb1)
  · omega

/-- The head of an edge is not at the vertex of `ka`. -/
theorem rev_not_ka {a : ℕ} (ha : a < W.n) :
    ¬ fconnect (R.double.split Γ).rot (R.double.rev (W.q a)) W.ka := fun h => by
  have h0 := connect_trans h (fconnect_symm W.start)
  rcases Nat.lt_or_ge (a + 1) W.n with ha1 | ha1
  · have := W.simple (a + 1) 0 ha1 W.pos (connect_trans (fconnect_symm (W.walk a ha1)) h0)
    omega
  · have e : W.n - 1 = a := by omega
    have ha' : fconnect (R.double.split Γ).rot (R.double.rev (W.q a)) W.kb := by
      rw [← e]
      exact W.stop
    exact W.simple_last 0 W.pos (fconnect_symm (connect_trans (fconnect_symm ha') h0))

/-- The digon corners at the tails of the edges, in the order of the walk. -/
def ms : List (D × Bool) := (List.range W.n).map W.mc

/-- The copies `(d, false)` of the edges. -/
def copy0 : List (D × Bool) := (List.range W.n).map fun j => ((W.q j).1, false)

section Reverse

variable (hlast : (R.rev (W.q (W.n - 1)).1, false) ∈ Γ → (W.q (W.n - 1)).2 = false)
  (hB : ∀ j, 0 < j → j < W.n → ∀ c ∈ W.kb :: W.B, ¬ fconnect (R.double.split Γ).rot (W.q j) c)

/-- The walk read backwards, from the vertex of `kb` to the vertex of `ka`, if the last edge is used
through its copy `(d, false)` when its digon corners are corners and the inner vertices carry no
corner of `kb, b_1, …, b_q`. -/
def reverse : R.WalkCut Γ where
  n := W.n
  q j := R.double.rev (W.q (W.n - 1 - j))
  ka := W.kb
  kb := W.ka
  A := W.B
  B := W.A
  pos := W.pos
  bound := W.bound.append_comm
  start := by
    show fconnect _ (R.double.rev (W.q (W.n - 1 - 0))) W.kb
    rw [Nat.sub_zero]
    exact W.stop
  walk j hj := by
    show fconnect _ (R.double.rev (R.double.rev (W.q (W.n - 1 - j))))
      (R.double.rev (W.q (W.n - 1 - (j + 1))))
    rw [R.double.rev_rev]
    have h := W.walk (W.n - 1 - (j + 1)) (by omega)
    rw [show W.n - 1 - (j + 1) + 1 = W.n - 1 - j by omega] at h
    exact fconnect_symm h
  stop := by
    show fconnect _ (R.double.rev (R.double.rev (W.q (W.n - 1 - (W.n - 1))))) W.ka
    rw [R.double.rev_rev, Nat.sub_self]
    exact W.start
  simple i j hi hj h := by
    have := W.rev_inj (a := W.n - 1 - i) (b := W.n - 1 - j) (by omega) (by omega) h
    omega
  simple_last i hi := W.rev_not_ka (by omega)
  edges i j hi hj h := by
    have key : W.n - 1 - i = W.n - 1 - j := by
      rcases h with h | h
      · have h' : R.rev (W.q (W.n - 1 - i)).1 = R.rev (W.q (W.n - 1 - j)).1 := h
        have h'' := congrArg R.rev h'
        rw [R.rev_rev, R.rev_rev] at h''
        exact W.edges _ _ (by omega) (by omega) (Or.inl h'')
      · have h' : R.rev (W.q (W.n - 1 - i)).1 = R.rev (R.rev (W.q (W.n - 1 - j)).1) := h
        rw [R.rev_rev] at h'
        exact (W.edges _ _ (by omega) (by omega) (Or.inr h'.symm)).symm
    omega
  pair j hj := by
    show (R.rev (W.q (W.n - 1 - j)).1, false) ∈ Γ ↔
      (R.rev (R.rev (W.q (W.n - 1 - j)).1), false) ∈ Γ
    rw [R.rev_rev]
    exact (W.pair _ (by omega)).symm
  first h := by
    have h' : (R.rev (W.q (W.n - 1)).1, false) ∈ Γ := by
      have h1 : (R.rev (W.q (W.n - 1 - 0)).1, false) ∈ Γ := h
      rwa [Nat.sub_zero] at h1
    show (!(W.q (W.n - 1 - 0)).2) = true
    simp [hlast h']
  avoid j h0 hj c hc h := by
    have h1 := W.walk (W.n - 1 - j) (by omega)
    rw [show W.n - 1 - j + 1 = W.n - j by omega] at h1
    exact hB (W.n - j) (by omega) (by omega) c hc (connect_trans (fconnect_symm h1) h)

theorem reverse_mc (i : ℕ) : (W.reverse hlast hB).mc i = W.rc (W.n - 1 - i) := rfl

theorem reverse_rc (i : ℕ) : (W.reverse hlast hB).rc i = W.mc (W.n - 1 - i) := by
  show (R.rev (R.rev (W.q (W.n - 1 - i)).1), false) = ((W.q (W.n - 1 - i)).1, false)
  rw [R.rev_rev]

/-- The walk read backwards cuts the same edges. -/
theorem reverse_Γ' : (W.reverse hlast hB).Γ' = W.Γ' := by
  ext z
  show z ∈ (W.reverse hlast hB).Γs W.n ↔ z ∈ W.Γs W.n
  rw [(W.reverse hlast hB).mem_Γs, W.mem_Γs]
  simp only [reverse_mc, reverse_rc]
  refine or_congr_right ⟨?_, ?_⟩
  · rintro ⟨i, hi, h | h⟩
    · exact ⟨W.n - 1 - i, by omega, Or.inr h⟩
    · exact ⟨W.n - 1 - i, by omega, Or.inl h⟩
  · rintro ⟨i, hi, h | h⟩
    · refine ⟨W.n - 1 - i, by omega, Or.inr ?_⟩
      rw [show W.n - 1 - (W.n - 1 - i) = i by omega]
      exact h
    · refine ⟨W.n - 1 - i, by omega, Or.inl ?_⟩
      rw [show W.n - 1 - (W.n - 1 - i) = i by omega]
      exact h

theorem reverse_rs : (W.reverse hlast hB).rs = W.ms := by
  refine List.map_congr_left fun i hi => ?_
  have hi' : i < W.n := List.mem_range.1 hi
  show (W.reverse hlast hB).hc (W.n - i) = W.mc i
  rw [(W.reverse hlast hB).hc_eq_rc (k := W.n - i) (by omega), reverse_rc,
    show W.n - 1 - (W.n - i - 1) = i by omega]

section Lo

variable (hR : R.Planar) (hC : R.Connected) (hS : R.double.SkeletonConnected Γ)
include hlast hB hR hC hS

/-- **The side of `kb`.** After the cut the boundary through `kb` is `kb, b_1, …, b_q, m_1, …,
m_n`, with `m_j` the digon corner of the `j`-th edge at its tail. -/
theorem boundary_lo : R.double.Boundary W.Γ' ((W.kb :: W.B) ++ W.ms) := by
  rw [← W.reverse_Γ' hlast hB, ← W.reverse_rs hlast hB]
  exact (W.reverse hlast hB).boundary_hi hR hC hS

/-- The corners in the component of `kb` are the corners of its boundary. -/
theorem gcomp_lo_iff {y : D × Bool} (hy : y ∈ W.Γ') :
    (R.double.split W.Γ').toHypermap.gcomp W.kb y ↔ y ∈ (W.kb :: W.B) ++ W.ms := by
  rw [← W.reverse_Γ' hlast hB] at hy ⊢
  rw [← W.reverse_rs hlast hB]
  exact (W.reverse hlast hB).gcomp_hi_iff hR hC hS hy

/-- **The walk on the side of `kb`.** The copies `(d, false)` of the edges form a walk of the cut
from the vertex of `m_1` to the vertex of `kb`. -/
theorem isWalk_lo : (R.double.split W.Γ').IsWalk ((R.double.split W.Γ').tail (W.mc 0)) W.copy0
    ((R.double.split W.Γ').tail W.kb) := by
  have hc : ∀ k, k < W.n → fconnect (R.double.split W.Γ').rot
      (R.rev (W.q (W.n - 1 - k)).1, true) ((W.reverse hlast hB).hc k) := fun k hk => by
    have h := (W.reverse hlast hB).fconnect_copy hR hC hS (k := k) hk
    rw [W.reverse_Γ' hlast hB] at h
    exact h
  have e1 : W.n - 1 + 1 = W.n := by have := W.pos; omega
  have hv : (R.double.split W.Γ').head ((W.q (W.n - 1)).1, false) =
      (R.double.split W.Γ').tail W.kb := by
    have h := hc 0 W.pos
    rw [Nat.sub_zero] at h
    exact ((R.double.split W.Γ').tail_eq_iff _ _).2 h
  have h := isWalk_map_range (R.double.split W.Γ') (fun j => ((W.q j).1, false)) (W.n - 1)
    (u := (R.double.split W.Γ').tail (W.mc 0)) (v := (R.double.split W.Γ').tail W.kb) rfl hv
    fun j hj => by
      have h1 := hc (W.n - 1 - j) (by omega)
      rw [show W.n - 1 - (W.n - 1 - j) = j by omega,
        (W.reverse hlast hB).hc_eq_rc (k := W.n - 1 - j) (by omega), reverse_rc,
        show W.n - 1 - (W.n - 1 - j - 1) = j + 1 by omega] at h1
      exact ((R.double.split W.Γ').tail_eq_iff _ _).2 h1
  rw [e1] at h
  exact h

/-- **One part of each vertex on the side of `kb`.** A dart at the `k`-th vertex of the walk in the
component of `kb` lies at the vertex of the cut of `m_k`. -/
theorem part_lo {k : ℕ} (hk : k < W.n) {z : D × Bool}
    (hz : fconnect (R.double.split Γ).rot z (W.q k))
    (hg : (R.double.split W.Γ').toHypermap.gcomp W.kb z) :
    fconnect (R.double.split W.Γ').rot z (W.mc k) := by
  rw [← W.reverse_Γ' hlast hB] at hg ⊢
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · have h := (W.reverse hlast hB).part_hi_last hR hC hS (z := z) (connect_trans hz W.start) hg
    have e : (W.reverse hlast hB).rc ((W.reverse hlast hB).n - 1) = W.mc 0 := by
      rw [reverse_rc]
      congr 1
      show W.n - 1 - (W.n - 1) = 0
      omega
    rw [e] at h
    exact h
  · have hz' : fconnect (R.double.split Γ).rot z ((W.reverse hlast hB).q (W.n - k)) := by
      have h1 := W.walk (k - 1) (by omega)
      rw [show k - 1 + 1 = k by omega] at h1
      show fconnect _ z (R.double.rev (W.q (W.n - 1 - (W.n - k))))
      rw [show W.n - 1 - (W.n - k) = k - 1 by omega]
      exact connect_trans hz (fconnect_symm h1)
    have h := (W.reverse hlast hB).part_hi hR hC hS (k := W.n - k)
      (show W.n - k < W.n by omega) hz' hg
    rw [(W.reverse hlast hB).hc_eq_rc (k := W.n - k) (by omega), reverse_rc,
      show W.n - 1 - (W.n - k - 1) = k by omega] at h
    exact h

/-- **One part of the last vertex on the side of `kb`.** A dart at the vertex of `kb` in the
component of `kb` lies at the vertex of the cut of `kb`. -/
theorem part_lo_last {z : D × Bool} (hz : fconnect (R.double.split Γ).rot z W.kb)
    (hg : (R.double.split W.Γ').toHypermap.gcomp W.kb z) :
    fconnect (R.double.split W.Γ').rot z W.kb := by
  rw [← W.reverse_Γ' hlast hB] at hg ⊢
  have hz' : fconnect (R.double.split Γ).rot z ((W.reverse hlast hB).q 0) := by
    show fconnect _ z (R.double.rev (W.q (W.n - 1 - 0)))
    rw [Nat.sub_zero]
    exact connect_trans hz (fconnect_symm W.stop)
  exact (W.reverse hlast hB).part_hi hR hC hS (k := 0) W.pos hz' hg

end Lo

end Reverse

/-- **The two sides.** If the last edge is used through its copy `(d, false)` when its digon corners
are corners, the vertices of `ka` and `kb` lie in different components of the cut. -/
theorem not_gcomp (hR : R.Planar) (hC : R.Connected) (hS : R.double.SkeletonConnected Γ)
    (hlast : (R.rev (W.q (W.n - 1)).1, false) ∈ Γ → (W.q (W.n - 1)).2 = false) :
    ¬ (R.double.split W.Γ').toHypermap.gcomp W.ka W.kb := by
  rw [W.gcomp_hi_iff hR hC hS (W.subset_Γ' W.kb_mem)]
  intro h
  obtain ⟨-, -, hn3⟩ := List.nodup_append.1 W.bound.nodup
  rcases List.mem_append.1 h with h | h
  · exact hn3 _ h _ List.mem_cons_self rfl
  · obtain ⟨m, hm, e⟩ := W.mem_rs.1 h
    rcases Nat.lt_or_ge (m + 1) W.n with h1 | h1
    · have h2 := W.fconnect_hc hR hC hS h1
      rw [W.hc_succ, ← e] at h2
      exact W.simple_last (m + 1) h1 h2
    · obtain rfl : m = W.n - 1 := by omega
      have hrc : W.rc (W.n - 1) ∈ Γ := e ▸ W.kb_mem
      have h2 := W.old_true hR hC hS hm ((W.pair _ hm).2 hrc)
      rw [hlast hrc] at h2
      exact Bool.false_ne_true h2

end WalkCut

end RotSystem

end SsspFlow
