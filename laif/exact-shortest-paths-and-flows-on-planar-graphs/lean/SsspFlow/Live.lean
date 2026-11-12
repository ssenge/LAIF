import SsspFlow.Reroute

/-!
# Live annuli

A live annulus of the recursion of `notes/LEMMA_O.md`, in the split model of `WalkCut.lean`: a
component of `R.double.split Γ` whose boundary reads `κ0(x_a), …, κ0(x_b), L_b, κ1(y_b), …, κ1(y_a),
L_a`, with `κ0(t)` at the copy `p_t^0` of the cut and `κ1(t)` at `p_t^1`, the corners of `L_a` and
`L_b` off the path, at most one copy of each cut edge off the path, and the distance `λ_t` between
`κ0(t)` and `κ1(t)` (`CutPath.Live`). The cut of the doubled map along the path is one
(`CutPath.liveOne`). A step is a shortest walk `Q` from `κ0(x)` to `κ1(y)` with its inner vertices
off the path and through no edge of the path (`CutPath.Live.Step`). The cut along it is a `WalkCut`
read from `κ0(x)` (`CutPath.Live.hiCut`) or, backwards, from `κ1(y)` (`CutPath.Live.loCut`). Its
side of `κ0(x)` is again a live annulus if `Q` avoids the corners of `L_b` (`CutPath.Live.hi`), and
its side of `κ1(y)` is one if `Q` avoids the corners of `L_a` (`CutPath.Live.lo`). This is the
invariant (I) of Lemma O with Claims 2, 13 and 14, in the split model.
-/

set_option autoImplicit false

namespace SsspFlow

open FourColor List
open scoped ENNReal

namespace RotSystem

/-! ### Two facts of splits -/

/-- In a split, the vertex of the dart after a dart in the rotation ends at the next corner. -/
theorem fconnect_split_nodeReturn {D : Type*} [Fintype D] [DecidableEq D] (M : RotSystem D)
    (Γ : Finset D) (x : D) : fconnect (M.split Γ).rot (M.rot x) (M.nodeReturn Γ x) := by
  have h := fconnect1 (M.split Γ).rot (M.nodeReturn Γ x)
  rw [M.split_rot_apply, Equiv.Perm.inv_def, Equiv.symm_apply_apply] at h
  exact fconnect_symm h

variable {D : Type*} [Fintype D] [DecidableEq D] {R : RotSystem D}

/-- **The head of a cut edge.** If both digon corners of an edge are corners, the dart `(d, false)`
ends at the vertex of the corner after `(d, false)` on its face. -/
theorem head_eq_psi {Γ : Finset (D × Bool)} {d : D} (h0 : (d, false) ∈ Γ)
    (h1 : (R.rev d, false) ∈ Γ) :
    (R.double.split Γ).head (d, false) = (R.double.split Γ).tail (R.double.psi Γ (d, false)) := by
  have hf : R.double.faceReturn Γ (d, false) = (R.rev d, false) :=
    firstReturn_eq_of_trail _ h0 (Trail.here h1)
  have hp : R.double.psi Γ (d, false) = R.double.nodeReturn Γ (R.rev d, false) := by
    show R.double.nodeReturn Γ (R.double.faceReturn Γ (d, false)) = _
    rw [hf]
  rw [hp, show (R.double.split Γ).head (d, false) =
    (R.double.split Γ).tail (R.double.rot (R.rev d, false)) from rfl]
  exact ((R.double.split Γ).tail_eq_iff _ _).2
    (R.double.fconnect_split_nodeReturn Γ (R.rev d, false))

/-! ### Walks given by their darts -/

section Darts

variable {E : Type*} [Fintype E] [DecidableEq E] {M : RotSystem E} {n : ℕ} {q : ℕ → E}

/-- A dart of a simple walk at the head of another dart of it is the next dart. -/
theorem eq_succ_of_fconnect_rev {kb : E}
    (walk : ∀ j, j + 1 < n → fconnect M.rot (M.rev (q j)) (q (j + 1)))
    (stop : fconnect M.rot (M.rev (q (n - 1))) kb)
    (simple : ∀ i j, i < n → j < n → fconnect M.rot (q i) (q j) → i = j)
    (simple_last : ∀ i, i < n → ¬ fconnect M.rot (q i) kb)
    {i j : ℕ} (hi : i < n) (hj : j < n) (h : fconnect M.rot (q i) (M.rev (q j))) : i = j + 1 := by
  rcases Nat.lt_or_ge (j + 1) n with h1 | h1
  · exact simple i (j + 1) hi h1 (connect_trans h (walk j h1))
  · obtain rfl : j = n - 1 := by omega
    exact absurd (connect_trans h stop) (simple_last i hi)

/-- The darts of a walk and their reverses lie in the component of its start. -/
theorem gcomp_walk {ka : E} (start : fconnect M.rot (q 0) ka)
    (walk : ∀ j, j + 1 < n → fconnect M.rot (M.rev (q j)) (q (j + 1))) :
    ∀ k, k < n → M.toHypermap.gcomp ka (q k) ∧ M.toHypermap.gcomp ka (M.rev (q k)) := by
  intro k
  induction k with
  | zero =>
    intro _
    have h0 : M.toHypermap.gcomp ka (q 0) := M.toHypermap.gcomp_of_cnode (fconnect_symm start)
    exact ⟨h0, connect_trans h0 (connect_of_rel (M.toHypermap.glinkE _))⟩
  | succ k ih =>
    intro hk
    have h0 : M.toHypermap.gcomp ka (q (k + 1)) :=
      connect_trans (ih (by omega)).2 (M.toHypermap.gcomp_of_cnode (walk k hk))
    exact ⟨h0, connect_trans h0 (connect_of_rel (M.toHypermap.glinkE _))⟩

end Darts

section Copies

variable {Γ : Finset (D × Bool)} {n : ℕ} {q : ℕ → D × Bool} {kb : D × Bool}

/-- **Distinct edges.** A simple walk uses distinct edges if it uses each cut edge through one of its
two copies only. -/
theorem edges_of_copies
    (walk : ∀ j, j + 1 < n → fconnect (R.double.split Γ).rot (R.double.rev (q j)) (q (j + 1)))
    (stop : fconnect (R.double.split Γ).rot (R.double.rev (q (n - 1))) kb)
    (simple : ∀ i j, i < n → j < n → fconnect (R.double.split Γ).rot (q i) (q j) → i = j)
    (simple_last : ∀ i, i < n → ¬ fconnect (R.double.split Γ).rot (q i) kb)
    (pair : ∀ j, j < n → (((q j).1, false) ∈ Γ ↔ (R.rev (q j).1, false) ∈ Γ))
    (hold : ∀ i j, i < n → j < n → ((q i).1 = (q j).1 ∨ (q i).1 = R.rev (q j).1) →
      ((q j).1, false) ∈ Γ → q i = q j ∨ q i = R.double.rev (q j)) :
    ∀ i j, i < n → j < n → ((q i).1 = (q j).1 ∨ (q i).1 = R.rev (q j).1) → i = j := by
  intro i j hi hj he
  have hs := fun {a b : ℕ} (ha : a < n) (hb : b < n)
    (h : fconnect (R.double.split Γ).rot (q a) (R.double.rev (q b))) =>
    eq_succ_of_fconnect_rev walk stop simple simple_last ha hb h
  by_cases hΓ : ((q j).1, false) ∈ Γ
  · rcases hold i j hi hj he hΓ with h | h
    · exact simple i j hi hj (by rw [h])
    · have h1 := hs hi hj (by rw [h])
      have h2 := hs hj hi (by rw [h, R.double.rev_rev])
      omega
  · have hΓ' : (R.rev (q j).1, false) ∉ Γ := fun h => hΓ ((pair j hj).2 h)
    rcases he with he | he
    · refine simple i j hi hj ?_
      rw [show q i = ((q j).1, (q i).2) from Prod.ext he rfl]
      exact connect_trans (fconnect_symm (fconnect_digon hΓ _)) (fconnect_digon hΓ _)
    · have h1 : i = j + 1 := hs hi hj (by
        rw [show q i = (R.rev (q j).1, (q i).2) from Prod.ext he rfl]
        exact connect_trans (fconnect_symm (fconnect_digon hΓ' _)) (fconnect_digon hΓ' _))
      have h2 : j = i + 1 := hs hj hi (by
        rw [show R.double.rev (q i) = ((q j).1, !(q i).2) by
          rw [show q i = (R.rev (q j).1, (q i).2) from Prod.ext he rfl]
          simp [double_rev, R.rev_rev]]
        exact connect_trans (fconnect_symm (fconnect_digon hΓ _)) (fconnect_digon hΓ _))
      omega

/-- **The first dart.** A walk from a corner `ka` of a boundary `ka, a_1, …, a_p, kb, …` whose inner
vertices carry no corner of `ka, a_1, …, a_p` starts on a cut edge through its copy `(d, true)`,
unless it is one edge from `ka` to `kb = ψ ka`. -/
theorem first_of_boundary {ka : D × Bool} {A B : List (D × Bool)}
    (hb : R.double.Boundary Γ ((ka :: A) ++ (kb :: B)))
    (start : fconnect (R.double.split Γ).rot (q 0) ka)
    (walk : ∀ j, j + 1 < n → fconnect (R.double.split Γ).rot (R.double.rev (q j)) (q (j + 1)))
    (stop : fconnect (R.double.split Γ).rot (R.double.rev (q (n - 1))) kb)
    (simple_last : ∀ i, i < n → ¬ fconnect (R.double.split Γ).rot (q i) kb)
    (avoid : ∀ j, 0 < j → j < n → ∀ c ∈ ka :: A, ¬ fconnect (R.double.split Γ).rot (q j) c)
    (hpos : 0 < n) (hpair : ((q 0).1, false) ∈ Γ → (R.rev (q 0).1, false) ∈ Γ)
    (hdeg : A ≠ [] ∨ 1 < n ∨ ((q 0).1, false) ∉ Γ) :
    ((q 0).1, false) ∈ Γ → (q 0).2 = true := by
  intro h0
  by_contra hne
  have hq : q 0 = ((q 0).1, false) := Prod.ext rfl (by simpa using hne)
  have hq0 : q 0 ∈ Γ := by rw [hq]; exact h0
  have hka : q 0 = ka := R.double.eq_of_fconnect_split hq0 (hb.sub ka (by simp)) start
  have hh : (R.double.split Γ).head (q 0) = (R.double.split Γ).tail (R.double.psi Γ ka) := by
    rw [← hka, hq]
    exact head_eq_psi h0 (hpair h0)
  have hpsi := hb.psi_getElem (i := 0) (by simp)
  have hnext : ∀ c, R.double.psi Γ ka = c → 1 < n → fconnect (R.double.split Γ).rot (q 1) c := by
    rintro c rfl h1
    have := walk 0 h1
    exact fconnect_symm (((R.double.split Γ).tail_eq_iff _ _).1 (hh.symm.trans
      (((R.double.split Γ).tail_eq_iff _ _).2 this)))
  cases A with
  | nil =>
    simp only [List.cons_append, List.nil_append, List.getElem_cons_zero,
      List.getElem_cons_succ] at hpsi
    have h1 : 1 < n := by
      rcases hdeg with h | h | h
      · exact absurd rfl h
      · exact h
      · exact absurd h0 h
    exact simple_last 1 h1 (hnext kb hpsi h1)
  | cons a A' =>
    simp only [List.cons_append, List.getElem_cons_zero, List.getElem_cons_succ] at hpsi
    rcases Nat.lt_or_ge 1 n with h1 | h1
    · exact avoid 1 (by omega) h1 a (by simp) (hnext a hpsi h1)
    · obtain rfl : n = 1 := by omega
      have hs : (R.double.split Γ).tail a = (R.double.split Γ).tail kb := by
        rw [← hpsi, ← hh]
        exact ((R.double.split Γ).tail_eq_iff _ _).2 stop
      have hab := R.double.eq_of_fconnect_split (hb.sub a (by simp)) (hb.sub kb (by simp))
        (((R.double.split Γ).tail_eq_iff _ _).1 hs)
      obtain ⟨-, -, hn3⟩ := List.nodup_append.1 hb.nodup
      exact hn3 a (by simp) kb (by simp) hab

end Copies

/-- A cut along a walk from its data, with distinct edges from `edges_of_copies` and the first dart
from `first_of_boundary`. -/
def WalkCut.ofWalk {Γ : Finset (D × Bool)} (n : ℕ) (q : ℕ → D × Bool) (ka kb : D × Bool)
    (A B : List (D × Bool)) (pos : 0 < n) (bound : R.double.Boundary Γ ((ka :: A) ++ (kb :: B)))
    (start : fconnect (R.double.split Γ).rot (q 0) ka)
    (walk : ∀ j, j + 1 < n → fconnect (R.double.split Γ).rot (R.double.rev (q j)) (q (j + 1)))
    (stop : fconnect (R.double.split Γ).rot (R.double.rev (q (n - 1))) kb)
    (simple : ∀ i j, i < n → j < n → fconnect (R.double.split Γ).rot (q i) (q j) → i = j)
    (simple_last : ∀ i, i < n → ¬ fconnect (R.double.split Γ).rot (q i) kb)
    (pair : ∀ j, j < n → (((q j).1, false) ∈ Γ ↔ (R.rev (q j).1, false) ∈ Γ))
    (avoid : ∀ j, 0 < j → j < n → ∀ c ∈ ka :: A, ¬ fconnect (R.double.split Γ).rot (q j) c)
    (hold : ∀ i j, i < n → j < n → ((q i).1 = (q j).1 ∨ (q i).1 = R.rev (q j).1) →
      ((q j).1, false) ∈ Γ → q i = q j ∨ q i = R.double.rev (q j))
    (hdeg : A ≠ [] ∨ 1 < n ∨ ((q 0).1, false) ∉ Γ) : R.WalkCut Γ where
  n := n
  q := q
  ka := ka
  kb := kb
  A := A
  B := B
  pos := pos
  bound := bound
  start := start
  walk := walk
  stop := stop
  simple := simple
  simple_last := simple_last
  edges := edges_of_copies walk stop simple simple_last pair hold
  pair := pair
  first := first_of_boundary bound start walk stop simple_last avoid pos (pair 0 pos).1 hdeg
  avoid := avoid

namespace WalkCut

variable {Γ : Finset (D × Bool)} (W : R.WalkCut Γ)

theorem rs_eq : W.rs = W.rc (W.n - 1) :: (List.range (W.n - 1)).map fun i => W.hc (W.n - 1 - i) := by
  obtain ⟨k, hk⟩ : ∃ k, W.n = k + 1 := ⟨W.n - 1, by have := W.pos; omega⟩
  unfold rs
  rw [hk, List.range_succ_eq_map, List.map_cons, List.map_map]
  refine congrArg₂ _ rfl (List.map_congr_left fun i _ => ?_)
  simp only [Function.comp_apply]
  congr 1
  omega

/-- The corners of `r_{n-1}, …, r_1`. -/
theorem mem_rs_tail {c : D × Bool} (hc : c ∈ W.rs.tail) :
    ∃ j, 0 < j ∧ j < W.n ∧ c = W.rc (j - 1) := by
  rw [W.rs_eq, List.tail_cons] at hc
  obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hc
  rw [List.mem_range] at hi
  refine ⟨W.n - 1 - i, by omega, by omega, ?_⟩
  rw [W.hc_eq_rc (by omega)]

/-- The inner corners of the side of `ka` lie at inner vertices of the walk. -/
theorem tail_rs_tail {c : D × Bool} (hc : c ∈ W.rs.tail) :
    ∃ j, 0 < j ∧ j < W.n ∧ R.tail c.1 = R.tail (W.q j).1 := by
  obtain ⟨j, h0, hj, rfl⟩ := W.mem_rs_tail hc
  refine ⟨j, h0, hj, ?_⟩
  have := DiskChord.tail_fst (W.walk (j - 1) (by omega))
  rwa [show j - 1 + 1 = j by omega] at this

/-- The digon corners come in pairs after the cut if they do before it. -/
theorem pair_Γ' (hp : ∀ d, (d, false) ∈ Γ → (R.rev d, false) ∈ Γ) :
    ∀ d, (d, false) ∈ W.Γ' → (R.rev d, false) ∈ W.Γ' := by
  intro d hd
  rcases W.mem_Γs.1 hd with h | ⟨i, hi, h | h⟩
  · exact W.subset_Γ' (hp d h)
  · have e : d = (W.q i).1 := congrArg Prod.fst h
    exact W.mem_Γs.2 (Or.inr ⟨i, hi, Or.inr (by rw [e]; rfl)⟩)
  · have e : d = R.rev (W.q i).1 := congrArg Prod.fst h
    exact W.mem_Γs.2 (Or.inr ⟨i, hi, Or.inl (by rw [e, R.rev_rev]; rfl)⟩)

section Side

variable (hR : R.Planar) (hC : R.Connected) (hS : R.double.SkeletonConnected Γ)
include hR hC hS

/-- A corner `r_j` of the cut that was a corner before lies on the boundary through `ka`. -/
theorem rc_mem_bound {j : ℕ} (hj : j < W.n) (h : W.rc j ∈ Γ) :
    W.rc j ∈ (W.ka :: W.A) ++ (W.kb :: W.B) := by
  have ht := W.old_true hR hC hS hj ((W.pair j hj).2 h)
  have he : (R.double.split Γ).rev (W.q j) = W.rc j := by
    show (R.rev (W.q j).1, !(W.q j).2) = (R.rev (W.q j).1, false)
    rw [ht]
    rfl
  have hg := (gcomp_walk W.start W.walk j hj).2
  rw [he] at hg
  exact (W.bound.gcomp_iff (R.double_planar hR hC) (R.double_connected hC) ⟨W.ka, W.ka_mem⟩ hS
    (List.mem_append_left _ List.mem_cons_self) h).1 hg

/-- If no edge of the walk has both digon corners on the boundary through `ka`, no corner `m_j` lies
on the side of `ka`. -/
theorem mc_not_mem_hi {S : Finset (D × Bool)}
    (hold : ∀ d, (d, false) ∉ S → (d, false) ∈ (W.ka :: W.A) ++ (W.kb :: W.B) →
      (R.rev d, false) ∉ (W.ka :: W.A) ++ (W.kb :: W.B))
    (hnoS : ∀ j, j < W.n → W.mc j ∉ S) {j : ℕ} (hj : j < W.n) :
    W.mc j ∉ (W.ka :: W.A) ++ W.rs := by
  intro h
  rcases List.mem_append.1 h with h | h
  · have hΓ : W.mc j ∈ Γ := W.bound.sub _ (List.mem_append_left _ h)
    exact hold (W.q j).1 (hnoS j hj) (List.mem_append_left _ h)
      (W.rc_mem_bound hR hC hS hj ((W.pair j hj).1 hΓ))
  · obtain ⟨i, hi, he⟩ := W.mem_rs.1 h
    exact W.mc_ne_rc hj hi he

/-- The side of `ka` has the property of `mc_not_mem_hi` again. -/
theorem old_hi {S : Finset (D × Bool)}
    (hold : ∀ d, (d, false) ∉ S → (d, false) ∈ (W.ka :: W.A) ++ (W.kb :: W.B) →
      (R.rev d, false) ∉ (W.ka :: W.A) ++ (W.kb :: W.B))
    (hnoS : ∀ j, j < W.n → W.mc j ∉ S) :
    ∀ d, (d, false) ∉ S → (d, false) ∈ (W.ka :: W.A) ++ W.rs →
      (R.rev d, false) ∉ (W.ka :: W.A) ++ W.rs := by
  intro d hdS hd hr
  rcases List.mem_append.1 hd with hd | hd
  · rcases List.mem_append.1 hr with hr | hr
    · exact hold d hdS (List.mem_append_left _ hd) (List.mem_append_left _ hr)
    · obtain ⟨j, hj, he⟩ := W.mem_rs.1 hr
      have e : d = (W.q j).1 := by
        have h1 : R.rev d = R.rev (W.q j).1 := congrArg Prod.fst he
        rw [← R.rev_rev d, h1, R.rev_rev]
      have hm : W.mc j = (d, false) := by rw [e]; rfl
      have hm' : W.mc j ∈ (W.ka :: W.A) ++ W.rs := by
        rw [hm]
        exact List.mem_append_left _ hd
      exact W.mc_not_mem_hi hR hC hS hold hnoS hj hm'
  · obtain ⟨j, hj, he⟩ := W.mem_rs.1 hd
    have e : R.rev d = (W.q j).1 := by
      have h1 : d = R.rev (W.q j).1 := congrArg Prod.fst he
      rw [h1, R.rev_rev]
    have hm : W.mc j = (R.rev d, false) := by rw [e]; rfl
    have hm' : W.mc j ∈ (W.ka :: W.A) ++ W.rs := by
      rw [hm]
      exact hr
    exact W.mc_not_mem_hi hR hC hS hold hnoS hj hm'

/-- The corners of the side of `ka` lie in its component. -/
theorem gcomp_of_mem_hi {c : D × Bool} (hc : c ∈ (W.ka :: W.A) ++ W.rs) :
    (R.double.split W.Γ').toHypermap.gcomp W.ka c :=
  (W.gcomp_hi_iff hR hC hS ((W.boundary_hi hR hC hS).sub c hc)).2 hc

theorem fconnect_rc_last : fconnect (R.double.split Γ).rot (W.rc (W.n - 1)) W.kb :=
  (W.final hR hC hS).2.2.2.2

end Side

end WalkCut

end RotSystem

/-! ### Pieces of corner lists -/

theorem cornerSeg_split {α : Type*} (f : ℕ → α) {a x b : ℕ} (hax : a ≤ x) (hxb : x ≤ b) :
    cornerSeg f a b = (List.range' a (x - a)).map f ++ f x :: cornerSeg f (x + 1) b := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hax
  obtain ⟨l, rfl⟩ := Nat.exists_eq_add_of_le hxb
  simp only [cornerSeg, show a + k + l + 1 - a = k + (l + 1) by omega, show a + k - a = k by omega,
    show a + k + l + 1 - (a + k + 1) = l by omega, ← List.range'_append_1, List.map_append,
    List.range'_succ, List.map_cons]

theorem cornerSeg_congr {α : Type*} {f f' : ℕ → α} {a b : ℕ}
    (h : ∀ t, a ≤ t → t ≤ b → f t = f' t) : cornerSeg f a b = cornerSeg f' a b := by
  unfold cornerSeg
  refine List.map_congr_left fun t ht => ?_
  rw [List.mem_range'_1] at ht
  exact h t ht.1 (by omega)

theorem mem_cornerSeg {α : Type*} {f : ℕ → α} {a b : ℕ} {c : α} :
    c ∈ cornerSeg f a b ↔ ∃ t, a ≤ t ∧ t ≤ b ∧ f t = c := by
  unfold cornerSeg
  simp only [List.mem_map, List.mem_range'_1]
  constructor
  · rintro ⟨t, ⟨h1, h2⟩, rfl⟩
    exact ⟨t, h1, by omega, rfl⟩
  · rintro ⟨t, h1, h2, rfl⟩
    exact ⟨t, ⟨h1, by omega⟩, rfl⟩

/-- The list `f (n - 1), …, f 0`. -/
theorem map_range_sub_eq_reverse {α : Type*} (f : ℕ → α) (n : ℕ) :
    (List.range n).map (fun j => f (n - 1 - j)) = ((List.range n).map f).reverse := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have e1 : (List.range (n + 1)).map (fun j => f (n + 1 - 1 - j)) =
        f n :: (List.range n).map (fun j => f (n - 1 - j)) := by
      rw [List.range_succ_eq_map, List.map_cons, List.map_map]
      refine congrArg₂ _ (by simp) (List.map_congr_left fun j _ => ?_)
      simp only [Function.comp_apply]
      congr 1
      omega
    rw [e1, ih, List.range_succ, List.map_append, List.reverse_append, List.map_singleton,
      List.reverse_singleton, List.singleton_append]

namespace RotSystem

variable {D : Type*} [Fintype D] [DecidableEq D] {R : RotSystem D}

/-- The boundary `κ0(x_a), …, κ0(x_b), L_b, κ1(y_b), …, κ1(y_a), L_a` of a live annulus. -/
def liveBoundary (κ0 κ1 : ℕ → D × Bool) (xa xb ya yb : ℕ) (La Lb : List (D × Bool)) :
    List (D × Bool) :=
  cornerSeg κ0 xa xb ++ Lb ++ (cornerSeg κ1 ya yb).reverse ++ La

namespace CutPath

variable (C : R.CutPath)

/-- The digon corners of the cut come in pairs. -/
theorem pair_Γ {d : D} (h : (d, false) ∈ C.Γ) : (R.rev d, false) ∈ C.Γ := by
  obtain ⟨σ, t, ht, he⟩ := C.mem_Γ.1 h
  fin_cases σ
  · have he' : (d, false) = C.k0 t := he
    unfold k0 at he'
    split_ifs at he' with h1
    · obtain rfl : d = C.e t := congrArg Prod.fst he'
      have := C.k_mem (σ := 1) (t := t + 1) (by omega)
      simpa [k1] using this
    · simp at he'
  · have he' : (d, false) = C.k1 t := he
    unfold k1 at he'
    split_ifs at he' with h1
    · simp at he'
    · obtain rfl : d = R.rev (C.e (t - 1)) := congrArg Prod.fst he'
      have := C.k_mem (σ := 0) (t := t - 1) (by omega)
      simpa [k0, R.rev_rev, show t - 1 < C.m by omega] using this

/-- The corners of the cut lie at the vertices of the path. -/
theorem tail_of_mem_Γ {z : D × Bool} (hz : z ∈ C.Γ) : ∃ t, t ≤ C.m ∧ R.tail z.1 = C.v t := by
  obtain ⟨σ, t, ht, rfl⟩ := C.mem_Γ.1 hz
  exact ⟨t, ht, C.tail_k ht⟩

variable (g : D → ℝ≥0∞)

/-- `λ_t`: the distance in the cut between the copies `p_t^0` and `p_t^1`. -/
noncomputable def lamD (t : ℕ) : ℝ≥0∞ :=
  C.cut.walkDist (g ∘ Prod.fst) (C.cut.tail (C.k 0 t)) (C.cut.tail (C.k 1 t))

/-- **A live annulus**: the component of a corner of `Γ` in `R.double.split Γ`, with the boundary
`κ0(x_a), …, κ0(x_b), L_b, κ1(y_b), …, κ1(y_a), L_a` (`liveBoundary`). The corner `κ0(t)` lies at the
copy `p_t^0` of the cut and `κ1(t)` at `p_t^1`, the corners of `L_a` and `L_b` lie off the path, no
cut edge off the path has both digon corners on the boundary, and the distance between `κ0(t)` and
`κ1(t)` is `λ_t`. -/
structure Live (Γ : Finset (D × Bool)) where
  /-- The first index of `κ0`. -/
  xa : ℕ
  /-- The last index of `κ0`. -/
  xb : ℕ
  /-- The first index of `κ1`. -/
  ya : ℕ
  /-- The last index of `κ1`. -/
  yb : ℕ
  /-- The corners at the copies `p_t^0`. -/
  κ0 : ℕ → D × Bool
  /-- The corners at the copies `p_t^1`. -/
  κ1 : ℕ → D × Bool
  /-- The inner corners of the bounding path from `κ1(y_a)` to `κ0(x_a)`. -/
  La : List (D × Bool)
  /-- The inner corners of the bounding path from `κ0(x_b)` to `κ1(y_b)`. -/
  Lb : List (D × Bool)
  le_x : xa ≤ xb
  le_y : ya ≤ yb
  xb_le : xb ≤ C.m
  yb_le : yb ≤ C.m
  sub : C.Γ ⊆ Γ
  pair : ∀ d, (d, false) ∈ Γ → (R.rev d, false) ∈ Γ
  skel : R.double.SkeletonConnected Γ
  bound : R.double.Boundary Γ (liveBoundary κ0 κ1 xa xb ya yb La Lb)
  piece0 : ∀ t, xa ≤ t → t ≤ xb → fconnect C.cut.rot (κ0 t) (C.k 0 t)
  piece1 : ∀ t, ya ≤ t → t ≤ yb → fconnect C.cut.rot (κ1 t) (C.k 1 t)
  off : ∀ c ∈ Lb ++ La, ∀ t, t ≤ C.m → R.tail c.1 ≠ C.v t
  old : ∀ d, (d, false) ∉ C.Γ → (d, false) ∈ liveBoundary κ0 κ1 xa xb ya yb La Lb →
    (R.rev d, false) ∉ liveBoundary κ0 κ1 xa xb ya yb La Lb
  dist : ∀ t, xa ≤ t → ya ≤ t → t ≤ xb → t ≤ yb →
    (R.double.split Γ).walkDist (g ∘ Prod.fst) ((R.double.split Γ).tail (κ0 t))
      ((R.double.split Γ).tail (κ1 t)) = C.lamD g t

theorem liveBoundary_one :
    liveBoundary (C.k 0) (C.k 1) 0 C.m 0 C.m [] [] = Recursion.copyCorners C.k C.m := by
  simp only [liveBoundary, cornerSeg, Recursion.copyCorners, Nat.sub_zero, List.append_nil,
    List.range_eq_range', List.map_reverse]

/-- **Claim 2.** The cut is a live annulus, with `x_a = y_a = 0`, `x_b = y_b = m` and no inner
corners of bounding paths. -/
def liveOne : C.Live g C.Γ where
  xa := 0
  xb := C.m
  ya := 0
  yb := C.m
  κ0 := C.k 0
  κ1 := C.k 1
  La := []
  Lb := []
  le_x := Nat.zero_le _
  le_y := Nat.zero_le _
  xb_le := le_rfl
  yb_le := le_rfl
  sub := Finset.Subset.refl _
  pair := fun _ h => C.pair_Γ h
  skel := C.skeletonConnected
  bound := by
    rw [liveBoundary_one]
    exact ⟨C.nodup, fun c hc => List.mem_toFinset.2 hc, fun c _ => by rw [C.psi_eq]⟩
  piece0 := fun _ _ _ => connect_refl _
  piece1 := fun _ _ _ => connect_refl _
  off := by simp
  old := fun d hd h => absurd (by rw [liveBoundary_one] at h; exact List.mem_toFinset.2 h) hd
  dist := fun _ _ _ _ _ => rfl

namespace Live

variable {C g} {Γ : Finset (D × Bool)} (L : C.Live g Γ)

theorem tail_κ0 {t : ℕ} (h1 : L.xa ≤ t) (h2 : t ≤ L.xb) : R.tail (L.κ0 t).1 = C.v t := by
  rw [C.tail_fst_of_cut ((C.cut.tail_eq_iff _ _).2 (L.piece0 t h1 h2)), C.tail_k (h2.trans L.xb_le)]

theorem tail_κ1 {t : ℕ} (h1 : L.ya ≤ t) (h2 : t ≤ L.yb) : R.tail (L.κ1 t).1 = C.v t := by
  rw [C.tail_fst_of_cut ((C.cut.tail_eq_iff _ _).2 (L.piece1 t h1 h2)), C.tail_k (h2.trans L.yb_le)]

/-- A dart off the path is not at a corner `κ0(t)`. -/
theorem not_fconnect_κ0 {z : D × Bool} (hz : ∀ t, t ≤ C.m → R.tail z.1 ≠ C.v t) {t : ℕ}
    (h1 : L.xa ≤ t) (h2 : t ≤ L.xb) : ¬ fconnect (R.double.split Γ).rot z (L.κ0 t) := fun h =>
  hz t (h2.trans L.xb_le) ((DiskChord.tail_fst h).trans (L.tail_κ0 h1 h2))

/-- A dart off the path is not at a corner `κ1(t)`. -/
theorem not_fconnect_κ1 {z : D × Bool} (hz : ∀ t, t ≤ C.m → R.tail z.1 ≠ C.v t) {t : ℕ}
    (h1 : L.ya ≤ t) (h2 : t ≤ L.yb) : ¬ fconnect (R.double.split Γ).rot z (L.κ1 t) := fun h =>
  hz t (h2.trans L.yb_le) ((DiskChord.tail_fst h).trans (L.tail_κ1 h1 h2))

include L in
theorem pair_iff (d : D) : (d, false) ∈ Γ ↔ (R.rev d, false) ∈ Γ :=
  ⟨L.pair d, fun h => by simpa [R.rev_rev] using L.pair _ h⟩

/-- **The step in a live annulus.** A simple walk of the split from the vertex of `κ0(x)` to the
vertex of `κ1(y)`, with its inner vertices off the path, through no edge of the path, and shortest
between its ends, of finite length: the part `Q` of the computed shortest walk. -/
structure Step where
  /-- The index of the first end. -/
  x : ℕ
  /-- The index of the last end. -/
  y : ℕ
  hxa : L.xa ≤ x
  hxb : x ≤ L.xb
  hya : L.ya ≤ y
  hyb : y ≤ L.yb
  /-- The number of edges. -/
  n : ℕ
  /-- The darts. -/
  q : ℕ → D × Bool
  pos : 0 < n
  start : fconnect (R.double.split Γ).rot (q 0) (L.κ0 x)
  walk : ∀ j, j + 1 < n → fconnect (R.double.split Γ).rot (R.double.rev (q j)) (q (j + 1))
  stop : fconnect (R.double.split Γ).rot (R.double.rev (q (n - 1))) (L.κ1 y)
  simple : ∀ i j, i < n → j < n → fconnect (R.double.split Γ).rot (q i) (q j) → i = j
  simple_last : ∀ i, i < n → ¬ fconnect (R.double.split Γ).rot (q i) (L.κ1 y)
  inner : ∀ j, 0 < j → j < n → ∀ t, t ≤ C.m → R.tail (q j).1 ≠ C.v t
  noP : ∀ j, j < n → ((q j).1, false) ∉ C.Γ
  short : ∀ p, (R.double.split Γ).IsWalk ((R.double.split Γ).tail (L.κ0 x)) p
      ((R.double.split Γ).tail (L.κ1 y)) →
    (((List.range n).map q).map (g ∘ Prod.fst)).sum ≤ (p.map (g ∘ Prod.fst)).sum
  fin : (((List.range n).map q).map (g ∘ Prod.fst)).sum ≠ ⊤

/-- The corners after `κ0(x)` up to `κ1(y)`. -/
def hiA (x y : ℕ) : List (D × Bool) :=
  cornerSeg L.κ0 (x + 1) L.xb ++ L.Lb ++ (cornerSeg L.κ1 (y + 1) L.yb).reverse

/-- The corners after `κ1(y)` up to `κ0(x)`. -/
def hiB (x y : ℕ) : List (D × Bool) :=
  ((List.range' L.ya (y - L.ya)).map L.κ1).reverse ++ L.La ++ (List.range' L.xa (x - L.xa)).map L.κ0

theorem xy_eq (x y : ℕ) : (L.κ0 x :: L.hiA x y) ++ (L.κ1 y :: L.hiB x y) =
    ((L.κ0 x :: L.hiA x y) ++ (L.κ1 y :: (((List.range' L.ya (y - L.ya)).map L.κ1).reverse ++
      L.La))) ++ (List.range' L.xa (x - L.xa)).map L.κ0 := by
  simp [hiB, List.append_assoc]

section Rotate

variable {x y : ℕ} (hxa : L.xa ≤ x) (hxb : x ≤ L.xb) (hya : L.ya ≤ y) (hyb : y ≤ L.yb)
include hxa hxb hya hyb

theorem liveBoundary_rot :
    liveBoundary L.κ0 L.κ1 L.xa L.xb L.ya L.yb L.La L.Lb =
      (List.range' L.xa (x - L.xa)).map L.κ0 ++ ((L.κ0 x :: L.hiA x y) ++
        (L.κ1 y :: (((List.range' L.ya (y - L.ya)).map L.κ1).reverse ++ L.La))) := by
  unfold liveBoundary hiA
  rw [cornerSeg_split L.κ0 hxa hxb, cornerSeg_split L.κ1 hya hyb]
  simp [List.reverse_append, List.append_assoc]

/-- The boundary read from `κ0(x)`. -/
theorem bound_xy : R.double.Boundary Γ ((L.κ0 x :: L.hiA x y) ++ (L.κ1 y :: L.hiB x y)) := by
  have h := L.bound
  rw [L.liveBoundary_rot hxa hxb hya hyb] at h
  rw [L.xy_eq]
  exact h.append_comm

theorem mem_xy {c : D × Bool} : c ∈ (L.κ0 x :: L.hiA x y) ++ (L.κ1 y :: L.hiB x y) ↔
    c ∈ liveBoundary L.κ0 L.κ1 L.xa L.xb L.ya L.yb L.La L.Lb := by
  rw [L.liveBoundary_rot hxa hxb hya hyb, L.xy_eq]
  simp only [List.mem_append]
  tauto

end Rotate

/-- **One copy of each cut edge.** A walk from a corner of the boundary through no edge of the path
uses every cut edge through one of its two copies only. -/
theorem hold_of_walk (hR : R.Planar) (hC : R.Connected) {n : ℕ} {q : ℕ → D × Bool} {c0 : D × Bool}
    (hc0 : c0 ∈ liveBoundary L.κ0 L.κ1 L.xa L.xb L.ya L.yb L.La L.Lb)
    (start : fconnect (R.double.split Γ).rot (q 0) c0)
    (walk : ∀ j, j + 1 < n → fconnect (R.double.split Γ).rot (R.double.rev (q j)) (q (j + 1)))
    (noP : ∀ j, j < n → ((q j).1, false) ∉ C.Γ) :
    ∀ i j, i < n → j < n → ((q i).1 = (q j).1 ∨ (q i).1 = R.rev (q j).1) →
      ((q j).1, false) ∈ Γ → q i = q j ∨ q i = R.double.rev (q j) := by
  intro i j hi hj he hΓ
  have hl : ∀ z, z ∈ Γ → (R.double.split Γ).toHypermap.gcomp c0 z →
      z ∈ liveBoundary L.κ0 L.κ1 L.xa L.xb L.ya L.yb L.La L.Lb := fun z hz hg =>
    (L.bound.gcomp_iff (R.double_planar hR hC) (R.double_connected hC) ⟨c0, L.bound.sub _ hc0⟩
      L.skel hc0 hz).1 hg
  have gi := gcomp_walk start walk i hi
  have gj := gcomp_walk start walk j hj
  have hΓr : (R.rev (q j).1, false) ∈ Γ := L.pair _ hΓ
  have key : ((q j).1, false) ∈ liveBoundary L.κ0 L.κ1 L.xa L.xb L.ya L.yb L.La L.Lb →
      (R.rev (q j).1, false) ∈ liveBoundary L.κ0 L.κ1 L.xa L.xb L.ya L.yb L.La L.Lb → False :=
    fun h1 h2 => L.old _ (noP j hj) h1 h2
  have ri : (R.double.split Γ).rev (q i) = (R.rev (q i).1, !(q i).2) := rfl
  have rj : (R.double.split Γ).rev (q j) = (R.rev (q j).1, !(q j).2) := rfl
  rcases he with he | he
  · by_cases hb : (q i).2 = (q j).2
    · exact Or.inl (Prod.ext he hb)
    · exfalso
      cases hbj : (q j).2 with
      | false =>
        have hbi : (q i).2 = true := by rw [hbj] at hb; simpa using hb
        have e1 : ((q j).1, false) = q j := Prod.ext rfl hbj.symm
        have e2 : (R.rev (q j).1, false) = (R.double.split Γ).rev (q i) := by rw [ri, he, hbi]; rfl
        refine key (hl _ hΓ ?_) (hl _ hΓr ?_)
        · rw [e1]; exact gj.1
        · rw [e2]; exact gi.2
      | true =>
        have hbi : (q i).2 = false := by rw [hbj] at hb; simpa using hb
        have e1 : ((q j).1, false) = q i := Prod.ext he.symm hbi.symm
        have e2 : (R.rev (q j).1, false) = (R.double.split Γ).rev (q j) := by rw [rj, hbj]; rfl
        refine key (hl _ hΓ ?_) (hl _ hΓr ?_)
        · rw [e1]; exact gi.1
        · rw [e2]; exact gj.2
  · by_cases hb : (q i).2 = !(q j).2
    · exact Or.inr (Prod.ext he hb)
    · exfalso
      have hb' : (q i).2 = (q j).2 := by
        cases h1 : (q i).2 <;> cases h2 : (q j).2 <;> simp_all
      cases hbj : (q j).2 with
      | false =>
        have e1 : ((q j).1, false) = q j := Prod.ext rfl hbj.symm
        have e2 : (R.rev (q j).1, false) = q i := Prod.ext he.symm (by rw [hb', hbj])
        refine key (hl _ hΓ ?_) (hl _ hΓr ?_)
        · rw [e1]; exact gj.1
        · rw [e2]; exact gi.1
      | true =>
        have e1 : ((q j).1, false) = (R.double.split Γ).rev (q i) := by
          rw [ri, he, hb', hbj, R.rev_rev]; rfl
        have e2 : (R.rev (q j).1, false) = (R.double.split Γ).rev (q j) := by rw [rj, hbj]; rfl
        refine key (hl _ hΓ ?_) (hl _ hΓr ?_)
        · rw [e1]; exact gi.2
        · rw [e2]; exact gj.2

section Hi

variable (hR : R.Planar) (hC : R.Connected) (S : L.Step)
  (noB : ∀ j, 0 < j → j < S.n → ∀ c ∈ L.Lb, ¬ fconnect (R.double.split Γ).rot (S.q j) c)
  (hdeg : L.hiA S.x S.y ≠ [] ∨ 1 < S.n ∨ ((S.q 0).1, false) ∉ Γ)

/-- **The cut of a step**, read from `κ0(x)`: its side of `κ0(x)` holds `κ0(x_b)`. -/
def hiCut : R.WalkCut Γ :=
  WalkCut.ofWalk S.n S.q (L.κ0 S.x) (L.κ1 S.y) (L.hiA S.x S.y) (L.hiB S.x S.y) S.pos
    (L.bound_xy S.hxa S.hxb S.hya S.hyb) S.start S.walk S.stop S.simple S.simple_last
    (fun j _ => L.pair_iff _)
    (fun j h0 hj c hc => by
      have hin := S.inner j h0 hj
      simp only [hiA, List.mem_cons, List.mem_append, List.mem_reverse] at hc
      rcases hc with rfl | (hc | hc) | hc
      · exact L.not_fconnect_κ0 hin S.hxa S.hxb
      · obtain ⟨t, h1, h2, rfl⟩ := mem_cornerSeg.1 hc
        exact L.not_fconnect_κ0 hin (by have := S.hxa; omega) h2
      · exact noB j h0 hj c hc
      · obtain ⟨t, h1, h2, rfl⟩ := mem_cornerSeg.1 hc
        exact L.not_fconnect_κ1 hin (by have := S.hya; omega) h2)
    (L.hold_of_walk hR hC (c0 := L.κ0 S.x)
      ((L.mem_xy S.hxa S.hxb S.hya S.hyb).1 (List.mem_append_left _ List.mem_cons_self))
      S.start S.walk S.noP)
    hdeg

@[simp] theorem hiCut_n : (L.hiCut hR hC S noB hdeg).n = S.n := rfl
@[simp] theorem hiCut_q : (L.hiCut hR hC S noB hdeg).q = S.q := rfl
@[simp] theorem hiCut_ka : (L.hiCut hR hC S noB hdeg).ka = L.κ0 S.x := rfl
@[simp] theorem hiCut_kb : (L.hiCut hR hC S noB hdeg).kb = L.κ1 S.y := rfl
@[simp] theorem hiCut_A : (L.hiCut hR hC S noB hdeg).A = L.hiA S.x S.y := rfl
@[simp] theorem hiCut_B : (L.hiCut hR hC S noB hdeg).B = L.hiB S.x S.y := rfl

local notation "𝒲" => L.hiCut hR hC S noB hdeg

theorem hiCut_qSeg : (𝒲).qSeg 0 (𝒲).n = (List.range S.n).map S.q := by
  simp [WalkCut.qSeg, List.range_eq_range']

/-- The corners `κ1` of the side of `κ0(x_b)`: the part `r_n` of the vertex of `κ1(y)` at `y`. -/
def hiκ1 (t : ℕ) : D × Bool := if t = S.y then (𝒲).rc (S.n - 1) else L.κ1 t

theorem hi_boundary_eq :
    liveBoundary L.κ0 (L.hiκ1 hR hC S noB hdeg) S.x L.xb S.y L.yb (𝒲).rs.tail L.Lb =
      ((𝒲).ka :: (𝒲).A) ++ (𝒲).rs := by
  rw [(𝒲).rs_eq]
  unfold liveBoundary
  rw [cornerSeg_cons _ S.hxb, cornerSeg_cons _ S.hyb,
    cornerSeg_congr (f := L.hiκ1 hR hC S noB hdeg) (f' := L.κ1) (fun t h1 _ => by
      unfold hiκ1
      rw [ite_eq_right (by omega)])]
  simp [hiκ1, hiA, List.append_assoc]

variable (hg : ∀ x, g (R.rev x) = g x)

/-- **Claims 13 and 14 for the side of `κ0(x_b)`.** If the step avoids the corners of `L_b`, the side
of `κ0(x)` of its cut is a live annulus, with `x_a = x`, `y_a = y`, the part `r_n` of the vertex of
`κ1(y)` as its corner at `y`, and the corners `r_{n-1}, …, r_1` of the step as `L_a`. -/
def hi : C.Live g (𝒲).Γ' where
  xa := S.x
  xb := L.xb
  ya := S.y
  yb := L.yb
  κ0 := L.κ0
  κ1 := L.hiκ1 hR hC S noB hdeg
  La := (𝒲).rs.tail
  Lb := L.Lb
  le_x := S.hxb
  le_y := S.hyb
  xb_le := L.xb_le
  yb_le := L.yb_le
  sub := L.sub.trans (𝒲).subset_Γ'
  pair := (𝒲).pair_Γ' L.pair
  skel := ((𝒲).final hR hC L.skel).2.1
  bound := by
    rw [L.hi_boundary_eq hR hC S noB hdeg]
    exact (𝒲).boundary_hi hR hC L.skel
  piece0 := fun t h1 h2 => L.piece0 t (S.hxa.trans h1) h2
  piece1 := fun t h1 h2 => by
    by_cases ht : t = S.y
    · subst ht
      unfold hiκ1
      rw [ite_eq_left rfl]
      exact connect_trans (fconnect_of_split_subset L.sub ((𝒲).fconnect_rc_last hR hC L.skel))
        (L.piece1 _ S.hya h2)
    · unfold hiκ1
      rw [ite_eq_right ht]
      exact L.piece1 t (S.hya.trans h1) h2
  off := fun c hc t ht => by
    rcases List.mem_append.1 hc with hc | hc
    · exact L.off c (List.mem_append_left _ hc) t ht
    · obtain ⟨j, h0, hj, he⟩ := (𝒲).tail_rs_tail hc
      rw [he]
      exact S.inner j h0 hj t ht
  old := by
    rw [L.hi_boundary_eq hR hC S noB hdeg]
    exact (𝒲).old_hi hR hC L.skel (S := C.Γ)
      (fun d hd h1 h2 => L.old d hd ((L.mem_xy S.hxa S.hxb S.hya S.hyb).1 h1)
        ((L.mem_xy S.hxa S.hxb S.hya S.hyb).1 h2)) S.noP
  dist := fun t h1 h2 h3 h4 => by
    have hQ : ∀ p, (R.double.split Γ).IsWalk ((R.double.split Γ).tail (𝒲).ka) p
        ((R.double.split Γ).tail (𝒲).kb) →
        (((𝒲).qSeg 0 (𝒲).n).map (g ∘ Prod.fst)).sum ≤ (p.map (g ∘ Prod.fst)).sum := fun p hp => by
      rw [L.hiCut_qSeg hR hC S noB hdeg]
      exact S.short p hp
    have hfin : (((𝒲).qSeg 0 (𝒲).n).map (g ∘ Prod.fst)).sum ≠ ⊤ := by
      rw [L.hiCut_qSeg hR hC S noB hdeg]
      exact S.fin
    have hmem0 : L.κ0 t ∈ ((𝒲).ka :: (𝒲).A) ++ (𝒲).rs := by
      rw [← L.hi_boundary_eq hR hC S noB hdeg]
      unfold liveBoundary
      simp only [List.mem_append]
      exact Or.inl (Or.inl (Or.inl (mem_cornerSeg.2 ⟨t, h1, h3, rfl⟩)))
    have hmem1 : L.hiκ1 hR hC S noB hdeg t ∈ ((𝒲).ka :: (𝒲).A) ++ (𝒲).rs := by
      rw [← L.hi_boundary_eq hR hC S noB hdeg]
      unfold liveBoundary
      simp only [List.mem_append, List.mem_reverse]
      exact Or.inl (Or.inr (mem_cornerSeg.2 ⟨t, h2, h4, rfl⟩))
    rw [(𝒲).walkDist_hi hR hC L.skel g hQ hfin hg ((𝒲).gcomp_of_mem_hi hR hC L.skel hmem0)
      ((𝒲).gcomp_of_mem_hi hR hC L.skel hmem1)]
    by_cases ht : t = S.y
    · subst ht
      have e : (R.double.split Γ).tail (L.hiκ1 hR hC S noB hdeg S.y) =
          (R.double.split Γ).tail (L.κ1 S.y) := by
        unfold hiκ1
        rw [ite_eq_left rfl]
        exact ((R.double.split Γ).tail_eq_iff _ _).2 ((𝒲).fconnect_rc_last hR hC L.skel)
      rw [e]
      exact L.dist _ (S.hxa.trans h1) S.hya h3 h4
    · unfold hiκ1
      rw [ite_eq_right ht]
      exact L.dist t (S.hxa.trans h1) (S.hya.trans h2) h3 h4

end Hi

namespace Step

variable {L} (S : L.Step)

/-- The heads of distinct darts of a step lie at distinct vertices. -/
theorem rev_inj {a b : ℕ} (ha : a < S.n) (hb : b < S.n)
    (h : fconnect (R.double.split Γ).rot (R.double.rev (S.q a)) (R.double.rev (S.q b))) : a = b := by
  rcases Nat.lt_or_ge (a + 1) S.n with ha1 | ha1 <;> rcases Nat.lt_or_ge (b + 1) S.n with hb1 | hb1
  · have := S.simple (a + 1) (b + 1) ha1 hb1
      (connect_trans (fconnect_symm (S.walk a ha1)) (connect_trans h (S.walk b hb1)))
    omega
  · obtain rfl : b = S.n - 1 := by omega
    exact absurd (connect_trans (fconnect_symm (S.walk a ha1)) (connect_trans h S.stop))
      (S.simple_last (a + 1) ha1)
  · obtain rfl : a = S.n - 1 := by omega
    exact absurd (connect_trans (fconnect_symm (S.walk b hb1))
      (connect_trans (fconnect_symm h) S.stop)) (S.simple_last (b + 1) hb1)
  · omega

theorem κ0_ne_κ1 : L.κ0 S.x ≠ L.κ1 S.y := by
  obtain ⟨-, -, hn3⟩ := List.nodup_append.1 (L.bound_xy S.hxa S.hxb S.hya S.hyb).nodup
  exact hn3 _ List.mem_cons_self _ List.mem_cons_self

/-- The darts of the step read backwards. -/
def rq (j : ℕ) : D × Bool := R.double.rev (S.q (S.n - 1 - j))

/-- The tail of a dart of the step read backwards is the tail of the next dart of the step. -/
theorem tail_rq {j : ℕ} (h0 : 0 < j) (hj : j < S.n) : R.tail (S.rq j).1 = R.tail (S.q (S.n - j)).1 := by
  have := DiskChord.tail_fst (S.walk (S.n - 1 - j) (by omega))
  rwa [show S.n - 1 - j + 1 = S.n - j by omega] at this

theorem noP_rq {j : ℕ} (hj : j < S.n) : ((S.rq j).1, false) ∉ C.Γ := fun h => by
  have h1 := C.pair_Γ h
  have e : R.rev (S.rq j).1 = (S.q (S.n - 1 - j)).1 := R.rev_rev _
  rw [e] at h1
  exact S.noP (S.n - 1 - j) (by omega) h1

/-- The sum of the weights of the step read backwards. -/
theorem sum_rq (hg : ∀ x, g (R.rev x) = g x) :
    (((List.range S.n).map S.rq).map (g ∘ Prod.fst)).sum =
      (((List.range S.n).map S.q).map (g ∘ Prod.fst)).sum := by
  have e : (List.range S.n).map S.rq = ((List.range S.n).map (R.double.rev ∘ S.q)).reverse :=
    map_range_sub_eq_reverse (R.double.rev ∘ S.q) S.n
  rw [e, List.map_reverse, List.sum_reverse, List.map_map, List.map_map]
  congr 2
  funext j
  exact hg (S.q j).1

end Step

section Lo

variable (hR : R.Planar) (hC : R.Connected) (S : L.Step)
  (noA : ∀ j, 0 < j → j < S.n → ∀ c ∈ L.La, ¬ fconnect (R.double.split Γ).rot (S.q j) c)
  (hdeg : L.hiB S.x S.y ≠ [] ∨ 1 < S.n ∨ ((S.rq 0).1, false) ∉ Γ)

/-- **The cut of a step**, read from `κ1(y)` along the step backwards: its side of `κ1(y)` holds
`κ0(x_a)`. -/
def loCut : R.WalkCut Γ :=
  WalkCut.ofWalk S.n S.rq (L.κ1 S.y) (L.κ0 S.x) (L.hiB S.x S.y) (L.hiA S.x S.y) S.pos
    (L.bound_xy S.hxa S.hxb S.hya S.hyb).append_comm
    (by
      show fconnect _ (R.double.rev (S.q (S.n - 1 - 0))) _
      rw [Nat.sub_zero]
      exact S.stop)
    (fun j hj => by
      have h := S.walk (S.n - 1 - (j + 1)) (by omega)
      rw [show S.n - 1 - (j + 1) + 1 = S.n - 1 - j by omega] at h
      show fconnect _ (R.double.rev (R.double.rev (S.q (S.n - 1 - j))))
        (R.double.rev (S.q (S.n - 1 - (j + 1))))
      rw [R.double.rev_rev]
      exact fconnect_symm h)
    (by
      show fconnect _ (R.double.rev (R.double.rev (S.q (S.n - 1 - (S.n - 1))))) _
      rw [R.double.rev_rev, Nat.sub_self]
      exact S.start)
    (fun i j hi hj h => by
      have := S.rev_inj (a := S.n - 1 - i) (b := S.n - 1 - j) (by omega) (by omega) h
      omega)
    (fun i hi h => by
      rcases Nat.eq_zero_or_pos i with rfl | h0
      · have h1 : fconnect (R.double.split Γ).rot (R.double.rev (S.q (S.n - 1))) (L.κ0 S.x) := by
          simpa [Step.rq] using h
        exact S.κ0_ne_κ1 (R.double.eq_of_fconnect_split
          ((L.bound_xy S.hxa S.hxb S.hya S.hyb).sub _ (by simp))
          ((L.bound_xy S.hxa S.hxb S.hya S.hyb).sub _ (by simp))
          (connect_trans (fconnect_symm h1) S.stop))
      · have h1 := S.walk (S.n - 1 - i) (by omega)
        rw [show S.n - 1 - i + 1 = S.n - i by omega] at h1
        have := S.simple (S.n - i) 0 (by omega) S.pos
          (connect_trans (fconnect_symm h1) (connect_trans h (fconnect_symm S.start)))
        omega)
    (fun j _ => L.pair_iff _)
    (fun j h0 hj c hc => by
      have h1 := S.walk (S.n - 1 - j) (by omega)
      rw [show S.n - 1 - j + 1 = S.n - j by omega] at h1
      intro h
      have h2 : fconnect (R.double.split Γ).rot (S.q (S.n - j)) c :=
        connect_trans (fconnect_symm h1) h
      have hin := S.inner (S.n - j) (by omega) (by omega)
      simp only [hiB, List.mem_cons, List.mem_append, List.mem_reverse, List.mem_map,
        List.mem_range'_1] at hc
      rcases hc with rfl | (⟨t, ht, rfl⟩ | hc) | ⟨t, ht, rfl⟩
      · exact L.not_fconnect_κ1 hin S.hya S.hyb h2
      · exact L.not_fconnect_κ1 hin ht.1 (by have := S.hyb; omega) h2
      · exact noA (S.n - j) (by omega) (by omega) c hc h2
      · exact L.not_fconnect_κ0 hin ht.1 (by have := S.hxb; omega) h2)
    (L.hold_of_walk hR hC (c0 := L.κ1 S.y)
      ((L.mem_xy S.hxa S.hxb S.hya S.hyb).1 (List.mem_append_right _ List.mem_cons_self))
      (by
        show fconnect _ (R.double.rev (S.q (S.n - 1 - 0))) _
        rw [Nat.sub_zero]
        exact S.stop)
      (fun j hj => by
        have h := S.walk (S.n - 1 - (j + 1)) (by omega)
        rw [show S.n - 1 - (j + 1) + 1 = S.n - 1 - j by omega] at h
        show fconnect _ (R.double.rev (R.double.rev (S.q (S.n - 1 - j))))
          (R.double.rev (S.q (S.n - 1 - (j + 1))))
        rw [R.double.rev_rev]
        exact fconnect_symm h)
      (fun j hj => S.noP_rq hj))
    hdeg

@[simp] theorem loCut_n : (L.loCut hR hC S noA hdeg).n = S.n := rfl
@[simp] theorem loCut_q : (L.loCut hR hC S noA hdeg).q = S.rq := rfl
@[simp] theorem loCut_ka : (L.loCut hR hC S noA hdeg).ka = L.κ1 S.y := rfl
@[simp] theorem loCut_kb : (L.loCut hR hC S noA hdeg).kb = L.κ0 S.x := rfl
@[simp] theorem loCut_A : (L.loCut hR hC S noA hdeg).A = L.hiB S.x S.y := rfl
@[simp] theorem loCut_B : (L.loCut hR hC S noA hdeg).B = L.hiA S.x S.y := rfl

local notation "𝒱" => L.loCut hR hC S noA hdeg

theorem loCut_qSeg : (𝒱).qSeg 0 (𝒱).n = (List.range S.n).map S.rq := by
  simp [WalkCut.qSeg, List.range_eq_range']

/-- The corners `κ0` of the side of `κ0(x_a)`: the part `m_1` of the vertex of `κ0(x)` at `x`. -/
def loκ0 (t : ℕ) : D × Bool := if t = S.x then (𝒱).rc (S.n - 1) else L.κ0 t

/-- The two ways to read the boundary of the side of `κ0(x_a)`. -/
theorem lo_boundary_eq :
    liveBoundary (L.loκ0 hR hC S noA hdeg) L.κ1 L.xa S.x L.ya S.y L.La (𝒱).rs.tail =
      ((List.range' L.xa (S.x - L.xa)).map L.κ0 ++ (𝒱).rs) ++
        (L.κ1 S.y :: (((List.range' L.ya (S.y - L.ya)).map L.κ1).reverse ++ L.La)) := by
  rw [(𝒱).rs_eq]
  unfold liveBoundary
  rw [cornerSeg_split _ S.hxa le_rfl, cornerSeg_split _ S.hya le_rfl]
  have e0 : (List.range' L.xa (S.x - L.xa)).map (L.loκ0 hR hC S noA hdeg) =
      (List.range' L.xa (S.x - L.xa)).map L.κ0 := by
    refine List.map_congr_left fun t ht => ?_
    rw [List.mem_range'_1] at ht
    unfold loκ0
    rw [ite_eq_right (by omega)]
  rw [e0]
  simp [loκ0, cornerSeg, List.append_assoc]

theorem lo_rot : ((𝒱).ka :: (𝒱).A) ++ (𝒱).rs =
    (L.κ1 S.y :: (((List.range' L.ya (S.y - L.ya)).map L.κ1).reverse ++ L.La)) ++
      ((List.range' L.xa (S.x - L.xa)).map L.κ0 ++ (𝒱).rs) := by
  simp [hiB, List.append_assoc]

theorem mem_lo {c : D × Bool} :
    c ∈ liveBoundary (L.loκ0 hR hC S noA hdeg) L.κ1 L.xa S.x L.ya S.y L.La (𝒱).rs.tail ↔
      c ∈ ((𝒱).ka :: (𝒱).A) ++ (𝒱).rs := by
  rw [L.lo_boundary_eq hR hC S noA hdeg, L.lo_rot hR hC S noA hdeg]
  simp only [List.mem_append]
  tauto

variable (hg : ∀ x, g (R.rev x) = g x)

/-- **Claims 13 and 14 for the side of `κ0(x_a)`.** If the step avoids the corners of `L_a`, the
side of `κ1(y)` of its cut is a live annulus, with `x_b = x`, `y_b = y`, the part `m_1` of the
vertex of `κ0(x)` as its corner at `x`, and the corners `m_2, …, m_n` of the step as `L_b`. -/
def lo : C.Live g (𝒱).Γ' where
  xa := L.xa
  xb := S.x
  ya := L.ya
  yb := S.y
  κ0 := L.loκ0 hR hC S noA hdeg
  κ1 := L.κ1
  La := L.La
  Lb := (𝒱).rs.tail
  le_x := S.hxa
  le_y := S.hya
  xb_le := S.hxb.trans L.xb_le
  yb_le := S.hyb.trans L.yb_le
  sub := L.sub.trans (𝒱).subset_Γ'
  pair := (𝒱).pair_Γ' L.pair
  skel := ((𝒱).final hR hC L.skel).2.1
  bound := by
    rw [L.lo_boundary_eq hR hC S noA hdeg]
    have h := (𝒱).boundary_hi hR hC L.skel
    rw [L.lo_rot hR hC S noA hdeg] at h
    exact h.append_comm
  piece0 := fun t h1 h2 => by
    by_cases ht : t = S.x
    · subst ht
      unfold loκ0
      rw [ite_eq_left rfl]
      exact connect_trans (fconnect_of_split_subset L.sub ((𝒱).fconnect_rc_last hR hC L.skel))
        (L.piece0 _ S.hxa S.hxb)
    · unfold loκ0
      rw [ite_eq_right ht]
      exact L.piece0 t h1 (h2.trans S.hxb)
  piece1 := fun t h1 h2 => L.piece1 t h1 (h2.trans S.hyb)
  off := fun c hc t ht => by
    rcases List.mem_append.1 hc with hc | hc
    · obtain ⟨j, h0, hj, he⟩ := (𝒱).tail_rs_tail hc
      rw [he]
      replace hj : j < S.n := hj
      have e : R.tail ((𝒱).q j).1 = R.tail (S.q (S.n - j)).1 := S.tail_rq h0 hj
      rw [e]
      exact S.inner (S.n - j) (by omega) (by omega) t ht
    · exact L.off c (List.mem_append_right _ hc) t ht
  old := fun d hd h1 h2 => by
    rw [L.mem_lo hR hC S noA hdeg] at h1 h2
    have hmem : ∀ c, c ∈ ((𝒱).ka :: (𝒱).A) ++ ((𝒱).kb :: (𝒱).B) ↔
        c ∈ liveBoundary L.κ0 L.κ1 L.xa L.xb L.ya L.yb L.La L.Lb := fun c => by
      rw [← L.mem_xy S.hxa S.hxb S.hya S.hyb]
      simp only [loCut_ka, loCut_A, loCut_kb, loCut_B, List.mem_append]
      tauto
    exact (𝒱).old_hi hR hC L.skel (S := C.Γ)
      (fun d hd h1 h2 => L.old d hd ((hmem _).1 h1) ((hmem _).1 h2)) (fun j hj => S.noP_rq hj)
      d hd h1 h2
  dist := fun t h1 h2 h3 h4 => by
    have hg' : ∀ z, (g ∘ Prod.fst) ((R.double.split Γ).rev z) = (g ∘ Prod.fst) z :=
      fun z => hg z.1
    have hQ : ∀ p, (R.double.split Γ).IsWalk ((R.double.split Γ).tail (𝒱).ka) p
        ((R.double.split Γ).tail (𝒱).kb) →
        (((𝒱).qSeg 0 (𝒱).n).map (g ∘ Prod.fst)).sum ≤ (p.map (g ∘ Prod.fst)).sum := fun p hp => by
      rw [L.loCut_qSeg hR hC S noA hdeg, S.sum_rq hg]
      have := S.short _ hp.reverse
      rwa [sum_map_reverseCycle _ hg'] at this
    have hfin : (((𝒱).qSeg 0 (𝒱).n).map (g ∘ Prod.fst)).sum ≠ ⊤ := by
      rw [L.loCut_qSeg hR hC S noA hdeg, S.sum_rq hg]
      exact S.fin
    have hmem0 : L.loκ0 hR hC S noA hdeg t ∈ ((𝒱).ka :: (𝒱).A) ++ (𝒱).rs := by
      rw [← L.mem_lo hR hC S noA hdeg]
      unfold liveBoundary
      simp only [List.mem_append]
      exact Or.inl (Or.inl (Or.inl (mem_cornerSeg.2 ⟨t, h1, h3, rfl⟩)))
    have hmem1 : L.κ1 t ∈ ((𝒱).ka :: (𝒱).A) ++ (𝒱).rs := by
      rw [← L.mem_lo hR hC S noA hdeg]
      unfold liveBoundary
      simp only [List.mem_append, List.mem_reverse]
      exact Or.inl (Or.inr (mem_cornerSeg.2 ⟨t, h2, h4, rfl⟩))
    rw [(𝒱).walkDist_hi hR hC L.skel g hQ hfin hg ((𝒱).gcomp_of_mem_hi hR hC L.skel hmem0)
      ((𝒱).gcomp_of_mem_hi hR hC L.skel hmem1)]
    by_cases ht : t = S.x
    · subst ht
      have e : (R.double.split Γ).tail (L.loκ0 hR hC S noA hdeg S.x) =
          (R.double.split Γ).tail (L.κ0 S.x) := by
        unfold loκ0
        rw [ite_eq_left rfl]
        exact ((R.double.split Γ).tail_eq_iff _ _).2 ((𝒱).fconnect_rc_last hR hC L.skel)
      rw [e]
      exact L.dist _ S.hxa h2 S.hxb (h4.trans S.hyb)
    · unfold loκ0
      rw [ite_eq_right ht]
      exact L.dist t h1 h2 (h3.trans S.hxb) (h4.trans S.hyb)

end Lo

end Live

end CutPath

end RotSystem

end SsspFlow
