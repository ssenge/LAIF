import SsspFlow.Chord

/-!
# Crossing and Monge on a disk-drawn map

`DiskDrawn R l`: the darts of `l` name corners of one face of a connected planar map, at pairwise
distinct vertices, in this cyclic order along the face.

* `DiskDrawn.crossing`: for `a, b, c, d` in this cyclic order, a walk between the tails of `a` and `c`
  and a walk between the tails of `b` and `d` share a vertex, in each of the four orientations. The
  proof adds a chord from corner `a` to corner `c`. A simple path along the first walk together with
  the chord is a ring, and the two parts of the split face lie on its two sides.
* `DiskDrawn.monge`: the condition (M) for distances in `ℝ≥0∞` over walks with dart weights.
* `triangle_diskDrawn`: the statements are not vacuous.
-/

set_option autoImplicit false

namespace SsspFlow

open FourColor
open scoped ENNReal

namespace RotSystem

variable {D : Type*} [Fintype D] [DecidableEq D] {R : RotSystem D} {l : List D}

/-- The darts of `l` name corners of one face of a connected planar map, at pairwise distinct
vertices, in this cyclic order along the face. -/
structure DiskDrawn (R : RotSystem D) (l : List D) : Prop where
  /-- The map is planar. -/
  planar : R.Planar
  /-- The map is connected. -/
  connected : R.Connected
  /-- The corners lie at pairwise distinct vertices. -/
  tails_nodup : (l.map R.tail).Nodup
  /-- Along the face, each corner is followed by the next one, cyclically. -/
  order : firstReturn R.facePerm l.toFinset = l.formPerm

theorem DiskDrawn.nodup (h : R.DiskDrawn l) : l.Nodup :=
  List.Nodup.of_map _ h.tails_nodup

theorem DiskDrawn.one_face (h : R.DiskDrawn l) {x y : D} (hx : x ∈ l) (hy : y ∈ l) :
    fconnect R.facePerm x y := by
  have hc := h.nodup.isCycleOn_formPerm.2 (show x ∈ {a | a ∈ l} from hx)
    (show y ∈ {a | a ∈ l} from hy)
  rw [← fconnect_firstReturn_iff R.facePerm (List.mem_toFinset.2 hx) (List.mem_toFinset.2 hy),
    h.order]
  exact (sameCycle_iff_fconnect _).1 hc

theorem DiskDrawn.rotate (h : R.DiskDrawn l) (n : ℕ) : R.DiskDrawn (l.rotate n) where
  planar := h.planar
  connected := h.connected
  tails_nodup := by
    rw [List.map_rotate]
    exact List.nodup_rotate.2 h.tails_nodup
  order := by
    have hS : (l.rotate n).toFinset = l.toFinset := by
      ext x
      simp
    rw [hS, List.formPerm_rotate l h.nodup n, h.order]

/-! ### Distances over walks -/

/-- The distance from `u` to `v` for dart weights `g`: the infimum over walks, `⊤` without a walk. -/
noncomputable def walkDist (R : RotSystem D) (g : D → ℝ≥0∞) (u v : R.Vertex) : ℝ≥0∞ :=
  ⨅ (p : List D) (_ : R.IsWalk u p v), (p.map g).sum

theorem walkDist_le (g : D → ℝ≥0∞) {u v : R.Vertex} {p : List D} (hp : R.IsWalk u p v) :
    R.walkDist g u v ≤ (p.map g).sum :=
  iInf₂_le p hp

theorem walkDist_self (g : D → ℝ≥0∞) (u : R.Vertex) : R.walkDist g u u = 0 :=
  le_antisymm (walkDist_le g (p := []) rfl) zero_le

/-- A lower bound for a sum of two distances from all pairs of walks. -/
private theorem le_walkDist_add {g : D → ℝ≥0∞} {a : ℝ≥0∞} {u v w z : R.Vertex}
    (h : ∀ p q, R.IsWalk u p v → R.IsWalk w q z → a ≤ (p.map g).sum + (q.map g).sum) :
    a ≤ R.walkDist g u v + R.walkDist g w z := by
  simp only [walkDist, ENNReal.iInf_add, ENNReal.add_iInf]
  exact le_iInf₂ fun q hq => le_iInf₂ fun p hp => h p q hp hq

theorem walkDist_triangle (g : D → ℝ≥0∞) (u v t : R.Vertex) :
    R.walkDist g u t ≤ R.walkDist g u v + R.walkDist g v t :=
  le_walkDist_add fun p q hp hq =>
    (walkDist_le g (hp.append hq)).trans_eq (by rw [List.map_append, List.sum_append])

/-- Splitting a walk at a list boundary. -/
theorem isWalk_append_iff {u v : R.Vertex} {p q : List D} :
    R.IsWalk u (p ++ q) v ↔ ∃ t, R.IsWalk u p t ∧ R.IsWalk t q v := by
  constructor
  · induction p generalizing u with
    | nil => exact fun h => ⟨u, rfl, h⟩
    | cons x p ih =>
      rintro ⟨hx, hw⟩
      obtain ⟨t, h1, h2⟩ := ih hw
      exact ⟨t, ⟨hx, h1⟩, h2⟩
  · rintro ⟨t, h1, h2⟩
    exact h1.append h2

/-- The reversal of a walk is a walk. -/
theorem IsWalk.reverse {u v : R.Vertex} {p : List D} (hp : R.IsWalk u p v) :
    R.IsWalk v (R.reverseCycle p) u := by
  induction p generalizing u with
  | nil => exact (show u = v from hp).symm
  | cons x p ih =>
    obtain ⟨rfl, hw⟩ := hp
    have he : R.reverseCycle (x :: p) = R.reverseCycle p ++ [R.rev x] := by
      simp [reverseCycle]
    rw [he]
    exact (ih hw).append ⟨rfl, R.head_rev x⟩

/-- Every walk contains a simple path with the same ends, and the path visits only vertices of the
walk. -/
theorem IsWalk.exists_simple {u v : R.Vertex} {p : List D} (hp : R.IsWalk u p v) :
    ∃ q, R.IsWalk u q v ∧ (q.map R.tail).Nodup ∧ (∀ x ∈ q, R.tail x ≠ v) ∧ q.Sublist p := by
  induction p generalizing u with
  | nil => exact ⟨[], hp, List.nodup_nil, by simp, List.Sublist.refl _⟩
  | cons x p ih =>
    obtain ⟨rfl, hw⟩ := hp
    obtain ⟨q, hq, hnd, hne, hsub⟩ := ih hw
    by_cases hv : R.tail x = v
    · exact ⟨[], hv, List.nodup_nil, by simp, List.nil_sublist _⟩
    by_cases hm : ∃ y ∈ q, R.tail y = R.tail x
    · obtain ⟨y, hy, hxy⟩ := hm
      obtain ⟨s, t, rfl⟩ := List.append_of_mem hy
      obtain ⟨m, -, h2⟩ := isWalk_append_iff.1 hq
      refine ⟨y :: t, ⟨hxy, h2.2⟩, ?_, fun z hz => hne z (by simp [List.mem_append, hz]), ?_⟩
      · rw [List.map_append] at hnd
        exact (List.nodup_append.1 hnd).2.1
      · exact ((List.sublist_append_right s (y :: t)).trans hsub).cons x
    · refine ⟨x :: q, ⟨rfl, hq⟩, ?_, ?_, hsub.cons_cons x⟩
      · rw [List.map_cons, List.nodup_cons]
        refine ⟨fun hmem => ?_, hnd⟩
        obtain ⟨y, hy, hxy⟩ := List.mem_map.1 hmem
        exact hm ⟨y, hy, hxy⟩
      · intro z hz
        rcases List.mem_cons.1 hz with rfl | hz
        · exact hv
        · exact hne z hz

/-! ### Splitting a walk at a vertex -/

/-- The walk `p` from `u` to `v` splits at the vertex `t`. -/
private def Splits (R : RotSystem D) (u : R.Vertex) (p : List D) (v t : R.Vertex) : Prop :=
  ∃ p₁ p₂, p = p₁ ++ p₂ ∧ R.IsWalk u p₁ t ∧ R.IsWalk t p₂ v

/-- A walk splits at the tail of each of its darts. -/
private theorem splits_of_mem {u v : R.Vertex} {p : List D} (hp : R.IsWalk u p v) {x : D}
    (hx : x ∈ p) : Splits R u p v (R.tail x) := by
  obtain ⟨s, t, rfl⟩ := List.append_of_mem hx
  obtain ⟨m, h1, h2⟩ := isWalk_append_iff.1 hp
  obtain rfl : R.tail x = m := h2.1
  exact ⟨s, x :: t, rfl, h1, h2⟩

/-- A walk splits at its last vertex. -/
private theorem splits_end {u v : R.Vertex} {p : List D} (hp : R.IsWalk u p v) :
    Splits R u p v v :=
  ⟨p, [], (List.append_nil p).symm, hp, rfl⟩

/-- A walk splits at its first vertex. -/
private theorem splits_start {u v : R.Vertex} {p : List D} (hp : R.IsWalk u p v) :
    Splits R u p v u :=
  ⟨[], p, rfl, rfl, hp⟩

/-- A split of the reversal is a split of the walk. -/
private theorem Splits.of_reverse {u v t : R.Vertex} {p : List D}
    (h : Splits R v (R.reverseCycle p) u t) : Splits R u p v t := by
  obtain ⟨q₁, q₂, he, h1, h2⟩ := h
  refine ⟨R.reverseCycle q₂, R.reverseCycle q₁, ?_, h2.reverse, h1.reverse⟩
  have hcat : R.reverseCycle (q₁ ++ q₂) = R.reverseCycle q₂ ++ R.reverseCycle q₁ := by
    simp [reverseCycle]
  rw [← hcat, ← he, reverseCycle_reverseCycle]

/-! ### The order along the face -/

/-- From the entry `i` of `l` the orbit of `f` reaches the entry `i + m`, and up to there it meets
only entries with an index from `i + 1` to `i + m`. -/
private theorem orbit_segment {f : Equiv.Perm D} (hn : l.Nodup)
    (ho : firstReturn f l.toFinset = l.formPerm) (i m : ℕ) (hm : i + m < l.length) :
    ∃ n, (⇑f)^[n] l[i] = l[i + m] ∧ ∀ j, 0 < j → j ≤ n → ∀ e (he : e < l.length),
      (⇑f)^[j] l[i] = l[e] → i < e ∧ e ≤ i + m := by
  induction m with
  | zero => exact ⟨0, rfl, fun j hj hj' => absurd hj' (by omega)⟩
  | succ m ih =>
    obtain ⟨n, hn1, hn2⟩ := ih (by omega)
    have hlt : i + m + 1 < l.length := by omega
    have hmem : l[i + m] ∈ l.toFinset := List.mem_toFinset.2 (List.getElem_mem _)
    obtain ⟨k, hk, hkv, -, hkj⟩ := firstReturn_spec f hmem
    have hstep : (⇑f)^[k] l[i + m] = l[i + m + 1] := by
      rw [← hkv, ho, List.formPerm_apply_lt_getElem _ hn _ hlt]
    refine ⟨k + n, ?_, ?_⟩
    · rw [Function.iterate_add_apply, hn1, hstep]
      rfl
    · intro j hj hjn e he hje
      by_cases hjle : j ≤ n
      · have := hn2 j hj hjle e he hje
        omega
      · obtain ⟨j', rfl⟩ : ∃ j', j = j' + n := ⟨j - n, by omega⟩
        rw [Function.iterate_add_apply, hn1] at hje
        rcases (show j' < k ∨ j' = k by omega) with hlt' | rfl
        · refine absurd ?_ (hkj j' (by omega) hlt')
          rw [hje]
          exact List.mem_toFinset.2 (List.getElem_mem _)
        · rw [hstep] at hje
          have hi := (List.Nodup.getElem_inj_iff hn).1 hje
          omega

/-- The orbit of `f` from entry `i` to entry `k` avoids the entries off that part of `l`. -/
private theorem orbit_between {f : Equiv.Perm D} (hn : l.Nodup)
    (ho : firstReturn f l.toFinset = l.formPerm) {i k s₁ s₂ : ℕ} (hi : i < k)
    (hk : k < l.length) (hs₁ : s₁ < l.length) (hs₂ : s₂ < l.length) (h₁ : s₁ ≤ i ∨ k < s₁)
    (h₂ : s₂ ≤ i ∨ k < s₂) :
    ∃ n, (⇑f)^[n] l[i] = l[k] ∧
      ∀ j, 0 < j → j ≤ n → (⇑f)^[j] l[i] ≠ l[s₁] ∧ (⇑f)^[j] l[i] ≠ l[s₂] := by
  obtain ⟨m, rfl⟩ : ∃ m, k = i + m := ⟨k - i, by omega⟩
  obtain ⟨n, hn1, hn2⟩ := orbit_segment hn ho i m hk
  refine ⟨n, hn1, fun j hj hjn => ⟨fun he => ?_, fun he => ?_⟩⟩
  · have := hn2 j hj hjn s₁ hs₁ he
    omega
  · have := hn2 j hj hjn s₂ hs₂ he
    omega

omit [Fintype D] [DecidableEq D] in
/-- The indices of four entries of a sublist. -/
private theorem exists_indices {a b c d : D} (hl : [a, b, c, d].Sublist l) :
    ∃ (i₀ i₁ i₂ i₃ : ℕ) (h₀ : i₀ < l.length) (h₁ : i₁ < l.length) (h₂ : i₂ < l.length)
      (h₃ : i₃ < l.length), l[i₀] = a ∧ l[i₁] = b ∧ l[i₂] = c ∧ l[i₃] = d ∧ i₀ < i₁ ∧ i₁ < i₂ ∧
        i₂ < i₃ := by
  obtain ⟨f, hf⟩ := List.sublist_iff_exists_fin_orderEmbedding_get_eq.1 hl
  have hlt : ∀ i j : Fin ([a, b, c, d] : List D).length, i < j → (f i : ℕ) < f j :=
    fun i j hij => f.strictMono hij
  refine ⟨f ⟨0, by simp⟩, f ⟨1, by simp⟩, f ⟨2, by simp⟩, f ⟨3, by simp⟩, (f _).2, (f _).2,
    (f _).2, (f _).2, (hf ⟨0, by simp⟩).symm, (hf ⟨1, by simp⟩).symm, (hf ⟨2, by simp⟩).symm,
    (hf ⟨3, by simp⟩).symm, hlt _ _ (by simp), hlt _ _ (by simp), hlt _ _ (by simp)⟩

/-! ### The ring of a chord -/

section Base

variable {D' : Type*} [Fintype D'] [DecidableEq D'] {M : RotSystem D'}

/-- The disk of a ring is a union of face orbits. -/
private theorem mem_diskN_of_fconnect {c : List D'} {x y : D'} (h : fconnect M.facePerm x y) :
    x ∈ M.dualMap.diskN c ↔ y ∈ M.dualMap.diskN c := by
  induction h with
  | refl => exact Iff.rfl
  | tail _ hbc ih =>
    rw [ih, ← hbc]
    exact (M.face_mem_diskN_iff _).symm

/-- A simple path from the head of `e` to the tail of `e`, with the dart `e`, is a ring. -/
private theorem isRing_concat {e : D'} {s : List D'} (hs : M.IsWalk (M.head e) s (M.tail e))
    (hn : (s.map M.tail).Nodup) (hne : ∀ x ∈ s, M.tail x ≠ M.tail e) : M.IsRing (s ++ [e]) := by
  refine ⟨(cycle_rotate_one e s).2 ?_, ?_⟩
  · exact ((M.isWalk_tail_iff e (s ++ [e]) (M.head e)).1 ⟨rfl, hs.append ⟨rfl, rfl⟩⟩).1
  · rw [List.map_append]
    refine List.nodup_append.2 ⟨hn, by simp, fun a ha b hb => ?_⟩
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 ha
    obtain rfl : b = M.tail e := by simpa using hb
    exact hne x hx

/-- A dart map that respects `rev` and tails carries walks to walks. -/
private theorem isWalk_map {ι : D → D'} (hrev : ∀ x, M.rev (ι x) = ι (R.rev x))
    (htail : ∀ x y, M.tail (ι x) = M.tail (ι y) ↔ R.tail x = R.tail y) {s : List D} {x y : D}
    (h : R.IsWalk (R.tail x) s (R.tail y)) :
    M.IsWalk (M.tail (ι x)) (s.map ι) (M.tail (ι y)) := by
  induction s generalizing x with
  | nil => exact (htail x y).2 h
  | cons z s ih =>
    refine ⟨(htail z x).2 h.1, ?_⟩
    have hw := ih (x := R.rev z) h.2
    show M.IsWalk (M.tail (M.rev (ι z))) (s.map ι) (M.tail (ι y))
    rw [hrev]
    exact hw

/-- **Separation by the ring of a chord.** Let `κ` be a dart of a planar map `M` from the vertex of
`a` to the vertex of `c`, off the image of `R`. A simple path `q` from `a` to `c` closes up with
`rev κ` to a ring. The face orbit of `rev κ` lies in the disk of the ring, and the face orbit of
`κ` lies outside. So a walk from the first orbit to the second meets the ring. -/
private theorem crossing_base {ι : D → D'} (hM : M.Planar)
    (hrev : ∀ x, M.rev (ι x) = ι (R.rev x))
    (htail : ∀ x y, M.tail (ι x) = M.tail (ι y) ↔ R.tail x = R.tail y) {κ : D'}
    (hκ : ∀ x, ι x ≠ κ) {a b c d : D} (hκa : M.tail κ = M.tail (ι a))
    (hκc : M.tail (M.rev κ) = M.tail (ι c)) (hb : fconnect M.facePerm (M.rev κ) (ι b))
    (hd : fconnect M.facePerm κ (ι d)) {q r : List D} (hq : R.IsWalk (R.tail a) q (R.tail c))
    (hqn : (q.map R.tail).Nodup) (hqc : ∀ x ∈ q, R.tail x ≠ R.tail c)
    (hr : R.IsWalk (R.tail b) r (R.tail d)) :
    ∃ t, (t = R.tail c ∨ ∃ x ∈ q, R.tail x = t) ∧
      (t = R.tail b ∨ t = R.tail d ∨ ∃ y ∈ r, R.tail y = t) := by
  have hρ : M.IsRing (q.map ι ++ [M.rev κ]) := by
    refine isRing_concat ?_ ?_ ?_
    · have hh : M.head (M.rev κ) = M.tail (ι a) := (M.head_rev κ).trans hκa
      rw [hh, hκc]
      exact isWalk_map hrev htail hq
    · rw [List.map_map, List.Nodup, List.pairwise_map]
      rw [List.Nodup, List.pairwise_map] at hqn
      exact hqn.imp fun hne heq => hne ((htail _ _).1 heq)
    · intro x hx
      obtain ⟨x', hx', rfl⟩ := List.mem_map.1 hx
      rw [hκc]
      exact fun he => hqc x' hx' ((htail _ _).1 he)
  have hrκ : M.rev κ ∈ q.map ι ++ [M.rev κ] := by simp
  have hκρ : κ ∉ q.map ι ++ [M.rev κ] := by
    intro hm
    rcases List.mem_append.1 hm with hm | hm
    · obtain ⟨x, -, hx⟩ := List.mem_map.1 hm
      exact hκ x hx
    · exact M.rev_ne κ (List.mem_singleton.1 hm).symm
  have hbin : ι b ∈ M.dualMap.diskN (q.map ι ++ [M.rev κ]) :=
    (mem_diskN_of_fconnect hb).1 (M.dualMap.mem_diskN_of_mem _ hrκ)
  have hκout : κ ∈ M.outside (q.map ι ++ [M.rev κ]) := by
    have hh := M.rev_cycle_mem_outside hM hρ hrκ (by rwa [M.rev_rev])
    rwa [M.rev_rev] at hh
  have hdout : ι d ∈ M.outside (q.map ι ++ [M.rev κ]) :=
    fun hd' => hκout ((mem_diskN_of_fconnect hd).2 hd')
  have hOn : ∀ y : D, M.OnCycle (q.map ι ++ [M.rev κ]) (M.tail (ι y)) →
      R.tail y = R.tail c ∨ ∃ x ∈ q, R.tail x = R.tail y := by
    rintro y ⟨e, he, hey⟩
    rcases List.mem_append.1 he with he | he
    · obtain ⟨x, hx, rfl⟩ := List.mem_map.1 he
      exact Or.inr ⟨x, hx, (htail _ _).1 hey⟩
    · obtain rfl : e = M.rev κ := List.mem_singleton.1 he
      exact Or.inl ((htail _ _).1 (hκc.symm.trans hey)).symm
  by_cases hbρ : M.OnCycle (q.map ι ++ [M.rev κ]) (M.tail (ι b))
  · exact ⟨R.tail b, hOn b hbρ, Or.inl rfl⟩
  by_cases hdρ : M.OnCycle (q.map ι ++ [M.rev κ]) (M.tail (ι d))
  · exact ⟨R.tail d, hOn d hdρ, Or.inr (Or.inl rfl)⟩
  have hI : M.InsideVertex (q.map ι ++ [M.rev κ]) (M.tail (ι b)) :=
    ⟨hbρ, ι b, rfl, hbin, fun hm => hbρ ⟨ι b, hm, rfl⟩⟩
  have hO : M.OutsideVertex (q.map ι ++ [M.rev κ]) (M.tail (ι d)) := ⟨hdρ, ι d, rfl, hdout⟩
  obtain ⟨y, hy, hyρ⟩ := M.isWalk_meets_cycle hM hρ (isWalk_map hrev htail hr) hI hO
  obtain ⟨y', hy', rfl⟩ := List.mem_map.1 hy
  exact ⟨R.tail y', hOn y' hyρ, Or.inr (Or.inr ⟨y', hy', rfl⟩)⟩

end Base

/-- The face permutation of the lift on the darts of the map. -/
private theorem lift_facePerm_iterate (k n : ℕ) (x : D) :
    (⇑(R.lift k).facePerm)^[n] (Sum.inl x) = Sum.inl ((⇑R.facePerm)^[n] x) := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
    exact ih _

/-- The chord from corner `a` to corner `c` in the lift separates the part of the face from `a` up
to `c` from the part from `c` up to `a`. -/
private theorem crossing_lift (hR : R.Planar) {a b c d : D} (hac : a ≠ c)
    (hface : fconnect R.facePerm a c)
    (hA : ∃ n, (⇑R.facePerm)^[n] a = b ∧
      ∀ j, 0 < j → j ≤ n → (⇑R.facePerm)^[j] a ≠ a ∧ (⇑R.facePerm)^[j] a ≠ c)
    (hB : ∃ n, (⇑R.facePerm)^[n] c = d ∧
      ∀ j, 0 < j → j ≤ n → (⇑R.facePerm)^[j] c ≠ a ∧ (⇑R.facePerm)^[j] c ≠ c)
    {q r : List D} (hq : R.IsWalk (R.tail a) q (R.tail c)) (hqn : (q.map R.tail).Nodup)
    (hqc : ∀ x ∈ q, R.tail x ≠ R.tail c) (hr : R.IsWalk (R.tail b) r (R.tail d)) :
    ∃ t, (t = R.tail c ∨ ∃ x ∈ q, R.tail x = t) ∧
      (t = R.tail b ∨ t = R.tail d ∨ ∃ y ∈ r, R.tail y = t) := by
  have hiso : (R.lift 1).IsolatedEdge (Sum.inr (0, true)) := lift_isolatedEdge 1 _
  have hoff : ∀ x : D, (R.lift 1).Off (Sum.inr (0, true)) (Sum.inl x) := fun x =>
    ⟨Sum.inl_ne_inr, Sum.inl_ne_inr⟩
  have hne : (Sum.inl a : D ⊕ Fin 1 × Bool) ≠ Sum.inl c := fun he => hac (Sum.inl_injective he)
  have hM : ((R.lift 1).chord (Sum.inr (0, true)) (Sum.inl a) (Sum.inl c)).Planar :=
    planar_chord ((planar_lift 1).2 hR) hiso (hoff a) (hoff c)
      ((fconnect_lift_face_iff 1 a c).2 hface)
  obtain ⟨n₁, rfl, hj₁⟩ := hA
  obtain ⟨n₂, rfl, hj₂⟩ := hB
  refine crossing_base (M := (R.lift 1).chord (Sum.inr (0, true)) (Sum.inl a) (Sum.inl c))
    (ι := Sum.inl) (κ := Sum.inr (0, true)) hM (fun _ => rfl)
    (fun x y => (tail_chord_iff hiso (hoff a) (hoff c) (hoff x) (hoff y)).trans
      (tail_lift_iff 1 x y))
    (fun _ => Sum.inl_ne_inr) (tail_chord_c hiso (hoff a) (hoff c))
    (tail_chord_rev hiso (hoff a) (hoff c)) ?_ ?_ hq hqn hqc hr
  · refine connect_trans (fconnect_chord_rev_left hiso (hoff a) (hoff c) hne) ?_
    have hh := fconnect_chord_left hiso (hoff a) (hoff c) n₁ (fun j hj hjn => by
      rw [lift_facePerm_iterate]
      exact ⟨fun he => (hj₁ j hj hjn).1 (Sum.inl_injective he),
        fun he => (hj₁ j hj hjn).2 (Sum.inl_injective he)⟩)
    rwa [lift_facePerm_iterate] at hh
  · refine connect_trans (fconnect_chord_c_right hiso (hoff a) (hoff c)) ?_
    have hh := fconnect_chord_right hiso (hoff a) (hoff c) n₂ (fun j hj hjn => by
      rw [lift_facePerm_iterate]
      exact ⟨fun he => (hj₂ j hj hjn).1 (Sum.inl_injective he),
        fun he => (hj₂ j hj hjn).2 (Sum.inl_injective he)⟩)
    rwa [lift_facePerm_iterate] at hh

/-! ### Crossing -/

/-- The base form of the crossing: the two walks split at a common vertex. -/
private theorem DiskDrawn.crossing_core (h : R.DiskDrawn l) {a b c d : D}
    (hl : [a, b, c, d].Sublist l) {p r : List D} (hp : R.IsWalk (R.tail a) p (R.tail c))
    (hr : R.IsWalk (R.tail b) r (R.tail d)) :
    ∃ t, Splits R (R.tail a) p (R.tail c) t ∧ Splits R (R.tail b) r (R.tail d) t := by
  obtain ⟨q, hq, hqn, hqc, hqs⟩ := hp.exists_simple
  have hA := exists_indices hl
  obtain ⟨i₀, i₁, i₂, i₃, h₀, h₁, h₂, h₃, rfl, rfl, rfl, rfl, h01, h12, h23⟩ := hA
  have hac : l[i₀] ≠ l[i₂] := fun he => by
    have := (List.Nodup.getElem_inj_iff h.nodup).1 he
    omega
  obtain ⟨t, ht1, ht2⟩ := crossing_lift h.planar hac
    (h.one_face (List.getElem_mem _) (List.getElem_mem _))
    (orbit_between h.nodup h.order h01 h₁ h₀ h₂ (Or.inl le_rfl) (Or.inr h12))
    (orbit_between h.nodup h.order h23 h₃ h₀ h₂ (Or.inl (by omega)) (Or.inl le_rfl))
    hq hqn hqc hr
  refine ⟨t, ?_, ?_⟩
  · rcases ht1 with rfl | ⟨x, hx, rfl⟩
    · exact splits_end hp
    · exact splits_of_mem hp (hqs.subset hx)
  · rcases ht2 with rfl | rfl | ⟨y, hy, rfl⟩
    · exact splits_start hr
    · exact splits_end hr
    · exact splits_of_mem hr hy

/-- **Crossing.** For corners `a, b, c, d` in this cyclic order, a walk between the tails of `a` and
`c` and a walk between the tails of `b` and `d` share a vertex, and both split there. -/
theorem DiskDrawn.crossing (h : R.DiskDrawn l) {a b c d u v w z : D} (hl : [a, b, c, d].Sublist l)
    (huv : (u = a ∧ v = c) ∨ (u = c ∧ v = a)) (hwz : (w = b ∧ z = d) ∨ (w = d ∧ z = b))
    {p r : List D} (hp : R.IsWalk (R.tail u) p (R.tail v)) (hr : R.IsWalk (R.tail w) r (R.tail z)) :
    ∃ t p₁ p₂ r₁ r₂, p = p₁ ++ p₂ ∧ r = r₁ ++ r₂ ∧ R.IsWalk (R.tail u) p₁ t ∧
      R.IsWalk t p₂ (R.tail v) ∧ R.IsWalk (R.tail w) r₁ t ∧ R.IsWalk t r₂ (R.tail z) := by
  have key : ∃ t, Splits R (R.tail u) p (R.tail v) t ∧ Splits R (R.tail w) r (R.tail z) t := by
    rcases huv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases hwz with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact h.crossing_core hl hp hr
    · obtain ⟨t, h1, h2⟩ := h.crossing_core hl hp hr.reverse
      exact ⟨t, h1, h2.of_reverse⟩
    · obtain ⟨t, h1, h2⟩ := h.crossing_core hl hp.reverse hr
      exact ⟨t, h1.of_reverse, h2⟩
    · obtain ⟨t, h1, h2⟩ := h.crossing_core hl hp.reverse hr.reverse
      exact ⟨t, h1.of_reverse, h2.of_reverse⟩
  obtain ⟨t, ⟨p₁, p₂, hp', h1, h2⟩, r₁, r₂, hr', h3, h4⟩ := key
  exact ⟨t, p₁, p₂, r₁, r₂, hp', hr', h1, h2, h3, h4⟩

/-- **Monge**, the condition (M), in each of the four orientations. -/
theorem DiskDrawn.monge (h : R.DiskDrawn l) (g : D → ℝ≥0∞) {a b c d u v w z : D}
    (hl : [a, b, c, d].Sublist l) (huv : (u = a ∧ v = c) ∨ (u = c ∧ v = a))
    (hwz : (w = b ∧ z = d) ∨ (w = d ∧ z = b)) :
    R.walkDist g (R.tail u) (R.tail z) + R.walkDist g (R.tail w) (R.tail v) ≤
      R.walkDist g (R.tail u) (R.tail v) + R.walkDist g (R.tail w) (R.tail z) := by
  refine le_walkDist_add fun P Q hP hQ => ?_
  obtain ⟨t, P₁, P₂, Q₁, Q₂, rfl, rfl, h1, h2, h3, h4⟩ := h.crossing hl huv hwz hP hQ
  calc R.walkDist g (R.tail u) (R.tail z) + R.walkDist g (R.tail w) (R.tail v)
      ≤ ((P₁ ++ Q₂).map g).sum + ((Q₁ ++ P₂).map g).sum :=
        add_le_add (walkDist_le g (h1.append h4)) (walkDist_le g (h3.append h2))
    _ = ((P₁ ++ P₂).map g).sum + ((Q₁ ++ Q₂).map g).sum := by
        simp only [List.map_append, List.sum_append]
        abel

/-! ### An example -/

/-- The vertices of `triangle`, as labels of its darts. -/
private def triangleVertexLabel : Fin 10 → Fin 5 := ![0, 1, 1, 2, 2, 0, 0, 3, 0, 4]

private theorem triangle_label_of_tail {x y : Fin 10} (h : triangle.tail x = triangle.tail y) :
    triangleVertexLabel x = triangleVertexLabel y := by
  have hstep : ∀ z : Fin 10, triangleVertexLabel (triangle.toHypermap.node z) =
      triangleVertexLabel z := by decide
  have hc := (triangle.tail_eq_iff x y).1 h
  clear h
  induction hc with
  | refl => rfl
  | tail _ hbc ih => rw [ih, ← hbc, hstep]

/-- Four corners along one face of `triangle`. -/
theorem triangle_diskDrawn : triangle.DiskDrawn [0, 2, 4, 7] where
  planar := triangle_planar
  connected := triangle_connected
  tails_nodup := by
    have hinj : ∀ x ∈ ([0, 2, 4, 7] : List (Fin 10)), ∀ y ∈ ([0, 2, 4, 7] : List (Fin 10)),
        triangleVertexLabel x = triangleVertexLabel y → x = y := by decide
    exact List.Nodup.map_on (fun x hx y hy he => hinj x hx y hy (triangle_label_of_tail he))
      (by decide)
  order := by
    have h0 : triangle.facePerm 0 = 2 := by decide
    have h2 : triangle.facePerm 2 = 4 := by decide
    have h4 : triangle.facePerm 4 = 6 := by decide
    have h6 : triangle.facePerm 6 = 7 := by decide
    have h7 : triangle.facePerm 7 = 0 := by decide
    have hcases : ∀ x : Fin 10, x ∈ ([0, 2, 4, 7] : List (Fin 10)).toFinset →
        x = 0 ∨ x = 2 ∨ x = 4 ∨ x = 7 := by decide
    ext x
    by_cases hx : x ∈ ([0, 2, 4, 7] : List (Fin 10)).toFinset
    · rcases hcases x hx with rfl | rfl | rfl | rfl
      · rw [show ([0, 2, 4, 7] : List (Fin 10)).formPerm 0 = 2 by decide]
        refine congrArg _ (firstReturn_eq_of_trail _ hx ?_)
        rw [h0]
        exact Trail.here (by decide)
      · rw [show ([0, 2, 4, 7] : List (Fin 10)).formPerm 2 = 4 by decide]
        refine congrArg _ (firstReturn_eq_of_trail _ hx ?_)
        rw [h2]
        exact Trail.here (by decide)
      · rw [show ([0, 2, 4, 7] : List (Fin 10)).formPerm 4 = 7 by decide]
        refine congrArg _ (firstReturn_eq_of_trail _ hx ?_)
        rw [h4]
        refine Trail.step (by decide) ?_
        rw [h6]
        exact Trail.here (by decide)
      · rw [show ([0, 2, 4, 7] : List (Fin 10)).formPerm 7 = 0 by decide]
        refine congrArg _ (firstReturn_eq_of_trail _ hx ?_)
        rw [h7]
        exact Trail.here (by decide)
    · rw [firstReturn_of_not_mem _ hx, List.formPerm_apply_of_notMem]
      simpa using hx

end RotSystem

end SsspFlow
