import Mathlib

/-!
# Boundary weight of the classes cut out of a rooted tree

A rooted tree on `V` is given by a root, a parent map and a depth that drops along every non-root
parent edge. The tree edge from `v ≠ root` to its parent has the side `sub v`, the set of vertices
below `v`. For a weight `w` and a threshold `k`, the vertex `v` is light if its side has weight
below `k` in `w`. Deleting the light tree edges leaves components, and `rep u` is the nearest vertex
on the path from `u` to the root that is the root or light, so the components are the fibres of
`rep`. For a Gomory-Hu tree of `w`, the weight of the side of a tree edge equals the tree weight of
that edge, and the components are the classes of pairs whose minimum cut is at least `k`.

* `iterate_depth`, `anc_iff`, `eq_root_of_iterate_eq`: walking up `depth u` steps reaches the root,
  ancestors are exactly iterated parents, and only the root lies on a cycle of the parent map.
* `rep_spec`: `rep u` is the first vertex on the way up from `u` that is the root or light.
* `sep`: if `rep x ≠ rep y`, then the side of `rep x` or of `rep y` is light and separates `x` from `y`.
* `crossing_eq`: `crossing` is the sum over the components of the weight of the ordered pairs leaving
  them.
* `crossing_le_light`, `boundary_le`: for symmetric `w` and `k ≥ 1`, the crossing weight is at most
  `2 (k - 1) (t - 1)`, where `t` is the number of components.
* `boundary_tight`: on two vertices joined by an edge of weight one, with `k = 2`, the bound is attained.
-/

namespace StCutClasses

/-- A rooted tree: every vertex other than the root has a parent of smaller depth. -/
structure RootedTree (V : Type*) where
  root : V
  par : V → V
  depth : V → ℕ
  par_root : par root = root
  depth_lt : ∀ v, v ≠ root → depth (par v) < depth v

namespace RootedTree

variable {V : Type*} [Fintype V] [DecidableEq V] (T : RootedTree V)

omit [Fintype V] [DecidableEq V] in
theorem iterate_root (i : ℕ) : T.par^[i] T.root = T.root :=
  Function.iterate_fixed T.par_root i

omit [Fintype V] in
theorem iterate_depth_aux (n : ℕ) : ∀ u, T.depth u ≤ n → T.par^[n] u = T.root := by
  induction n with
  | zero =>
    intro u hu
    show u = T.root
    by_contra h
    have := T.depth_lt u h
    omega
  | succ n ih =>
    intro u hu
    show T.par^[n] (T.par u) = T.root
    by_cases h : u = T.root
    · rw [h, T.par_root]
      exact T.iterate_root n
    · exact ih _ (by have := T.depth_lt u h; omega)

omit [Fintype V] in
theorem iterate_depth (u : V) : T.par^[T.depth u] u = T.root :=
  T.iterate_depth_aux _ u le_rfl

/-- `v` lies on the path from `u` to the root. -/
def Anc (v u : V) : Prop := ∃ j ∈ Finset.range (T.depth u + 1), T.par^[j] u = v

instance (v u : V) : Decidable (T.Anc v u) := by
  unfold Anc
  infer_instance

theorem anc_iff {v u : V} : T.Anc v u ↔ ∃ j, T.par^[j] u = v := by
  constructor
  · rintro ⟨j, -, hj⟩
    exact ⟨j, hj⟩
  · rintro ⟨j, hj⟩
    by_cases hjd : j ≤ T.depth u
    · exact ⟨j, Finset.mem_range.2 (by omega), hj⟩
    · refine ⟨T.depth u, Finset.mem_range.2 (by omega), ?_⟩
      obtain ⟨d, rfl⟩ : ∃ d, j = d + T.depth u := ⟨j - T.depth u, by omega⟩
      rw [← hj, Function.iterate_add_apply, T.iterate_depth, T.iterate_root]

omit [Fintype V] in
theorem depth_iterate_le (i : ℕ) : ∀ u, T.depth (T.par^[i] u) ≤ T.depth u := by
  induction i with
  | zero => intro u; exact le_rfl
  | succ i ih =>
    intro u
    show T.depth (T.par^[i] (T.par u)) ≤ T.depth u
    by_cases h : u = T.root
    · rw [h, T.par_root]
      exact ih _
    · exact (ih _).trans (T.depth_lt u h).le

omit [Fintype V] in
theorem eq_root_of_iterate_eq {c : ℕ} (hc : 0 < c) {v : V} (h : T.par^[c] v = v) :
    v = T.root := by
  by_contra hv
  obtain ⟨d, rfl⟩ : ∃ d, c = d + 1 := ⟨c - 1, by omega⟩
  have h2 : T.par^[d] (T.par v) = v := h
  have h1 := T.depth_iterate_le d (T.par v)
  rw [h2] at h1
  have := T.depth_lt v hv
  omega

/-- The side of the tree edge from `v` to its parent. -/
def sub (v : V) : Finset V := Finset.univ.filter (fun u => T.Anc v u)

theorem mem_sub_root (u : V) : u ∈ T.sub T.root :=
  Finset.mem_filter.2 ⟨Finset.mem_univ _, T.anc_iff.2 ⟨_, T.iterate_depth u⟩⟩

variable (w : V → V → ℕ) (k : ℕ)

/-- The weight of the ordered pairs leaving `S`. -/
def cutO (S : Finset V) : ℕ := ∑ x, ∑ y, if x ∈ S ∧ y ∉ S then w x y else 0

/-- A non-root vertex whose side has weight below `k`. -/
def Light (v : V) : Prop := v ≠ T.root ∧ cutO w (T.sub v) < k

instance : DecidablePred (T.Light w k) := fun v => by
  unfold Light
  infer_instance

/-- Walk up at most `n` steps until the root or a light vertex. -/
def repAux : ℕ → V → V
  | 0, u => u
  | n + 1, u => if u = T.root ∨ T.Light w k u then u else repAux n (T.par u)

/-- The first vertex on the way up from `u` that is the root or light. -/
def rep (u : V) : V := T.repAux w k (T.depth u) u

theorem repAux_spec (n : ℕ) : ∀ u, T.depth u ≤ n →
    ∃ j, T.par^[j] u = T.repAux w k n u ∧
      (T.repAux w k n u = T.root ∨ T.Light w k (T.repAux w k n u)) ∧
      ∀ i < j, T.par^[i] u ≠ T.root ∧ ¬ T.Light w k (T.par^[i] u) := by
  induction n with
  | zero =>
    intro u hu
    have hr : u = T.root := by
      by_contra h
      have := T.depth_lt u h
      omega
    exact ⟨0, rfl, Or.inl hr, fun i hi => absurd hi (Nat.not_lt_zero _)⟩
  | succ n ih =>
    intro u hu
    simp only [repAux]
    split_ifs with h
    · exact ⟨0, rfl, h, fun i hi => absurd hi (Nat.not_lt_zero _)⟩
    · simp only [not_or] at h
      obtain ⟨j, hj1, hj2, hj3⟩ := ih (T.par u) (by have := T.depth_lt u h.1; omega)
      refine ⟨j + 1, hj1, hj2, ?_⟩
      intro i hi
      cases i with
      | zero => exact h
      | succ i => exact hj3 i (by omega)

theorem rep_spec (u : V) :
    ∃ j, T.par^[j] u = T.rep w k u ∧ (T.rep w k u = T.root ∨ T.Light w k (T.rep w k u)) ∧
      ∀ i < j, T.par^[i] u ≠ T.root ∧ ¬ T.Light w k (T.par^[i] u) :=
  T.repAux_spec w k _ u le_rfl

theorem mem_sub_rep (u : V) : u ∈ T.sub (T.rep w k u) := by
  obtain ⟨j, hj, -, -⟩ := T.rep_spec w k u
  exact Finset.mem_filter.2 ⟨Finset.mem_univ _, T.anc_iff.2 ⟨j, hj⟩⟩

/-- If a vertex `par^[i] u` is the root or light, then `rep u` lies on the path from `u` to it. -/
theorem rep_below {u : V} {i : ℕ} (hi : T.par^[i] u = T.root ∨ T.Light w k (T.par^[i] u)) :
    ∃ c, T.par^[c] (T.rep w k u) = T.par^[i] u := by
  obtain ⟨j, hj1, -, hj3⟩ := T.rep_spec w k u
  have hji : j ≤ i := by
    by_contra hlt
    have := hj3 i (by omega)
    rcases hi with hi | hi
    · exact this.1 hi
    · exact this.2 hi
  refine ⟨i - j, ?_⟩
  rw [← hj1, ← Function.iterate_add_apply]
  congr 1
  omega

theorem sep {x y : V} (hxy : T.rep w k x ≠ T.rep w k y) :
    (T.Light w k (T.rep w k x) ∧ x ∈ T.sub (T.rep w k x) ∧ y ∉ T.sub (T.rep w k x)) ∨
    (T.Light w k (T.rep w k y) ∧ y ∈ T.sub (T.rep w k y) ∧ x ∉ T.sub (T.rep w k y)) := by
  obtain ⟨jx, hx1, hx2, -⟩ := T.rep_spec w k x
  obtain ⟨jy, hy1, hy2, -⟩ := T.rep_spec w k y
  by_cases hyx : y ∈ T.sub (T.rep w k x)
  · right
    obtain ⟨i, hi⟩ := T.anc_iff.1 (Finset.mem_filter.1 hyx).2
    obtain ⟨c1, hc1⟩ := T.rep_below w k (u := y) (i := i) (by rw [hi]; exact hx2)
    rw [hi] at hc1
    -- hc1 : par^[c1] (rep y) = rep x
    have hry : T.rep w k y ≠ T.root := by
      intro h
      rw [h, T.iterate_root] at hc1
      exact hxy (hc1.symm.trans h.symm)
    refine ⟨hy2.resolve_left hry, T.mem_sub_rep w k y, ?_⟩
    intro hxs
    obtain ⟨a, ha⟩ := T.anc_iff.1 (Finset.mem_filter.1 hxs).2
    obtain ⟨c2, hc2⟩ := T.rep_below w k (u := x) (i := a) (by rw [ha]; exact hy2)
    rw [ha] at hc2
    -- hc2 : par^[c2] (rep x) = rep y
    have hcyc : T.par^[c1 + c2] (T.rep w k x) = T.rep w k x := by
      rw [Function.iterate_add_apply, hc2, hc1]
    by_cases hc : c1 + c2 = 0
    · have : c2 = 0 := by omega
      rw [this] at hc2
      exact hxy hc2
    · have hr := T.eq_root_of_iterate_eq (by omega) hcyc
      rw [hr, T.iterate_root] at hc2
      exact hry hc2.symm
  · left
    refine ⟨?_, T.mem_sub_rep w k x, hyx⟩
    rcases hx2 with h | h
    · exact absurd (h ▸ T.mem_sub_root y) hyx
    · exact h

/-- The weight of the ordered pairs whose endpoints have different representatives. -/
def crossing : ℕ := ∑ x, ∑ y, if T.rep w k x ≠ T.rep w k y then w x y else 0

theorem crossing_eq : T.crossing w k = ∑ i ∈ Finset.univ.image (T.rep w k),
    ∑ x ∈ Finset.univ.filter (fun x => T.rep w k x = i),
      ∑ y, if T.rep w k y ≠ i then w x y else 0 := by
  rw [crossing, ← Finset.sum_fiberwise_of_maps_to (s := Finset.univ)
    (t := Finset.univ.image (T.rep w k)) (g := T.rep w k)
    (fun x _ => Finset.mem_image_of_mem _ (Finset.mem_univ x))]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun x hx => ?_
  rw [(Finset.mem_filter.1 hx).2]
  exact Finset.sum_congr rfl fun y _ => if_congr ne_comm rfl rfl

/-- The weight that the side of `v` separates, for the ordered pair `(x, y)`. -/
def sepW (x y v : V) : ℕ :=
  (if x ∈ T.sub v ∧ y ∉ T.sub v then w x y else 0) +
    (if x ∉ T.sub v ∧ y ∈ T.sub v then w x y else 0)

theorem cutO_swap (hw : ∀ x y, w x y = w y x) (S : Finset V) :
    (∑ x, ∑ y, if x ∉ S ∧ y ∈ S then w x y else 0) = cutO w S := by
  rw [Finset.sum_comm, cutO]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [hw b a]
  by_cases h1 : a ∈ S <;> by_cases h2 : b ∈ S <;> simp [h1, h2]

theorem crossing_le_light (hw : ∀ x y, w x y = w y x) :
    T.crossing w k ≤ ∑ v ∈ Finset.univ.filter (T.Light w k), 2 * cutO w (T.sub v) := by
  set L := Finset.univ.filter (T.Light w k)
  calc T.crossing w k ≤ ∑ x, ∑ y, ∑ v ∈ L, T.sepW w x y v := by
        refine Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ => ?_
        split_ifs with hxy
        · rcases T.sep w k hxy with ⟨hl, hx, hy⟩ | ⟨hl, hy, hx⟩
          · refine le_trans ?_ (Finset.single_le_sum (fun v _ => Nat.zero_le _)
              (Finset.mem_filter.2 ⟨Finset.mem_univ _, hl⟩))
            simp [sepW, hx, hy]
          · refine le_trans ?_ (Finset.single_le_sum (fun v _ => Nat.zero_le _)
              (Finset.mem_filter.2 ⟨Finset.mem_univ _, hl⟩))
            simp [sepW, hx, hy]
        · exact Nat.zero_le _
    _ = ∑ x, ∑ v ∈ L, ∑ y, T.sepW w x y v :=
        Finset.sum_congr rfl fun x _ => Finset.sum_comm
    _ = ∑ v ∈ L, ∑ x, ∑ y, T.sepW w x y v := Finset.sum_comm
    _ = ∑ v ∈ L, 2 * cutO w (T.sub v) := by
        refine Finset.sum_congr rfl fun v _ => ?_
        simp only [sepW, Finset.sum_add_distrib]
        rw [cutO_swap w hw]
        simp only [cutO]
        ring

theorem rep_root : T.rep w k T.root = T.root := by
  obtain ⟨j, hj, -, -⟩ := T.rep_spec w k T.root
  rw [← hj, T.iterate_root]

theorem rep_light {v : V} (hv : T.Light w k v) : T.rep w k v = v := by
  obtain ⟨j, hj, -, hj3⟩ := T.rep_spec w k v
  cases j with
  | zero => exact hj.symm
  | succ j => exact absurd hv (hj3 0 (by omega)).2

theorem image_rep :
    Finset.univ.image (T.rep w k) = insert T.root (Finset.univ.filter (T.Light w k)) := by
  ext v
  simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_filter]
  constructor
  · rintro ⟨u, rfl⟩
    exact (T.rep_spec w k u).choose_spec.2.1
  · rintro (rfl | hv)
    · exact ⟨T.root, T.rep_root w k⟩
    · exact ⟨v, T.rep_light w k hv⟩

/-- For symmetric weights, the components left after deleting the light tree edges have total
boundary weight at most `2 (k - 1) (t - 1)`, counted over ordered pairs, where `t` is their number. -/
theorem boundary_le (hw : ∀ x y, w x y = w y x) :
    T.crossing w k ≤ 2 * (k - 1) * ((Finset.univ.image (T.rep w k)).card - 1) := by
  have hcard : (Finset.univ.image (T.rep w k)).card - 1 =
      (Finset.univ.filter (T.Light w k)).card := by
    rw [T.image_rep w k, Finset.card_insert_of_notMem (fun h => (Finset.mem_filter.1 h).2.1 rfl)]
    omega
  rw [hcard]
  calc T.crossing w k ≤ ∑ v ∈ Finset.univ.filter (T.Light w k), 2 * cutO w (T.sub v) :=
        T.crossing_le_light w k hw
    _ ≤ ∑ _v ∈ Finset.univ.filter (T.Light w k), 2 * (k - 1) := by
        refine Finset.sum_le_sum fun v hv => ?_
        have := (Finset.mem_filter.1 hv).2.2
        omega
    _ = 2 * (k - 1) * (Finset.univ.filter (T.Light w k)).card := by
        rw [Finset.sum_const, smul_eq_mul, mul_comm]

end RootedTree

/-- The tree on two vertices with root `0`. -/
def twoTree : RootedTree (Fin 2) where
  root := 0
  par := fun _ => 0
  depth := fun v => v.val
  par_root := rfl
  depth_lt := by decide

/-- On two vertices joined by an edge of weight one, with `k = 2`, the vertex `1` is light, there
are two components, and the crossing weight `2` attains the bound `2 (k - 1) (t - 1)`. -/
theorem boundary_tight :
    twoTree.crossing (fun u v : Fin 2 => if u ≠ v then 1 else 0) 2 = 2 ∧
      (Finset.univ.image (twoTree.rep (fun u v : Fin 2 => if u ≠ v then 1 else 0) 2)).card = 2 := by
  decide

end StCutClasses
