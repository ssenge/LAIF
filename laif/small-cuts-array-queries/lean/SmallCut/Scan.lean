import SmallCut.Certificate

/-!
# The scan-first certificate with capped labels

The vertices are scanned in the order of an injective `pos : V → ℕ`. Write `cnt t y` for the number of
neighbours of `y` at positions below `t`. When `v` is scanned, the counter of an unscanned neighbour `w` is
`min k (cnt (pos v) w)`, and the edge `v w` goes into forest `cnt (pos v) w` (counted from 0) if this is below `k`.
So forest `i < k` is `scanF G pos i`. The scan rule is `hscan`: the scanned vertex has a label `min k (cnt t ·)`
at least that of every unscanned vertex.

* `exists_parent`: if `i < cnt T y`, some neighbour `u` of `y` below `T` has `cnt (pos u) y = i`.
* `scan_run`: within a stretch of the scan where every vertex has more than `i` earlier neighbours, all vertices
  are connected in forest `i`.
* `scan_hmax`: for `i < k`, an edge outside forests `0, …, i - 1` joins two vertices connected in forest `i`.
* `scan_parent_unique`: each vertex has at most one earlier neighbour in forest `i`, so forest `i` is a forest.
* `scan_certificate`: the union of forests `0, …, k - 1` keeps `min k c` of the `c` edges across every set.
* `sum_found_le`: at most `k · |V|` entries are found in total.
-/

open Classical

namespace SmallCut

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The number of neighbours of `y` at positions below `t`. -/
noncomputable def cnt (G : SimpleGraph V) (pos : V → ℕ) (t : ℕ) (y : V) : ℕ :=
  (Finset.univ.filter (fun u => G.Adj u y ∧ pos u < t)).card

/-- Forest `i` of the scan: edges `v w` with `pos v < pos w` and `cnt (pos v) w = i`. -/
noncomputable def scanF (G : SimpleGraph V) (pos : V → ℕ) (i : ℕ) : SimpleGraph V :=
  SimpleGraph.fromRel (fun v w => G.Adj v w ∧ pos v < pos w ∧ cnt G pos (pos v) w = i)

variable {G : SimpleGraph V} {pos : V → ℕ}

theorem cnt_mono {t t' : ℕ} (h : t ≤ t') (y : V) : cnt G pos t y ≤ cnt G pos t' y := by
  apply Finset.card_le_card
  intro u hu
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu ⊢
  exact ⟨hu.1, lt_of_lt_of_le hu.2 h⟩

theorem cnt_lt_of {u u' y : V} (hu : G.Adj u y) (h : pos u < pos u') :
    cnt G pos (pos u) y < cnt G pos (pos u') y := by
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset]
  · refine ⟨u, ?_, ?_⟩
    · simp [hu, h]
    · simp
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    exact ⟨hx.1, lt_trans hx.2 h⟩

/-- Discrete intermediate values: if `y` has more than `i` neighbours below `T`, one of them has exactly `i`
neighbours of `y` below it. -/
theorem exists_parent (hinj : Function.Injective pos) {i : ℕ} {y : V} :
    ∀ T, i < cnt G pos T y → ∃ u, G.Adj u y ∧ pos u < T ∧ cnt G pos (pos u) y = i := by
  intro T
  induction T with
  | zero => intro h; simp [cnt] at h
  | succ T ih =>
    intro h
    by_cases hT : i < cnt G pos T y
    · obtain ⟨u, h1, h2, h3⟩ := ih hT
      exact ⟨u, h1, by omega, h3⟩
    · push Not at hT
      have hlt : cnt G pos T y < cnt G pos (T + 1) y := by omega
      by_contra hno
      push Not at hno
      have hsub : (Finset.univ.filter (fun u => G.Adj u y ∧ pos u < T + 1)) ⊆
          (Finset.univ.filter (fun u => G.Adj u y ∧ pos u < T)) := by
        intro u hu
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu ⊢
        refine ⟨hu.1, ?_⟩
        rcases Nat.lt_succ_iff_lt_or_eq.1 hu.2 with h' | h'
        · exact h'
        · exfalso
          have hle : cnt G pos T y ≤ i := hT
          have hge : i < cnt G pos (T + 1) y := h
          -- the vertex at position `T` is the only new neighbour, so `cnt (T + 1) y ≤ cnt T y + 1`
          have hone : cnt G pos (T + 1) y ≤ cnt G pos T y + 1 := by
            unfold cnt
            calc (Finset.univ.filter (fun x => G.Adj x y ∧ pos x < T + 1)).card
                ≤ (Finset.univ.filter (fun x => G.Adj x y ∧ pos x < T) ∪ {u}).card := by
                  apply Finset.card_le_card
                  intro x hx
                  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union,
                    Finset.mem_singleton] at hx ⊢
                  rcases Nat.lt_succ_iff_lt_or_eq.1 hx.2 with hx' | hx'
                  · exact Or.inl ⟨hx.1, hx'⟩
                  · exact Or.inr (hinj (hx'.trans h'.symm))
              _ ≤ _ := Finset.card_union_le _ _
          have hcu : cnt G pos (pos u) y = i := by
            rw [h']; omega
          exact hno u hu.1 (by omega) hcu
      exact absurd (Finset.card_le_card hsub) (by unfold cnt at hlt; omega)

/-- **Runs.** If every vertex scanned after `x` up to `y` has more than `i` earlier neighbours, then `x` and `y` are
connected in forest `i`. -/
theorem scan_run (hinj : Function.Injective pos) (k i : ℕ) (hik : i < k)
    (hscan : ∀ x y, pos x < pos y → min k (cnt G pos (pos x) y) ≤ min k (cnt G pos (pos x) x)) :
    ∀ n x y, pos y = n → pos x < pos y →
      (∀ z, pos x < pos z → pos z ≤ pos y → i < cnt G pos (pos z) z) →
      (scanF G pos i).Reachable x y := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro x y hy hxy hrun
  obtain ⟨q, hqy, hq, hcq⟩ := exists_parent hinj (pos y) (hrun y hxy le_rfl)
  have hadj : (scanF G pos i).Adj q y := by
    rw [scanF, SimpleGraph.fromRel_adj]
    exact ⟨fun h => by rw [h] at hq; omega, Or.inl ⟨hqy, hq, hcq⟩⟩
  have hqrun : ∀ z, pos q < pos z → pos z ≤ pos y → i < cnt G pos (pos z) z := by
    intro z hz1 hz2
    rcases lt_or_eq_of_le hz2 with hz | hz
    · have h1 := hscan z y hz
      have h2 : i < cnt G pos (pos z) y := hcq ▸ cnt_lt_of hqy hz1
      have h3 : i + 1 ≤ min k (cnt G pos (pos z) y) := le_min (by omega) (by omega)
      have h4 := le_trans h3 h1
      exact lt_of_lt_of_le (Nat.lt_succ_self i) (le_trans h4 (min_le_right _ _))
    · rw [hinj hz]; exact hrun y hxy le_rfl
  rcases lt_trichotomy (pos x) (pos q) with h | h | h
  · have hr := ih (pos q) (by omega) x q rfl h
      (fun z hz1 hz2 => hrun z hz1 (by omega))
    exact hr.trans hadj.reachable
  · rw [hinj h]; exact hadj.reachable
  · have hr := ih (pos x) (by omega) q x rfl h
      (fun z hz1 hz2 => hqrun z hz1 (by omega))
    exact hr.symm.trans hadj.reachable

theorem scan_hmax_lt (hinj : Function.Injective pos) (k i : ℕ) (hik : i < k)
    (hscan : ∀ x y, pos x < pos y → min k (cnt G pos (pos x) y) ≤ min k (cnt G pos (pos x) x))
    (v w : V) (hvw : G.Adj v w) (hp : pos v < pos w)
    (hnot : ∀ j < i, ¬ (scanF G pos j).Adj v w) : (scanF G pos i).Reachable v w := by
  have hne : v ≠ w := G.ne_of_adj hvw
  rcases lt_trichotomy (cnt G pos (pos v) w) i with h | h | h
  · exfalso
    apply hnot _ h
    rw [scanF, SimpleGraph.fromRel_adj]
    exact ⟨hne, Or.inl ⟨hvw, hp, rfl⟩⟩
  · apply SimpleGraph.Adj.reachable
    rw [scanF, SimpleGraph.fromRel_adj]
    exact ⟨hne, Or.inl ⟨hvw, hp, h⟩⟩
  · obtain ⟨p, hpw, hpv, hcp⟩ := exists_parent hinj (pos v) h
    have hadj : (scanF G pos i).Adj p w := by
      rw [scanF, SimpleGraph.fromRel_adj]
      exact ⟨G.ne_of_adj hpw, Or.inl ⟨hpw, by omega, hcp⟩⟩
    have hr := scan_run hinj k i hik hscan (pos v) p v rfl hpv (by
      intro z hz1 hz2
      have h1 := hscan z w (by omega)
      have h2 : i < cnt G pos (pos z) w := hcp ▸ cnt_lt_of hpw hz1
      have h3 : i + 1 ≤ min k (cnt G pos (pos z) w) := le_min (by omega) (by omega)
      exact lt_of_lt_of_le (Nat.lt_succ_self i) (le_trans (le_trans h3 h1) (min_le_right _ _)))
    exact hr.symm.trans hadj.reachable

/-- **Lemma 4.** For `i < k`, an edge of `G` outside forests `0, …, i - 1` joins two vertices connected in
forest `i`. -/
theorem scan_hmax (hinj : Function.Injective pos) (k : ℕ)
    (hscan : ∀ x y, pos x < pos y → min k (cnt G pos (pos x) y) ≤ min k (cnt G pos (pos x) x)) :
    ∀ i < k, ∀ v w, G.Adj v w → (∀ j < i, ¬ (scanF G pos j).Adj v w) → (scanF G pos i).Reachable v w := by
  intro i hik v w hvw hnot
  have hne : pos v ≠ pos w := fun h => G.ne_of_adj hvw (hinj h)
  rcases lt_or_gt_of_ne hne with hp | hp
  · exact scan_hmax_lt hinj k i hik hscan v w hvw hp hnot
  · exact (scan_hmax_lt hinj k i hik hscan w v hvw.symm hp
      (fun j hj h => hnot j hj h.symm)).symm

theorem scan_adj_iff {i : ℕ} {v w : V} (hp : pos v < pos w) :
    (scanF G pos i).Adj v w ↔ G.Adj v w ∧ cnt G pos (pos v) w = i := by
  rw [scanF, SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨-, h | h⟩
    · exact ⟨h.1, h.2.2⟩
    · omega
  · rintro ⟨h1, h2⟩
    exact ⟨G.ne_of_adj h1, Or.inl ⟨h1, hp, h2⟩⟩

theorem scan_disj (hinj : Function.Injective pos) :
    ∀ i j, i ≠ j → ∀ u v, (scanF G pos i).Adj u v → ¬ (scanF G pos j).Adj u v := by
  intro i j hij u v hi hj
  have hne : pos u ≠ pos v := fun h => (scanF G pos i).ne_of_adj hi (hinj h)
  rcases lt_or_gt_of_ne hne with hp | hp
  · exact hij (((scan_adj_iff hp).1 hi).2.symm.trans ((scan_adj_iff hp).1 hj).2)
  · exact hij (((scan_adj_iff hp).1 hi.symm).2.symm.trans ((scan_adj_iff hp).1 hj.symm).2)

theorem scanF_le (i : ℕ) : scanF G pos i ≤ G := by
  intro v w h
  rw [scanF, SimpleGraph.fromRel_adj] at h
  rcases h.2 with h' | h'
  · exact h'.1
  · exact h'.1.symm

/-- Each vertex has at most one earlier neighbour in forest `i`. -/
theorem scan_parent_unique (hinj : Function.Injective pos) {i : ℕ} {u u' w : V} (hu : pos u < pos w)
    (hu' : pos u' < pos w) (h : (scanF G pos i).Adj u w) (h' : (scanF G pos i).Adj u' w) : u = u' := by
  have a := (scan_adj_iff hu).1 h
  have b := (scan_adj_iff hu').1 h'
  rcases lt_trichotomy (pos u) (pos u') with hl | hl | hl
  · have := cnt_lt_of (pos := pos) a.1 hl; omega
  · exact hinj hl
  · have := cnt_lt_of (pos := pos) b.1 hl; omega

/-- **Certificate of the scan.** -/
theorem scan_certificate (hinj : Function.Injective pos) (k : ℕ)
    (hscan : ∀ x y, pos x < pos y → min k (cnt G pos (pos x) y) ≤ min k (cnt G pos (pos x) x))
    (S : Finset V) :
    min k (cross G.Adj S).card ≤ (cross (fun u v => ∃ i < k, (scanF G pos i).Adj u v) S).card :=
  certificate G (scanF G pos) k (scan_disj hinj) (scan_hmax hinj k hscan) S

/-- At most `k` entries of all lists lead to a fixed `w` and are found. -/
theorem card_found_le (hinj : Function.Injective pos) (k : ℕ) (w : V) :
    (Finset.univ.filter (fun v => G.Adj v w ∧ pos v < pos w ∧ cnt G pos (pos v) w < k)).card ≤ k := by
  calc _ ≤ (Finset.range k).card := by
        apply Finset.card_le_card_of_injOn (fun v => cnt G pos (pos v) w)
        · intro v hv
          simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hv
          simpa using hv.2.2
        · intro v hv v' hv' heq
          simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hv hv'
          simp only at heq
          rcases lt_trichotomy (pos v) (pos v') with hl | hl | hl
          · have := cnt_lt_of (pos := pos) hv.1 hl; omega
          · exact hinj hl
          · have := cnt_lt_of (pos := pos) hv'.1 hl; omega
    _ = k := Finset.card_range k

/-- **Found entries.** In total at most `k · |V|` entries are found by the scan. -/
theorem sum_found_le (hinj : Function.Injective pos) (k : ℕ) :
    ∑ v, (Finset.univ.filter (fun w => G.Adj v w ∧ pos v < pos w ∧ cnt G pos (pos v) w < k)).card
      ≤ k * Fintype.card V := by
  have h : ∑ v, (Finset.univ.filter (fun w => G.Adj v w ∧ pos v < pos w ∧ cnt G pos (pos v) w < k)).card
      = ∑ w, (Finset.univ.filter (fun v => G.Adj v w ∧ pos v < pos w ∧ cnt G pos (pos v) w < k)).card := by
    simp only [Finset.card_filter]
    exact Finset.sum_comm
  rw [h]
  calc _ ≤ ∑ _w : V, k := Finset.sum_le_sum (fun w _ => card_found_le hinj k w)
    _ = k * Fintype.card V := by rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_comm]

end SmallCut
