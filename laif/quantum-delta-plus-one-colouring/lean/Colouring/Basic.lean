import Mathlib

/-!
# Quantum (Δ + 1)-colouring by palette sparsification: the combinatorial steps

* `proper_of_conflict`: a colouring from the lists that is proper on the conflict edges is proper on
  the whole graph.
* `count_containing`, `pair_bound`: two independent uniform lists of ℓ colours from {0, …, Δ} share
  a colour for at most a fraction ℓ²/(Δ + 1) of the pairs of lists.
* `vertex_cost`, `total_cost`: the search cost per vertex and in total.
* `min_sq_le`, `balance`: the minimum of the two totals is at most n^{5/4} L^{3/2}.
-/

namespace Colouring

open Finset

/-- A colouring χ with χ(v) ∈ L(v) that is proper on every edge whose endpoints have intersecting
lists is proper on every edge. -/
theorem proper_of_conflict {V : Type*} (adj : V → V → Prop) (L : V → Finset ℕ) (χ : V → ℕ)
    (hχ : ∀ v, χ v ∈ L v) (hH : ∀ u v, adj u v → (L u ∩ L v).Nonempty → χ u ≠ χ v) :
    ∀ u v, adj u v → χ u ≠ χ v := by
  intro u v huv heq
  have hv : χ u ∈ L v := by rw [heq]; exact hχ v
  exact hH u v huv ⟨χ u, mem_inter.mpr ⟨hχ u, hv⟩⟩ heq

/-- The (l + 1)-subsets of T that contain a fixed c ∈ T are counted by C(|T| − 1, l). -/
theorem count_containing {T : Finset ℕ} {c : ℕ} (hc : c ∈ T) (l : ℕ) :
    ((T.powersetCard (l + 1)).filter (fun A => c ∈ A)).card = (T.card - 1).choose l := by
  have hT : T = insert c (T.erase c) := (insert_erase hc).symm
  have hnot : c ∉ T.erase c := notMem_erase c T
  have h1 : (powersetCard (l + 1) (T.erase c)).filter (fun A => c ∈ A) = ∅ := by
    apply filter_eq_empty_iff.mpr
    intro A hA hcA
    exact hnot ((mem_powersetCard.mp hA).1 hcA)
  have h2 : ((powersetCard l (T.erase c)).image (insert c)).filter (fun A => c ∈ A) =
      (powersetCard l (T.erase c)).image (insert c) := by
    apply filter_true_of_mem
    intro A hA
    obtain ⟨B, -, rfl⟩ := mem_image.mp hA
    exact mem_insert_self c B
  have hinj : Set.InjOn (insert c) (↑(powersetCard l (T.erase c)) : Set (Finset ℕ)) := by
    intro B hB B' hB' h
    have hcB : c ∉ B := fun h' => hnot ((mem_powersetCard.mp (mem_coe.mp hB)).1 h')
    have hcB' : c ∉ B' := fun h' => hnot ((mem_powersetCard.mp (mem_coe.mp hB')).1 h')
    rw [← erase_insert hcB, ← erase_insert hcB']
    exact congrArg (fun A => A.erase c) h
  have e : powersetCard (l + 1) (insert c (T.erase c)) =
      powersetCard (l + 1) (T.erase c) ∪ (powersetCard l (T.erase c)).image (insert c) :=
    powersetCard_succ_insert hnot l
  conv_lhs => rw [hT, e, filter_union, h1, h2, empty_union]
  rw [card_image_of_injOn hinj, card_powersetCard, card_erase_of_mem hc]

/-- **Pair bound.** Among the pairs of (l + 1)-subsets of {0, …, D}, those that intersect make up at
most a fraction (l + 1)²/(D + 1). -/
theorem pair_bound (D l : ℕ) :
    (((range (D + 1)).powersetCard (l + 1) ×ˢ (range (D + 1)).powersetCard (l + 1)).filter
        (fun p => (p.1 ∩ p.2).Nonempty)).card * (D + 1) ≤
      (l + 1) ^ 2 * ((D + 1).choose (l + 1)) ^ 2 := by
  set P := (range (D + 1)).powersetCard (l + 1) with hP
  set B := (range (D + 1)).biUnion
    (fun c => P.filter (fun A => c ∈ A) ×ˢ P.filter (fun A => c ∈ A)) with hB
  have hsub : (P ×ˢ P).filter (fun p => (p.1 ∩ p.2).Nonempty) ⊆ B := by
    intro p hp
    rw [mem_filter, mem_product] at hp
    obtain ⟨⟨h1, h2⟩, c, hc⟩ := hp
    rw [mem_inter] at hc
    rw [hB, mem_biUnion]
    refine ⟨c, (mem_powersetCard.mp h1).1 hc.1, ?_⟩
    rw [mem_product, mem_filter, mem_filter]
    exact ⟨⟨h1, hc.1⟩, h2, hc.2⟩
  have hcount : ∀ c ∈ range (D + 1),
      (P.filter (fun A => c ∈ A) ×ˢ P.filter (fun A => c ∈ A)).card = (D.choose l) ^ 2 := by
    intro c hc
    rw [card_product, hP, count_containing hc, card_range, Nat.add_sub_cancel, sq]
  have hBcard : B.card ≤ (D + 1) * (D.choose l) ^ 2 := by
    calc B.card ≤ ∑ c ∈ range (D + 1),
          (P.filter (fun A => c ∈ A) ×ˢ P.filter (fun A => c ∈ A)).card := card_biUnion_le
      _ = (D + 1) * (D.choose l) ^ 2 := by
        rw [sum_congr rfl hcount, sum_const, card_range, smul_eq_mul]
  calc ((P ×ˢ P).filter (fun p => (p.1 ∩ p.2).Nonempty)).card * (D + 1)
      ≤ B.card * (D + 1) := Nat.mul_le_mul_right _ (card_le_card hsub)
    _ ≤ (D + 1) * (D.choose l) ^ 2 * (D + 1) := Nat.mul_le_mul_right _ hBcard
    _ = ((D + 1) * D.choose l) ^ 2 := by ring
    _ = (l + 1) ^ 2 * ((D + 1).choose (l + 1)) ^ 2 := by rw [Nat.add_one_mul_choose_eq]; ring

/-- The cost of one vertex: a search over N ≤ M items that finds t ≤ T marked ones and certifies
that none is left costs √(N(t + 1)) + √N L ≤ √M (√(T + 1) + L). -/
theorem vertex_cost (N M t T L : ℝ) (hN : 0 ≤ N) (hNM : N ≤ M) (ht : 0 ≤ t) (htT : t ≤ T)
    (hL : 0 ≤ L) :
    Real.sqrt (N * (t + 1)) + Real.sqrt N * L ≤ Real.sqrt M * (Real.sqrt (T + 1) + L) := by
  have hM : 0 ≤ M := le_trans hN hNM
  have h1 : Real.sqrt (N * (t + 1)) ≤ Real.sqrt M * Real.sqrt (T + 1) := by
    rw [← Real.sqrt_mul hM]
    exact Real.sqrt_le_sqrt (by nlinarith)
  have h2 : Real.sqrt N * L ≤ Real.sqrt M * L :=
    mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hNM) hL
  rw [mul_add (Real.sqrt M)]
  linarith

/-- Summed over the vertices. -/
theorem total_cost {V : Type*} (s : Finset V) (N t : V → ℝ) (M T L : ℝ) (hN : ∀ v, 0 ≤ N v)
    (hNM : ∀ v, N v ≤ M) (ht : ∀ v, 0 ≤ t v) (htT : ∀ v, t v ≤ T) (hL : 0 ≤ L) :
    ∑ v ∈ s, (Real.sqrt (N v * (t v + 1)) + Real.sqrt (N v) * L) ≤
      s.card * (Real.sqrt M * (Real.sqrt (T + 1) + L)) := by
  have h := Finset.sum_le_card_nsmul s
    (fun v => Real.sqrt (N v * (t v + 1)) + Real.sqrt (N v) * L)
    (Real.sqrt M * (Real.sqrt (T + 1) + L))
    (fun v _ => vertex_cost (N v) M (t v) T L (hN v) (hNM v) (ht v) (htT v) hL)
  simpa [nsmul_eq_mul] using h

theorem min_sq_le (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) : (min a b) ^ 2 ≤ a * b := by
  rcases le_total a b with h | h
  · rw [min_eq_left h]; nlinarith
  · rw [min_eq_right h]; nlinarith

/-- **Balance.** The minimum of n √Δ L and n √n L² / √Δ is at most n^{5/4} L^{3/2}, stated for the
squares: its square is at most n² √n L³. -/
theorem balance (n Δ L : ℝ) (hn : 0 ≤ n) (hΔ : 0 < Δ) (hL : 0 ≤ L) :
    (min (n * Real.sqrt Δ * L) (n * Real.sqrt n / Real.sqrt Δ * L ^ 2)) ^ 2 ≤
      n ^ 2 * Real.sqrt n * L ^ 3 := by
  have hs : 0 < Real.sqrt Δ := Real.sqrt_pos.mpr hΔ
  have hsn : 0 ≤ Real.sqrt n := Real.sqrt_nonneg n
  have hs' := hs.ne'
  calc (min (n * Real.sqrt Δ * L) (n * Real.sqrt n / Real.sqrt Δ * L ^ 2)) ^ 2
      ≤ (n * Real.sqrt Δ * L) * (n * Real.sqrt n / Real.sqrt Δ * L ^ 2) :=
        min_sq_le _ _ (by positivity) (by positivity)
    _ = n ^ 2 * Real.sqrt n * L ^ 3 := by field_simp <;> ring

end Colouring
