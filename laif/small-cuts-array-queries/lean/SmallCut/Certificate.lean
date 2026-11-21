import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Forest certificates for small cuts

Let `F 0, F 1, …` be edge-disjoint subgraphs of `G` such that every edge of `G` that lies in none of
`F 0, …, F (i - 1)` joins two vertices that are connected in `F i`. This holds when `F i` is a maximal
spanning forest of `G` minus the edges of `F 0, …, F (i - 1)`. The union `H` of `F 0, …, F (k - 1)` keeps
`min k c` of the `c` edges of `G` across every vertex set `S`.

* `cross R S`: the ordered pairs `(u, v)` with `u ∈ S`, `v ∉ S` and `R u v`, one per edge across `S`.
* `cross_of_reachable`: a connected pair across `S` gives an edge across `S`.
* `certificate`: `min k |δ_G(S)| ≤ |δ_H(S)|`.
* `certificate_eq`: if `|δ_H(S)| < k`, then `|δ_G(S)| = |δ_H(S)|`.
* `star_bound_end`, `star_bound_merge`: the two cases of the degree bound for the stars of the first phase.
* `sum_sqrt_le`: `∑ √(a_C² + b_C) ≤ ∑ a_C + √(m ∑ b_C)` for `m` terms, the sum behind the cost of a round.
-/

open Classical

namespace SmallCut

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The ordered pairs `(u, v)` with `u ∈ S`, `v ∉ S` and `R u v`. -/
noncomputable def cross (R : V → V → Prop) (S : Finset V) : Finset (V × V) :=
  (S ×ˢ Sᶜ).filter (fun p => R p.1 p.2)

theorem mem_cross {R : V → V → Prop} {S : Finset V} {p : V × V} :
    p ∈ cross R S ↔ p.1 ∈ S ∧ p.2 ∉ S ∧ R p.1 p.2 := by
  simp [cross, and_assoc]

theorem cross_mono {R R' : V → V → Prop} (h : ∀ u v, R u v → R' u v) (S : Finset V) :
    cross R S ⊆ cross R' S := by
  intro p hp
  rw [mem_cross] at hp ⊢
  exact ⟨hp.1, hp.2.1, h _ _ hp.2.2⟩

/-- A pair across `S` that is connected in `F` gives an edge of `F` across `S`. -/
theorem cross_of_reachable {F : SimpleGraph V} {S : Finset V} {u v : V}
    (h : F.Reachable u v) (hu : u ∈ S) (hv : v ∉ S) : ∃ q, q ∈ cross F.Adj S := by
  obtain ⟨w⟩ := h
  obtain ⟨d, -, h1, h2⟩ := w.exists_boundary_dart (S : Set V) (by simpa using hu) (by simpa using hv)
  exact ⟨(d.fst, d.snd), mem_cross.2 ⟨by simpa using h1, by simpa using h2, d.adj⟩⟩

/-- **Certificate.** If the `F i` are edge-disjoint and every edge of `G` outside `F 0, …, F (i - 1)` joins two
vertices connected in `F i`, then the union of `F 0, …, F (k - 1)` has at least `min k c` edges across `S`, where
`c` is the number of edges of `G` across `S`. -/
theorem certificate (G : SimpleGraph V) (F : ℕ → SimpleGraph V) (k : ℕ)
    (hdisj : ∀ i j, i ≠ j → ∀ u v, (F i).Adj u v → ¬ (F j).Adj u v)
    (hmax : ∀ i u v, G.Adj u v → (∀ j < i, ¬ (F j).Adj u v) → (F i).Reachable u v)
    (S : Finset V) :
    min k (cross G.Adj S).card ≤ (cross (fun u v => ∃ i < k, (F i).Adj u v) S).card := by
  by_cases hall : ∀ i < k, ∃ p ∈ cross G.Adj S, ∀ j < i, ¬ (F j).Adj p.1 p.2
  · have hq : ∀ i, i < k → ∃ q, q ∈ cross (F i).Adj S := by
      intro i hi
      obtain ⟨p, hp, hnot⟩ := hall i hi
      rw [mem_cross] at hp
      exact cross_of_reachable (hmax i p.1 p.2 hp.2.2 hnot) hp.1 hp.2.1
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · simp
    have : Nonempty (V × V) := ⟨(hq 0 hk0).choose⟩
    choose! q hq using hq
    have hinj : Set.InjOn q (Finset.range k) := by
      intro i hi j hj hij
      by_contra hne
      have hi' := mem_cross.1 (hq i (Finset.mem_range.1 hi))
      have hj' := mem_cross.1 (hq j (Finset.mem_range.1 hj))
      rw [hij] at hi'
      exact hdisj i j hne _ _ hi'.2.2 hj'.2.2
    have hsub : (Finset.range k).image q ⊆ cross (fun u v => ∃ i < k, (F i).Adj u v) S := by
      intro p hp
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hp
      have h := mem_cross.1 (hq i (Finset.mem_range.1 hi))
      exact mem_cross.2 ⟨h.1, h.2.1, i, Finset.mem_range.1 hi, h.2.2⟩
    calc min k (cross G.Adj S).card ≤ k := min_le_left _ _
      _ = ((Finset.range k).image q).card := by rw [Finset.card_image_of_injOn hinj, Finset.card_range]
      _ ≤ _ := Finset.card_le_card hsub
  · push Not at hall
    obtain ⟨i, hi, hno⟩ := hall
    have hsub : cross G.Adj S ⊆ cross (fun u v => ∃ i < k, (F i).Adj u v) S := by
      intro p hp
      obtain ⟨j, hj, hadj⟩ := hno p hp
      have h := mem_cross.1 hp
      exact mem_cross.2 ⟨h.1, h.2.1, j, lt_trans hj hi, hadj⟩
    exact le_trans (min_le_right _ _) (Finset.card_le_card hsub)

/-- **Small cuts are exact.** If moreover every `F i` is a subgraph of `G` and the union of
`F 0, …, F (k - 1)` has fewer than `k` edges across `S`, then `G` has the same number of edges across `S`. -/
theorem certificate_eq (G : SimpleGraph V) (F : ℕ → SimpleGraph V) (k : ℕ) (hle : ∀ i, F i ≤ G)
    (hdisj : ∀ i j, i ≠ j → ∀ u v, (F i).Adj u v → ¬ (F j).Adj u v)
    (hmax : ∀ i u v, G.Adj u v → (∀ j < i, ¬ (F j).Adj u v) → (F i).Reachable u v)
    (S : Finset V) (hsmall : (cross (fun u v => ∃ i < k, (F i).Adj u v) S).card < k) :
    (cross G.Adj S).card = (cross (fun u v => ∃ i < k, (F i).Adj u v) S).card := by
  have h1 := certificate G F k hdisj hmax S
  have h2 : (cross (fun u v => ∃ i < k, (F i).Adj u v) S).card ≤ (cross G.Adj S).card :=
    Finset.card_le_card (cross_mono (fun u v ⟨i, _, h⟩ => hle i h) S)
  have h3 : (cross G.Adj S).card ≤ (cross (fun u v => ∃ i < k, (F i).Adj u v) S).card := by
    rcases le_total k (cross G.Adj S).card with hk | hk
    · rw [min_eq_left hk] at h1; omega
    · rwa [min_eq_right hk] at h1
  omega

/-- **Degree bound, a star that ends its list.** A star of a vertex of residual degree `d` with all its `d`
neighbours, each of residual degree at most `d`, has total residual degree below `(d + 1)²`. -/
theorem star_bound_end (d s : ℕ) (hs : s ≤ d + d * d) : s < (d + 1) ^ 2 := by nlinarith

/-- **Degree bound, a star that joins a component.** If a component of `a` vertices has total residual degree at
most `a²`, and a star of `b ≥ 1` vertices of residual degree at most `d ≤ a` joins it, the result has total
residual degree below `(a + b)²`. -/
theorem star_bound_merge (a b d s t : ℕ) (hb : 0 < b) (hda : d ≤ a) (hs : s ≤ a ^ 2)
    (ht : t ≤ b * d) : s + t < (a + b) ^ 2 := by nlinarith

/-- **The sum behind the cost of a round.** For `m` components with sizes `a_C` and extra list lengths `b_C`,
`∑ √(a_C² + b_C) ≤ ∑ a_C + √(m ∑ b_C)`. -/
theorem sum_sqrt_le {ι : Type*} (I : Finset ι) (a b : ι → ℝ) (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i) :
    ∑ i ∈ I, Real.sqrt (a i ^ 2 + b i) ≤ ∑ i ∈ I, a i + Real.sqrt (I.card * ∑ i ∈ I, b i) := by
  have h1 : ∀ i ∈ I, Real.sqrt (a i ^ 2 + b i) ≤ a i + Real.sqrt (b i) := by
    intro i _
    rw [Real.sqrt_le_left (add_nonneg (ha i) (Real.sqrt_nonneg _))]
    nlinarith [Real.sq_sqrt (hb i), Real.sqrt_nonneg (b i), ha i]
  have h2 : ∑ i ∈ I, Real.sqrt (b i) ≤ Real.sqrt (I.card * ∑ i ∈ I, b i) := by
    apply Real.le_sqrt_of_sq_le
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq I (fun _ => (1 : ℝ)) (fun i => Real.sqrt (b i))
    simp only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] at hcs
    calc (∑ i ∈ I, Real.sqrt (b i)) ^ 2 ≤ I.card * ∑ i ∈ I, Real.sqrt (b i) ^ 2 := hcs
      _ = I.card * ∑ i ∈ I, b i := by
        congr 1; exact Finset.sum_congr rfl (fun i _ => Real.sq_sqrt (hb i))
  calc ∑ i ∈ I, Real.sqrt (a i ^ 2 + b i) ≤ ∑ i ∈ I, (a i + Real.sqrt (b i)) := Finset.sum_le_sum h1
    _ = ∑ i ∈ I, a i + ∑ i ∈ I, Real.sqrt (b i) := Finset.sum_add_distrib
    _ ≤ _ := by linarith

end SmallCut
