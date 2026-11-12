import Mathlib

/-!
Deterministic core of the s-t minimum cut bound on simple graphs: the levels of a residual network
with costs at most 1, the length of a shortest path, the total cost of a flow built in equal steps,
the sparsifier sum over parts, the count of small vertices and of big parts, the choice of
parameters, peeling, and the combination that bounds the crossing edges.
-/

open Finset

namespace StCut

/-- A residual arc that leaves the level set `{π ≤ i}` has cost 1 and joins levels `i` and `i + 1`. -/
theorem arc_leaves_level (a b c i : ℤ) (hc : c ≤ 1) (harc : b ≤ a + c) (ha : a ≤ i) (hb : i < b) :
    c = 1 ∧ a = i ∧ b = i + 1 := by
  omega

/-- If each good level `i` has `r ≤ W c_i c_{i+1}`, then the number of good levels is at most
`s √W / √r`, where `s` is the sum of the `c_i`. -/
theorem good_levels (d : ℕ) (I : Finset ℕ) (hI : I ⊆ range d) (c : ℕ → ℝ) (hc : ∀ i, 0 ≤ c i)
    (r W s : ℝ) (hW : 0 ≤ W) (hgood : ∀ i ∈ I, r ≤ W * (c i * c (i + 1)))
    (hs : ∑ i ∈ range (d + 1), c i ≤ s) :
    (I.card : ℝ) * √r ≤ s * √W := by
  have h1 : ∑ i ∈ I, c i ≤ s := by
    refine le_trans (sum_le_sum_of_subset_of_nonneg ?_ fun i _ _ => hc i) hs
    intro i hi
    have := mem_range.1 (hI hi)
    exact mem_range.2 (by omega)
  have h2 : ∑ i ∈ I, c (i + 1) ≤ s := by
    have himg : ∑ i ∈ I, c (i + 1) = ∑ j ∈ I.image (· + 1), c j := by
      rw [sum_image]
      intro x _ y _ h
      simpa using h
    rw [himg]
    refine le_trans (sum_le_sum_of_subset_of_nonneg ?_ fun i _ _ => hc i) hs
    intro j hj
    obtain ⟨i, hi, rfl⟩ := mem_image.1 hj
    have := mem_range.1 (hI hi)
    exact mem_range.2 (by omega)
  have hstep : ∀ i ∈ I, √r ≤ √W * ((c i + c (i + 1)) / 2) := by
    intro i hi
    have hle : r ≤ W * ((c i + c (i + 1)) / 2) ^ 2 := by
      refine le_trans (hgood i hi) (mul_le_mul_of_nonneg_left ?_ hW)
      nlinarith [sq_nonneg (c i - c (i + 1))]
    calc √r ≤ √(W * ((c i + c (i + 1)) / 2) ^ 2) := Real.sqrt_le_sqrt hle
      _ = √W * ((c i + c (i + 1)) / 2) := by
        rw [Real.sqrt_mul hW, Real.sqrt_sq (by linarith [hc i, hc (i + 1)])]
  have hsum : (I.card : ℝ) * √r ≤ ∑ i ∈ I, √W * ((c i + c (i + 1)) / 2) := by
    have := sum_le_sum hstep
    simpa [sum_const, nsmul_eq_mul] using this
  have hexp : ∑ i ∈ I, √W * ((c i + c (i + 1)) / 2)
      = √W * ((∑ i ∈ I, c i + ∑ i ∈ I, c (i + 1)) / 2) := by
    rw [← mul_sum, ← sum_div, sum_add_distrib]
  have hsq : 0 ≤ √W := Real.sqrt_nonneg W
  calc (I.card : ℝ) * √r ≤ √W * ((∑ i ∈ I, c i + ∑ i ∈ I, c (i + 1)) / 2) := by rw [← hexp]; exact hsum
    _ ≤ √W * s := mul_le_mul_of_nonneg_left (by linarith) hsq
    _ = s * √W := mul_comm _ _

/-- A shortest path with `B` spoiled levels and otherwise good levels has length at most
`B + s √W / √r`, in the form that avoids the division. -/
theorem path_length (d B : ℕ) (I : Finset ℕ) (hI : I ⊆ range d) (hB : (range d \ I).card ≤ B)
    (c : ℕ → ℝ) (hc : ∀ i, 0 ≤ c i) (r W s : ℝ) (hW : 0 ≤ W)
    (hgood : ∀ i ∈ I, r ≤ W * (c i * c (i + 1))) (hs : ∑ i ∈ range (d + 1), c i ≤ s) :
    (d : ℝ) * √r ≤ B * √r + s * √W := by
  have hcard : d ≤ B + I.card := by
    have h := card_sdiff_add_card_eq_card hI
    rw [card_range] at h
    omega
  have hcardR : (d : ℝ) ≤ B + I.card := by exact_mod_cast hcard
  have := good_levels d I hI c hc r W s hW hgood hs
  nlinarith [Real.sqrt_nonneg r]

/-- `∑_{r = 1}^f 1 / √r ≤ 2 √f`. -/
theorem sum_inv_sqrt_le (f : ℕ) : ∑ r ∈ Icc 1 f, (1 / √(r : ℝ)) ≤ 2 * √(f : ℝ) := by
  induction f with
  | zero => simp
  | succ n ih =>
    rw [sum_Icc_succ_top (by omega)]
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hpos : (0 : ℝ) < √((n + 1 : ℕ) : ℝ) := Real.sqrt_pos.2 (by positivity)
    have hsq : √((n + 1 : ℕ) : ℝ) ^ 2 = (n : ℝ) + 1 := by
      rw [Real.sq_sqrt (by positivity)]; push_cast; ring
    have hsq' : √(n : ℝ) ^ 2 = n := Real.sq_sqrt hn
    have hn' := Real.sqrt_nonneg (n : ℝ)
    have hle : √(n : ℝ) ≤ √((n + 1 : ℕ) : ℝ) := Real.sqrt_le_sqrt (by push_cast; linarith)
    have hstep : 1 / √((n + 1 : ℕ) : ℝ) ≤ 2 * (√((n + 1 : ℕ) : ℝ) - √(n : ℝ)) := by
      rw [div_le_iff₀ hpos]
      nlinarith
    linarith

/-- Total cost of the flow: if the path found with `r` units left has length `d r` and
`d r · √r ≤ B √r + s √W`, then the sum of the lengths is at most `B f + 2 s √(W f)`. -/
theorem flow_cost (f B : ℕ) (d : ℕ → ℝ) (s W : ℝ) (hs : 0 ≤ s) (hW : 0 ≤ W)
    (hd : ∀ r ∈ Icc 1 f, d r * √(r : ℝ) ≤ B * √(r : ℝ) + s * √W) :
    ∑ r ∈ Icc 1 f, d r ≤ (B : ℝ) * f + 2 * s * √(W * f) := by
  have hstep : ∀ r ∈ Icc 1 f, d r ≤ B + s * √W * (1 / √(r : ℝ)) := by
    intro r hr
    have hr1 : 1 ≤ r := (mem_Icc.1 hr).1
    have hpos : (0 : ℝ) < √(r : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hr1)
    have h := hd r hr
    have hrw : (B : ℝ) + s * √W * (1 / √(r : ℝ)) = (B * √(r : ℝ) + s * √W) / √(r : ℝ) := by
      field_simp
    rw [hrw, le_div_iff₀ hpos]
    exact h
  have hsum := sum_le_sum hstep
  rw [sum_add_distrib, ← mul_sum] at hsum
  have hcard : ∑ _r ∈ Icc 1 f, (B : ℝ) = (B : ℝ) * f := by
    simp [sum_const, nsmul_eq_mul, mul_comm]
  rw [hcard] at hsum
  have hinv := sum_inv_sqrt_le f
  have hnn : 0 ≤ s * √W := mul_nonneg hs (Real.sqrt_nonneg W)
  have hmul := mul_le_mul_of_nonneg_left hinv hnn
  have heq : √(W * f) = √W * √(f : ℝ) := Real.sqrt_mul hW _
  rw [heq]
  nlinarith

/-- The combination: from `s D / 4 ≤ C`, `C ≤ (3/2) (k (b + s) + 2 b f + 4 s X)`, `k ≤ D / 24` and
`X ≤ D / 96`, the crossing edges satisfy `C ≤ (D / 8) b + 6 b f`, and `s D ≤ D b / 2 + 24 b f`. -/
theorem crossing_bound (C s b k f X D : ℝ) (hs : 0 ≤ s) (hb : 0 ≤ b) (hf : 0 ≤ f)
    (hk : k ≤ D / 24) (hX : X ≤ D / 96)
    (hD : s * D / 4 ≤ C) (hC : C ≤ 3 / 2 * (k * (b + s) + 2 * b * f + 4 * s * X)) :
    C ≤ D / 8 * b + 6 * (b * f) ∧ s * D ≤ D / 2 * b + 24 * (b * f) := by
  have h1 : k * (b + s) ≤ D / 24 * (b + s) := mul_le_mul_of_nonneg_right hk (by linarith)
  have h2 : s * X ≤ s * (D / 96) := mul_le_mul_of_nonneg_left hX hs
  have hmain : C ≤ D / 16 * b + D / 8 * s + 3 * (b * f) := by nlinarith
  have hsD : s * D ≤ D / 2 * b + 24 * (b * f) := by nlinarith
  constructor
  · nlinarith
  · exact hsD

/-- With `b ≤ 2 n / D`, in the form `b D ≤ 2 n`, the crossing edges number at most
`n / 4 + 12 n f / D`. -/
theorem crossing_final (C b f D n : ℝ) (hb : 0 ≤ b) (hf : 0 ≤ f) (hD : 0 < D)
    (hbD : b * D ≤ 2 * n) (hC : C ≤ D / 8 * b + 6 * (b * f)) :
    C ≤ n / 4 + 12 * n * f / D := by
  have hb' : b ≤ 2 * n / D := by rwa [le_div_iff₀ hD]
  have h1 : D / 8 * b ≤ n / 4 := by nlinarith
  have h2 : 6 * (b * f) ≤ 12 * n * f / D := by
    have : b * f ≤ 2 * n / D * f := mul_le_mul_of_nonneg_right hb' hf
    have heq : 12 * n * f / D = 6 * (2 * n / D * f) := by ring
    rw [heq]
    linarith
  linarith

/-- Peeled vertices have total list length at most `2 n D`: if the number of edges counted at the
peeling of each of at most `n` vertices is at most `D`, then twice their sum is at most `2 n D`. -/
theorem peel_lists (p n : ℕ) (hp : p ≤ n) (D : ℝ) (hD : 0 ≤ D) (e : ℕ → ℝ)
    (he : ∀ i ∈ range p, e i ≤ D) : 2 * ∑ i ∈ range p, e i ≤ 2 * (n * D) := by
  have h : ∑ i ∈ range p, e i ≤ p * D := by
    have := sum_le_sum he
    simpa [sum_const, nsmul_eq_mul] using this
  have hpn : (p : ℝ) * D ≤ n * D :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast hp) hD
  linarith

section Network

variable {ι A : Type*} [Fintype ι] [DecidableEq ι] [Fintype A]

/-- Cut at a level. A flow of value `r` in a residual network with costs at most 1 and potentials
`π` crosses `{π ≤ i}`, and only arcs of cost 1 from level `i` to level `i + 1` can carry it. -/
theorem level_capacity (tail head : A → ι) (cost : A → ℤ) (cap g : A → ℝ) (π : ι → ℤ)
    (src snk : ι) (r : ℝ) (i : ℤ) (hg0 : ∀ a, 0 ≤ g a) (hgcap : ∀ a, g a ≤ cap a)
    (hcons : ∀ v, ∑ a with tail a = v, g a - ∑ a with head a = v, g a
      = if v = src then r else if v = snk then -r else 0)
    (hpot : ∀ a, 0 < cap a → π (head a) ≤ π (tail a) + cost a) (hcost : ∀ a, cost a ≤ 1)
    (hs : π src ≤ i) (ht : i < π snk) :
    r ≤ ∑ a with (cost a = 1 ∧ π (tail a) = i ∧ π (head a) = i + 1), cap a := by
  classical
  set X : Finset ι := univ.filter fun v => π v ≤ i with hX
  have hsX : src ∈ X := by simp [hX, hs]
  have htX : snk ∉ X := by simp [hX, ht]
  have hne : snk ≠ src := fun h => htX (h ▸ hsX)
  have hrhs : ∑ v ∈ X, (if v = src then r else if v = snk then -r else 0) = r := by
    rw [sum_eq_single_of_mem src hsX]
    · simp
    · intro v hv hvs
      have hvt : v ≠ snk := fun h => htX (h ▸ hv)
      simp [hvs, hvt]
  have hout : ∀ φ : A → ι, ∑ v ∈ X, ∑ a with φ a = v, g a = ∑ a, if φ a ∈ X then g a else 0 := by
    intro φ
    simp_rw [sum_filter]
    rw [sum_comm]
    refine sum_congr rfl fun a _ => ?_
    simp [sum_ite_eq]
  have hsum : r = ∑ a, ((if tail a ∈ X then g a else 0) - (if head a ∈ X then g a else 0)) := by
    rw [sum_sub_distrib, ← hout tail, ← hout head, ← sum_sub_distrib, ← hrhs]
    exact sum_congr rfl fun v _ => (hcons v).symm
  rw [hsum, sum_filter]
  refine sum_le_sum fun a _ => ?_
  have hcap : 0 ≤ cap a := (hg0 a).trans (hgcap a)
  have hrhs0 : 0 ≤ if (cost a = 1 ∧ π (tail a) = i ∧ π (head a) = i + 1) then cap a else 0 := by
    split_ifs <;> simp [hcap]
  by_cases h1 : tail a ∈ X
  · by_cases h2 : head a ∈ X
    · simpa [h1, h2] using hrhs0
    · have h1' : π (tail a) ≤ i := by simpa [hX] using h1
      have h2' : i < π (head a) := by simpa [hX] using h2
      simp only [h1, h2, ite_true, ite_false, sub_zero]
      rcases (hg0 a).eq_or_lt with h0 | h0
      · rw [← h0]; exact hrhs0
      · have hpos : 0 < cap a := h0.trans_le (hgcap a)
        obtain ⟨c1, c2, c3⟩ := arc_leaves_level _ _ _ i (hcost a) (hpot a hpos) h1' h2'
        rw [if_pos ⟨c1, c2, c3⟩]
        exact hgcap a
  · have : (if tail a ∈ X then g a else 0) - (if head a ∈ X then g a else 0) ≤ 0 := by
      rw [if_neg h1]; split_ifs <;> linarith [hg0 a]
    exact this.trans hrhs0

variable {U : Type*} [Fintype U] [DecidableEq U]

/-- The arcs of cost 1 between levels `i` and `i + 1` come from pairs of vertices of `S`, each pair
of capacity at most `W`. -/
theorem level_pairs (tail head : A → ι) (cost : A → ℤ) (cap : A → ℝ) (π : ι → ℤ) (P : U → ι)
    (lift : A → U × U) (S : Finset U) (W : ℝ) (i : ℤ) (hcap : ∀ a, 0 ≤ cap a) (hW0 : 0 ≤ W)
    (hS : ∀ a, cost a = 1 → π (tail a) = i → π (head a) = i + 1 →
      (lift a).1 ∈ S ∧ (lift a).2 ∈ S ∧ P (lift a).1 = tail a ∧ P (lift a).2 = head a)
    (hW : ∀ p, ∑ a with (cost a = 1 ∧ lift a = p), cap a ≤ W) :
    ∑ a with (cost a = 1 ∧ π (tail a) = i ∧ π (head a) = i + 1), cap a
      ≤ W * (((S.filter fun u => π (P u) = i).card : ℝ)
        * ((S.filter fun u => π (P u) = i + 1).card : ℝ)) := by
  classical
  set Af : Finset A := univ.filter fun a => cost a = 1 ∧ π (tail a) = i ∧ π (head a) = i + 1
  set L₁ := S.filter fun u => π (P u) = i
  set L₂ := S.filter fun u => π (P u) = i + 1
  have hmaps : ∀ a ∈ Af, lift a ∈ L₁ ×ˢ L₂ := by
    intro a ha
    obtain ⟨hc, h1, h2⟩ := (mem_filter.1 ha).2
    obtain ⟨a1, a2, a3, a4⟩ := hS a hc h1 h2
    refine mem_product.2 ⟨mem_filter.2 ⟨a1, ?_⟩, mem_filter.2 ⟨a2, ?_⟩⟩
    · rw [a3]; exact h1
    · rw [a4]; exact h2
  rw [← sum_fiberwise_of_maps_to hmaps]
  have hbound : ∀ p ∈ L₁ ×ˢ L₂, ∑ a ∈ Af with lift a = p, cap a ≤ W := by
    intro p _
    refine le_trans (sum_le_sum_of_subset_of_nonneg ?_ fun a _ _ => hcap a) (hW p)
    intro a ha
    obtain ⟨h1, h2⟩ := mem_filter.1 ha
    exact mem_filter.2 ⟨mem_univ a, (mem_filter.1 h1).2.1, h2⟩
  have := sum_le_sum hbound
  simp only [sum_const, nsmul_eq_mul, card_product, Nat.cast_mul] at this
  linarith

/-- Lengths of a shortest path with `r` units left: levels without a big part give `r ≤ W c_i c_{i+1}`,
and each big part spoils at most two levels. -/
theorem rest_path_length (tail head : A → ι) (cost : A → ℤ) (cap g : A → ℝ) (π : ι → ℤ) (P : U → ι)
    (lift : A → U × U) (S : Finset U) (big : Finset ι) (src snk : ι) (r W : ℝ)
    (hW0 : 0 ≤ W) (hg0 : ∀ a, 0 ≤ g a) (hgcap : ∀ a, g a ≤ cap a)
    (hcons : ∀ v, ∑ a with tail a = v, g a - ∑ a with head a = v, g a
      = if v = src then r else if v = snk then -r else 0)
    (hpot : ∀ a, 0 < cap a → π (head a) ≤ π (tail a) + cost a) (hcost : ∀ a, cost a ≤ 1)
    (hsrc : π src = 0)
    (hlift : ∀ a, cost a = 1 → P (lift a).1 = tail a ∧ P (lift a).2 = head a)
    (hS : ∀ a, cost a = 1 → ((lift a).1 ∈ S ∨ tail a ∈ big) ∧ ((lift a).2 ∈ S ∨ head a ∈ big))
    (hW : ∀ p, ∑ a with (cost a = 1 ∧ lift a = p), cap a ≤ W) :
    (π snk : ℝ) * √r ≤ ((2 * big.card : ℕ) : ℝ) * √r + (S.card : ℝ) * √W := by
  classical
  have hcap : ∀ a, 0 ≤ cap a := fun a => (hg0 a).trans (hgcap a)
  set d := (π snk).toNat with hd
  set I : Finset ℕ := (range d).filter fun i => ∀ p ∈ big, π p ≠ (i : ℤ) ∧ π p ≠ (i : ℤ) + 1 with hI
  set c : ℕ → ℝ := fun j => ((S.filter fun u => π (P u) = (j : ℤ)).card : ℝ) with hc
  have hspoil : (range d \ I).card ≤ 2 * big.card := by
    have hsub : range d \ I ⊆ big.biUnion fun p => {(π p).toNat, (π p - 1).toNat} := by
      intro i hi
      obtain ⟨h1, h2⟩ := mem_sdiff.1 hi
      have : ∃ p ∈ big, π p = (i : ℤ) ∨ π p = (i : ℤ) + 1 := by
        by_contra hcon
        push_neg at hcon
        exact h2 (mem_filter.2 ⟨h1, fun p hp => hcon p hp⟩)
      obtain ⟨p, hp, hpi⟩ := this
      refine mem_biUnion.2 ⟨p, hp, ?_⟩
      rcases hpi with h | h
      · simp [h]
      · simp [h]
    refine (card_le_card hsub).trans (card_biUnion_le.trans ?_)
    have : ∀ p ∈ big, ({(π p).toNat, (π p - 1).toNat} : Finset ℕ).card ≤ 2 := fun p _ => card_le_two
    simpa [mul_comm] using sum_le_card_nsmul big _ 2 this
  have hgood : ∀ i ∈ I, r ≤ W * (c i * c (i + 1)) := by
    intro i hi
    obtain ⟨h1, h2⟩ := mem_filter.1 hi
    have hid : (i : ℤ) < π snk := by
      have := mem_range.1 h1
      omega
    have h3 := level_capacity tail head cost cap g π src snk r (i : ℤ) hg0 hgcap hcons hpot hcost
      (by rw [hsrc]; positivity) hid
    have h4 := level_pairs tail head cost cap π P lift S W (i : ℤ) hcap hW0
      (fun a hc' ht' hh' => by
        obtain ⟨l1, l2⟩ := hlift a hc'
        obtain ⟨s1, s2⟩ := hS a hc'
        have nt : tail a ∉ big := fun hb => (h2 _ hb).1 ht'
        have nh : head a ∉ big := fun hb => (h2 _ hb).2 hh'
        exact ⟨s1.resolve_right nt, s2.resolve_right nh, l1, l2⟩) hW
    have hcast : (((i + 1 : ℕ) : ℤ)) = (i : ℤ) + 1 := by push_cast; ring
    simp only [hc, hcast]
    exact h3.trans h4
  have hsum : ∑ j ∈ range (d + 1), c j ≤ (S.card : ℝ) := by
    have hdis : ((range (d + 1) : Finset ℕ) : Set ℕ).PairwiseDisjoint
        fun j : ℕ => S.filter fun u => π (P u) = (j : ℤ) := by
      intro j _ l _ hjl
      refine disjoint_left.2 fun u hu hu' => hjl ?_
      have h1 := (mem_filter.1 hu).2
      have h2 := (mem_filter.1 hu').2
      omega
    have h := card_biUnion hdis
    have hle : ((range (d + 1)).biUnion fun j : ℕ => S.filter fun u => π (P u) = (j : ℤ)).card
        ≤ S.card := card_le_card (biUnion_subset.2 fun j _ => filter_subset _ _)
    rw [h] at hle
    simp only [hc]
    exact_mod_cast hle
  have hmain := path_length d (2 * big.card) I (filter_subset _ _) hspoil c
    (fun j => Nat.cast_nonneg _) r W (S.card : ℝ) hW0 hgood hsum
  have hle : (π snk : ℝ) ≤ d := by
    have : π snk ≤ (d : ℤ) := by omega
    exact_mod_cast this
  exact (mul_le_mul_of_nonneg_right hle (Real.sqrt_nonneg r)).trans hmain

/-- Lemma B. Let the flow be built in `N` steps of size `δ`, with total cost `δ ∑ d_j`, where `d_j` is
the distance to the sink with `j δ` units left, and the remaining flow is a flow in the residual
network of that step. Then the cost is at most `2 b f + 2 s √(W f)` with `f = N δ`. -/
theorem flow_cost_graph (tail head : A → ι) (cost : A → ℤ) (cap g : ℕ → A → ℝ) (π : ℕ → ι → ℤ)
    (P : U → ι) (lift : A → U × U) (S : Finset U) (big : Finset ι) (src snk : ι)
    (N : ℕ) (δ W F : ℝ) (hδ : 0 < δ) (hW0 : 0 ≤ W)
    (hF : F = δ * ∑ j ∈ Icc 1 N, (π j snk : ℝ))
    (hg0 : ∀ j a, 0 ≤ g j a) (hgcap : ∀ j a, g j a ≤ cap j a)
    (hcons : ∀ j ∈ Icc 1 N, ∀ v, ∑ a with tail a = v, g j a - ∑ a with head a = v, g j a
      = if v = src then (j : ℝ) * δ else if v = snk then -((j : ℝ) * δ) else 0)
    (hpot : ∀ j ∈ Icc 1 N, ∀ a, 0 < cap j a → π j (head a) ≤ π j (tail a) + cost a)
    (hcost : ∀ a, cost a ≤ 1) (hsrc : ∀ j ∈ Icc 1 N, π j src = 0)
    (hlift : ∀ a, cost a = 1 → P (lift a).1 = tail a ∧ P (lift a).2 = head a)
    (hS : ∀ a, cost a = 1 → ((lift a).1 ∈ S ∨ tail a ∈ big) ∧ ((lift a).2 ∈ S ∨ head a ∈ big))
    (hW : ∀ j ∈ Icc 1 N, ∀ p, ∑ a with (cost a = 1 ∧ lift a = p), cap j a ≤ W) :
    F ≤ 2 * (big.card : ℝ) * ((N : ℝ) * δ) + 2 * (S.card : ℝ) * √(W * ((N : ℝ) * δ)) := by
  have hsδ : 0 < √δ := Real.sqrt_pos.2 hδ
  have hstep : ∀ j ∈ Icc 1 N, (π j snk : ℝ) * √(j : ℝ)
      ≤ ((2 * big.card : ℕ) : ℝ) * √(j : ℝ) + (S.card : ℝ) * √(W / δ) := by
    intro j hj
    have h := rest_path_length tail head cost (cap j) (g j) (π j) P lift S big src snk
      ((j : ℝ) * δ) W hW0 (hg0 j) (hgcap j) (hcons j hj) (hpot j hj) hcost (hsrc j hj) hlift hS
      (hW j hj)
    have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    rw [Real.sqrt_mul hj0] at h
    have hdiv : √(W / δ) * √δ = √W := by
      rw [← Real.sqrt_mul (div_nonneg hW0 hδ.le), div_mul_cancel₀ _ hδ.ne']
    have h' : ((π j snk : ℝ) * √(j : ℝ)) * √δ
        ≤ (((2 * big.card : ℕ) : ℝ) * √(j : ℝ) + (S.card : ℝ) * √(W / δ)) * √δ := by
      calc ((π j snk : ℝ) * √(j : ℝ)) * √δ = (π j snk : ℝ) * (√(j : ℝ) * √δ) := by ring
        _ ≤ ((2 * big.card : ℕ) : ℝ) * (√(j : ℝ) * √δ) + (S.card : ℝ) * √W := h
        _ = _ := by rw [← hdiv]; ring
    exact le_of_mul_le_mul_right h' hsδ
  have hmain := flow_cost N (2 * big.card) (fun j => (π j snk : ℝ)) (S.card : ℝ) (W / δ)
    (Nat.cast_nonneg _) (div_nonneg hW0 hδ.le) hstep
  have hroot : δ * √(W / δ * (N : ℝ)) = √(W * ((N : ℝ) * δ)) := by
    have : W * ((N : ℝ) * δ) = δ ^ 2 * (W / δ * (N : ℝ)) := by field_simp
    rw [this, Real.sqrt_mul (sq_nonneg δ), Real.sqrt_sq hδ.le]
  have hmul := mul_le_mul_of_nonneg_left hmain hδ.le
  rw [hF]
  push_cast at hmul
  calc δ * ∑ j ∈ Icc 1 N, (π j snk : ℝ)
      ≤ δ * (2 * (big.card : ℝ) * (N : ℝ) + 2 * (S.card : ℝ) * √(W / δ * (N : ℝ))) := hmul
    _ = 2 * (big.card : ℝ) * ((N : ℝ) * δ) + 2 * (S.card : ℝ) * (δ * √(W / δ * (N : ℝ))) := by ring
    _ = _ := by rw [hroot]

/-- Ordered sum of the weights of pairs in different parts, twice the crossing weight. -/
noncomputable def crossing (w : U → U → ℝ) (P : U → ι) : ℝ :=
  ∑ u, ∑ v, if P u ≠ P v then w u v else 0

/-- Weight of the cut around a part. -/
noncomputable def partCut (w : U → U → ℝ) (P : U → ι) (p : ι) : ℝ :=
  ∑ u, ∑ v, if P u = p ∧ P v ≠ p then w u v else 0

/-- The cuts around the parts sum to the ordered crossing weight. -/
theorem sum_partCut (w : U → U → ℝ) (P : U → ι) :
    ∑ p, partCut w P p = crossing w P := by
  unfold partCut crossing
  rw [sum_comm]
  refine sum_congr rfl fun u _ => ?_
  rw [sum_comm]
  refine sum_congr rfl fun v _ => ?_
  rw [sum_eq_single (P u)]
  · simp [eq_comm]
  · intro p _ hp
    rw [if_neg]
    exact fun h => hp h.1.symm
  · simp

/-- Lemma C, the sparsifier step: a lower bound on every cut around a part passes to the crossing
weight. -/
theorem crossing_sparsifier (g h : U → U → ℝ) (P : U → ι) (ε : ℝ)
    (hspars : ∀ p, (1 - ε) * partCut g P p ≤ partCut h P p) :
    (1 - ε) * crossing g P ≤ crossing h P := by
  rw [← sum_partCut g, ← sum_partCut h, mul_sum]
  exact sum_le_sum fun p _ => hspars p

/-- Lemma D: a vertex of `S` has at least `D` neighbours in `K` and at most `D / 2` of them in its
part. So `s D / 2` is at most the ordered crossing count. -/
theorem small_vertices (g : U → U → ℝ) (P : U → ι) (K S : Finset U) (D : ℝ)
    (h01 : ∀ u v, 0 ≤ g u v ∧ g u v ≤ 1) (hK : ∀ u v, v ∉ K → g u v = 0)
    (hdeg : ∀ u ∈ S, D ≤ ∑ v, g u v)
    (hsmall : ∀ u ∈ S, ((K.filter fun v => P v = P u).card : ℝ) ≤ D / 2) :
    (S.card : ℝ) * (D / 2) ≤ crossing g P := by
  have hone : ∀ u ∈ S, D / 2 ≤ ∑ v, if P u ≠ P v then g u v else 0 := by
    intro u hu
    have hsplit : ∑ v, g u v = (∑ v, if P v = P u then g u v else 0)
        + ∑ v, if P u ≠ P v then g u v else 0 := by
      rw [← sum_add_distrib]
      refine sum_congr rfl fun v _ => ?_
      by_cases h : P v = P u
      · simp [h]
      · have h' : P u ≠ P v := fun e => h e.symm
        simp [h, h']
    have hsame : (∑ v, if P v = P u then g u v else 0)
        ≤ ((K.filter fun v => P v = P u).card : ℝ) := by
      have hle : ∀ v ∈ (univ : Finset U), (if P v = P u then g u v else 0)
          ≤ if v ∈ K ∧ P v = P u then (1 : ℝ) else 0 := by
        intro v _
        by_cases hv : v ∈ K
        · by_cases h : P v = P u <;> simp [hv, h, (h01 u v).2]
        · simp [hv, hK u v hv]
      refine (sum_le_sum hle).trans (le_of_eq ?_)
      rw [sum_boole]
      congr 2
      ext v
      simp
    linarith [hdeg u hu, hsmall u hu]
  have hnn : ∀ u, 0 ≤ ∑ v, if P u ≠ P v then g u v else 0 := fun u =>
    sum_nonneg fun v _ => by split_ifs <;> simp [(h01 u v).1]
  calc (S.card : ℝ) * (D / 2) = ∑ _u ∈ S, D / 2 := by simp
    _ ≤ ∑ u ∈ S, ∑ v, if P u ≠ P v then g u v else 0 := sum_le_sum hone
    _ ≤ ∑ u, ∑ v, if P u ≠ P v then g u v else 0 :=
      sum_le_sum_of_subset_of_nonneg (subset_univ S) fun u _ _ => hnn u

omit [Fintype ι] [Fintype U] in
/-- Parts with at least `D / 2` vertices of `K` number at most `2 |K| / D`. -/
theorem big_parts (P : U → ι) (K : Finset U) (big : Finset ι) (D : ℝ)
    (hbig : ∀ p ∈ big, D / 2 ≤ ((K.filter fun v => P v = p).card : ℝ)) :
    (big.card : ℝ) * D ≤ 2 * (K.card : ℝ) := by
  have hdis : ((big : Finset ι) : Set ι).PairwiseDisjoint fun p => K.filter fun v => P v = p := by
    intro p _ q _ hpq
    refine disjoint_left.2 fun u hu hu' => hpq ?_
    rw [← (mem_filter.1 hu).2, (mem_filter.1 hu').2]
  have hle : (big.biUnion fun p => K.filter fun v => P v = p).card ≤ K.card :=
    card_le_card (biUnion_subset.2 fun p _ => filter_subset _ _)
  rw [card_biUnion hdis] at hle
  have hle' : ∑ p ∈ big, ((K.filter fun v => P v = p).card : ℝ) ≤ (K.card : ℝ) := by
    exact_mod_cast hle
  have hsum : ∑ _p ∈ big, D / 2 ≤ ∑ p ∈ big, ((K.filter fun v => P v = p).card : ℝ) :=
    sum_le_sum hbig
  simp only [sum_const, nsmul_eq_mul] at hsum
  linarith

omit [Fintype ι] [Fintype U] [DecidableEq U] in
/-- Parts meeting `K` are big or contain a vertex of `S`. -/
theorem parts_meeting (P : U → ι) (K S : Finset U) (big : Finset ι)
    (h : ∀ u ∈ K, P u ∈ big ∨ u ∈ S) :
    (K.image P).card ≤ big.card + S.card := by
  classical
  have hsub : K.image P ⊆ big ∪ S.image P := by
    intro p hp
    obtain ⟨u, hu, rfl⟩ := mem_image.1 hp
    rcases h u hu with h1 | h1
    · exact mem_union_left _ h1
    · exact mem_union_right _ (mem_image_of_mem P h1)
  exact (card_le_card hsub).trans ((card_union_le _ _).trans (by gcongr; exact card_image_le))

end Network

/-- Safety: a minimum cut has residual weight below `k = 4 ε f_H` after the flow is removed. -/
theorem safety_margin (ε f fH : ℝ) (hε : 0 < ε) (hε' : ε ≤ 1 / 3) (hf : 0 < f)
    (hlow : (1 - ε) * f ≤ fH) :
    (1 + ε) * f - fH < 4 * ε * fH := by
  have h1 : f ≤ 3 / 2 * fH := by nlinarith
  have hH : 0 < fH := by nlinarith
  nlinarith

/-- The choice of parameters: `ε ≤ D / (128 √(n f̂))` and `D ≥ 111 √f̂`, stated in squares, with
`f ≤ f̂`, `f ≤ n`, `f_H ≤ (4 / 3) f` and sparsifier weights at most `max {1, ε² n}`, gives
`k ≤ D / 24` and `√(W f_H) ≤ D / 96`. -/
theorem parameters (ε f fh fH n D W : ℝ) (hε : 0 ≤ ε) (hf : 0 ≤ f) (hfh : f ≤ fh) (hn : f ≤ n)
    (hH0 : 0 ≤ fH) (hH : fH ≤ 4 / 3 * f) (hD : 0 ≤ D)
    (h1 : (128 * ε) ^ 2 * (n * fh) ≤ D ^ 2) (h2 : 111 ^ 2 * fh ≤ D ^ 2)
    (hW : W ≤ 1 ∨ W ≤ ε ^ 2 * n) :
    4 * ε * fH ≤ D / 24 ∧ √(W * fH) ≤ D / 96 := by
  have hfh0 : 0 ≤ fh := hf.trans hfh
  have hn0 : 0 ≤ n := hf.trans hn
  constructor
  · have hsq : (128 * ε * f) ^ 2 ≤ D ^ 2 := by
      refine le_trans ?_ h1
      have hff : f * f ≤ n * fh := mul_le_mul hn hfh hf hn0
      have : (128 * ε * f) ^ 2 = (128 * ε) ^ 2 * (f * f) := by ring
      rw [this]
      exact mul_le_mul_of_nonneg_left hff (sq_nonneg _)
    have hle : 128 * ε * f ≤ D := abs_le_of_sq_le_sq' hsq hD |>.2
    have : ε * fH ≤ ε * (4 / 3 * f) := mul_le_mul_of_nonneg_left hH hε
    nlinarith
  · have hsqrt : W * fH ≤ (D / 96) ^ 2 := by
      rcases hW with hW | hW
      · have : W * fH ≤ 1 * (4 / 3 * f) :=
          mul_le_mul hW hH hH0 (by norm_num)
        nlinarith
      · have h3 : W * fH ≤ ε ^ 2 * n * (4 / 3 * f) :=
          mul_le_mul hW hH hH0 (by positivity)
        have h4 : ε ^ 2 * (n * f) ≤ ε ^ 2 * (n * fh) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hfh hn0) (sq_nonneg _)
        nlinarith
    rw [show D / 96 = √((D / 96) ^ 2) from (Real.sqrt_sq (by positivity)).symm]
    exact Real.sqrt_le_sqrt hsqrt

/-- All parts together: with Lemma A and the sparsifier bound as inputs, the ordered crossing weight
`2 C` of `G[K]` gives `C ≤ n / 4 + 12 n f / D`. -/
theorem crossing_edges (C Hc res F k b s f X D n ε : ℝ) (hb : 0 ≤ b) (hs : 0 ≤ s) (hf : 0 ≤ f)
    (hX0 : 0 ≤ X) (hD0 : 0 < D) (hC0 : 0 ≤ C) (hε : ε ≤ 1 / 3)
    (hspars : (1 - ε) * C ≤ Hc) (hsplit : Hc ≤ res + F)
    (hres : res ≤ k * (b + s)) (hF : F ≤ 2 * b * f + 2 * s * X)
    (hk : k ≤ D / 24) (hX : X ≤ D / 96) (hD : s * D / 4 ≤ C) (hbD : b * D ≤ 2 * n) :
    C ≤ n / 4 + 12 * n * f / D := by
  have h1 : 2 / 3 * C ≤ (1 - ε) * C := mul_le_mul_of_nonneg_right (by linarith) hC0
  have hsX : 0 ≤ s * X := mul_nonneg hs hX0
  have hC : C ≤ 3 / 2 * (k * (b + s) + 2 * b * f + 4 * s * X) := by linarith
  exact crossing_final C b f D n hb hf hD0 hbD (crossing_bound C s b k f X D hs hb hf hk hX hD hC).1

/-- Peeling: if each vertex of `L` has at most `D` neighbours that are outside `L` or later in the
order `ρ`, then the lists of `L` have total length at most `2 |L| D`. -/
theorem peel_total {V : Type*} [Fintype V] [DecidableEq V] (adj : V → V → Prop) [DecidableRel adj]
    (hsymm : ∀ u v, adj u v → adj v u) (hirr : ∀ v, ¬ adj v v) (L : Finset V) (ρ : V → ℕ)
    (hρ : ∀ u ∈ L, ∀ v ∈ L, ρ u = ρ v → u = v) (D : ℕ)
    (hlow : ∀ v ∈ L, (univ.filter fun w => adj v w ∧ (w ∉ L ∨ ρ v < ρ w)).card ≤ D) :
    ∑ v ∈ L, (univ.filter fun w => adj v w).card ≤ 2 * (L.card * D) := by
  classical
  set later : V → Finset V := fun v => univ.filter fun w => adj v w ∧ (w ∉ L ∨ ρ v < ρ w) with hl
  set early : V → Finset V := fun v => L.filter fun w => adj v w ∧ ρ w < ρ v with he
  have hsplit : ∀ v ∈ L, (univ.filter fun w => adj v w).card ≤ (later v).card + (early v).card := by
    intro v hv
    refine le_trans (card_le_card ?_) (card_union_le _ _)
    intro w hw
    have hvw : adj v w := (mem_filter.1 hw).2
    by_cases hwL : w ∈ L
    · have hne : ρ v ≠ ρ w := fun h => hirr v (by
        have := hρ v hv w hwL h
        rw [← this] at hvw
        exact hvw)
      rcases lt_or_gt_of_ne hne with h | h
      · exact mem_union_left _ (mem_filter.2 ⟨mem_univ _, hvw, Or.inr h⟩)
      · exact mem_union_right _ (mem_filter.2 ⟨hwL, hvw, h⟩)
    · exact mem_union_left _ (mem_filter.2 ⟨mem_univ _, hvw, Or.inl hwL⟩)
  have hdouble : ∑ v ∈ L, (early v).card ≤ ∑ v ∈ L, (later v).card := by
    have h1 : ∑ v ∈ L, (early v).card
        = ∑ v ∈ L, ∑ w ∈ L, if adj v w ∧ ρ w < ρ v then 1 else 0 := by
      exact sum_congr rfl fun v _ => card_filter _ _
    rw [h1, sum_comm]
    refine sum_le_sum fun w hw => ?_
    have h2 : (∑ v ∈ L, if adj v w ∧ ρ w < ρ v then 1 else 0)
        = (L.filter fun v => adj v w ∧ ρ w < ρ v).card := (card_filter _ _).symm
    rw [h2]
    refine card_le_card fun v hv => ?_
    obtain ⟨_, h3, h4⟩ := mem_filter.1 hv
    exact mem_filter.2 ⟨mem_univ _, hsymm _ _ h3, Or.inr h4⟩
  have hlater : ∑ v ∈ L, (later v).card ≤ L.card * D := by
    simpa using sum_le_card_nsmul L _ D hlow
  calc ∑ v ∈ L, (univ.filter fun w => adj v w).card
      ≤ ∑ v ∈ L, ((later v).card + (early v).card) := sum_le_sum hsplit
    _ = ∑ v ∈ L, (later v).card + ∑ v ∈ L, (early v).card := sum_add_distrib
    _ ≤ 2 * (L.card * D) := by omega

end StCut
