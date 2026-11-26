import Mathlib

/-!
# Counting lemmas for the grouped contraction algorithm

The class of a group of size `s` is `Nat.log 2 s`. A vertex changes its group either when its
supernode is the smaller side of an absorption (the class does not decrease and the supernode at
least doubles), or by a merge that at least doubles its group or joins two groups of one class
(the class rises). These lemmas bound the number of groups per vertex, the number of groups per
supernode, the rows handed out by doubling batches, and the total cost by the Cauchy-Schwarz
inequality.
-/

namespace ArbGroups

open Finset

/-- The class of a group of size `s`. -/
def cls (s : ℕ) : ℕ := Nat.log 2 s

/-- Case (a): a group that is not smaller has a class that is not smaller. -/
theorem cls_mono {s t : ℕ} (h : s ≤ t) : cls s ≤ cls t := Nat.log_mono_right h

/-- Case (b): a group of at least twice the size has a strictly larger class. -/
theorem cls_double {s t : ℕ} (hs : 1 ≤ s) (h : 2 * s ≤ t) : cls s + 1 ≤ cls t := by
  unfold cls
  apply Nat.le_log_of_pow_le (by norm_num)
  have := Nat.pow_log_le_self 2 (show s ≠ 0 by omega)
  rw [pow_succ]; omega

/-- Case (c): merging two groups of the same class gives a strictly larger class. -/
theorem cls_merge {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) (h : cls a = cls b) :
    cls a + 1 ≤ cls (a + b) := by
  unfold cls at *
  apply Nat.le_log_of_pow_le (by norm_num)
  have h1 := Nat.pow_log_le_self 2 (show a ≠ 0 by omega)
  have h2 := Nat.pow_log_le_self 2 (show b ≠ 0 by omega)
  rw [← h] at h2
  rw [pow_succ]; omega

/-- Groups of pairwise distinct classes with total size at most `n`: at most `log₂ n + 1`. -/
theorem card_le_of_distinct_cls {ι : Type*} (G : Finset ι) (size : ι → ℕ) (n : ℕ)
    (hinj : Set.InjOn (fun g => cls (size g)) G) (hsum : ∑ g ∈ G, size g ≤ n) :
    G.card ≤ Nat.log 2 n + 1 := by
  classical
  have hsub : G.image (fun g => cls (size g)) ⊆ range (Nat.log 2 n + 1) := by
    intro c hc
    obtain ⟨g, hg, rfl⟩ := mem_image.1 hc
    have : size g ≤ n := (single_le_sum (fun _ _ => Nat.zero_le _) hg).trans hsum
    exact mem_range.2 (Nat.lt_succ_of_le (cls_mono this |>.trans_eq (by rfl)))
  calc G.card = (G.image (fun g => cls (size g))).card := (card_image_of_injOn hinj).symm
    _ ≤ (range (Nat.log 2 n + 1)).card := card_le_card hsub
    _ = Nat.log 2 n + 1 := card_range _

/-- A sequence that never decreases and rises at every step of `S` rises by at least the number
of those steps. -/
theorem count_strict (f : ℕ → ℕ) (S : Finset ℕ) (m : ℕ) (hmono : ∀ i < m, f i ≤ f (i + 1))
    (hstr : ∀ i < m, i ∈ S → f i + 1 ≤ f (i + 1)) :
    f 0 + ((range m).filter (· ∈ S)).card ≤ f m := by
  induction m with
  | zero => simp
  | succ m ih =>
    have ih' := ih (fun i hi => hmono i (by omega)) (fun i hi => hstr i (by omega))
    rw [range_add_one, filter_insert]
    have hm : m ∉ (range m).filter (· ∈ S) := by simp
    split_ifs with h
    · rw [card_insert_of_notMem hm]; have := hstr m (by omega) h; omega
    · have := hmono m (by omega); omega

/-- A sequence that never decreases and at least doubles at every step of `A`. -/
theorem count_double (z : ℕ → ℕ) (A : Finset ℕ) (m : ℕ) (hmono : ∀ i < m, z i ≤ z (i + 1))
    (hdbl : ∀ i < m, i ∈ A → 2 * z i ≤ z (i + 1)) :
    2 ^ ((range m).filter (· ∈ A)).card * z 0 ≤ z m := by
  induction m with
  | zero => simp
  | succ m ih =>
    have ih' := ih (fun i hi => hmono i (by omega)) (fun i hi => hdbl i (by omega))
    rw [range_add_one, filter_insert]
    have hm : m ∉ (range m).filter (· ∈ A) := by simp
    split_ifs with h
    · rw [card_insert_of_notMem hm, pow_succ]; have := hdbl m (by omega) h; nlinarith
    · have := hmono m (by omega); omega

/-- A supernode of size between `1` and `n` that at least doubles at each of `k` steps: `k ≤ log₂ n`. -/
theorem doublings_le_log (z : ℕ → ℕ) (k n : ℕ) (h0 : 1 ≤ z 0) (hk : z k ≤ n)
    (hdbl : ∀ i < k, 2 * z i ≤ z (i + 1)) : k ≤ Nat.log 2 n := by
  have h := count_double z (range k) k (fun i hi => by have := hdbl i hi; omega)
    (fun i hi _ => hdbl i hi)
  have hc : ((range k).filter (· ∈ range k)).card = k := by
    rw [filter_true_of_mem (fun x hx => hx), card_range]
  rw [hc] at h
  exact Nat.le_log_of_pow_le (by norm_num) (by nlinarith)

/-- **Lemma 2.** Steps `0, …, m-1` change the group of a vertex. At steps in `A` its supernode
(sizes `z`) is the smaller side and at least doubles, and the class `c` of its group does not
decrease; at the other steps the class rises. Sizes stay in `[1, n]` and classes at most `log₂ n`.
Then `m ≤ 2 log₂ n`, so the vertex lies in at most `2 log₂ n + 1` groups. -/
theorem lemma2 (c z : ℕ → ℕ) (A : Finset ℕ) (m n : ℕ)
    (hc : ∀ i < m, c i ≤ c (i + 1)) (hcstr : ∀ i < m, i ∉ A → c i + 1 ≤ c (i + 1))
    (hz : ∀ i < m, z i ≤ z (i + 1)) (hzdbl : ∀ i < m, i ∈ A → 2 * z i ≤ z (i + 1))
    (hz0 : 1 ≤ z 0) (hzm : z m ≤ n) (hcm : c m ≤ Nat.log 2 n) : m ≤ 2 * Nat.log 2 n := by
  have h1 := count_strict c (range m \ A) m hc (fun i hi hS => hcstr i hi (mem_sdiff.1 hS).2)
  have h2 := count_double z A m hz hzdbl
  have hA : ((range m).filter (· ∈ A)).card ≤ Nat.log 2 n :=
    Nat.le_log_of_pow_le (by norm_num) (by nlinarith)
  have hsplit : ((range m).filter (· ∈ A)).card + ((range m).filter (· ∈ range m \ A)).card = m := by
    have : (range m).filter (· ∈ range m \ A) = (range m).filter (fun i => ¬ i ∈ A) := by
      ext i; simp
    rw [this, card_filter_add_card_filter_not, card_range]
  omega

/-- **Lemma 3.** A row is dropped only at absorptions where its supernode is the smaller side, at
most `K` of them, and each time from at most `L` groups: at most `L * K` drops. -/
theorem lemma3 {ι : Type*} (E : Finset ι) (k : ι → ℕ) (L K : ℕ) (hk : ∀ e ∈ E, k e ≤ L)
    (hE : E.card ≤ K) : ∑ e ∈ E, k e ≤ L * K := by
  calc ∑ e ∈ E, k e ≤ E.card * L := by simpa using sum_le_card_nsmul E k L hk
    _ ≤ K * L := Nat.mul_le_mul_right _ hE
    _ = L * K := Nat.mul_comm _ _

/-- **Lemma 4, rows.** Batches of sizes `1, 2, …, 2^t`; the first `t` are fully dropped, `d` drops
in total. Then the rows handed out are at most `2d + 1`. -/
theorem lemma4_rows (t d : ℕ) (hd : ∑ i ∈ range t, 2 ^ i ≤ d) :
    ∑ i ∈ range (t + 1), 2 ^ i ≤ 2 * d + 1 := by
  have h := Nat.geomSum_eq (le_refl 2) t
  have h' := Nat.geomSum_eq (le_refl 2) (t + 1)
  simp only [show (2 : ℕ) - 1 = 1 from rfl, Nat.div_one] at h h'
  rw [h'] ; rw [h] at hd
  have : 1 ≤ 2 ^ t := Nat.one_le_two_pow
  rw [pow_succ]; omega

/-- `√(x^i) = √x^i` for `x ≥ 0`. -/
theorem sqrt_pow' {x : ℝ} (hx : 0 ≤ x) (i : ℕ) : Real.sqrt (x ^ i) = Real.sqrt x ^ i := by
  induction i with
  | zero => simp
  | succ i ih => rw [pow_succ, Real.sqrt_mul (pow_nonneg hx i), ih, pow_succ]

/-- Geometric sum of square roots: `∑_{i ≤ t} √2^i ≤ (2 + √2) √2^t`. -/
theorem sqrt_geom (t : ℕ) :
    ∑ i ∈ range (t + 1), Real.sqrt 2 ^ i ≤ (2 + Real.sqrt 2) * Real.sqrt 2 ^ t := by
  have hs : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hs0 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  induction t with
  | zero => simp only [zero_add, sum_range_one, pow_zero, mul_one]; linarith
  | succ t ih =>
    rw [sum_range_succ, pow_succ]
    have hp : 0 ≤ Real.sqrt 2 ^ t := pow_nonneg hs0 t
    nlinarith

/-- **Lemma 4, cost.** With the first `t` batches dropped (`d` drops), the batches of sizes
`1, …, 2^t` cost `∑ √(n s 2^i) ≤ (2 + √2) √(n s (d + 1))`. -/
theorem lemma4_cost (t d : ℕ) (n s : ℝ) (hn : 0 ≤ n) (hs : 0 ≤ s)
    (hd : ∑ i ∈ range t, 2 ^ i ≤ d) :
    ∑ i ∈ range (t + 1), Real.sqrt (n * s * 2 ^ i) ≤ (2 + Real.sqrt 2) * Real.sqrt (n * s * (d + 1)) := by
  have hs0 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hns : 0 ≤ n * s := mul_nonneg hn hs
  have hterm : ∀ i : ℕ, Real.sqrt (n * s * 2 ^ i) = Real.sqrt (n * s) * Real.sqrt 2 ^ i := by
    intro i; rw [Real.sqrt_mul hns, sqrt_pow' (by norm_num)]
  simp_rw [hterm]
  rw [← mul_sum]
  have h2t : (2 : ℝ) ^ t ≤ d + 1 := by
    have := Nat.geomSum_eq (le_refl 2) t
    simp only [show (2 : ℕ) - 1 = 1 from rfl, Nat.div_one] at this
    rw [this] at hd
    have h1 : 1 ≤ 2 ^ t := Nat.one_le_two_pow
    have : 2 ^ t ≤ d + 1 := by omega
    exact_mod_cast this
  have hst : Real.sqrt 2 ^ t ≤ Real.sqrt (d + 1) := by
    rw [← sqrt_pow' (by norm_num)]; exact Real.sqrt_le_sqrt h2t
  rw [Real.sqrt_mul hns]
  have := sqrt_geom t
  have hsq : 0 ≤ Real.sqrt (n * s) := Real.sqrt_nonneg _
  calc Real.sqrt (n * s) * ∑ i ∈ range (t + 1), Real.sqrt 2 ^ i
      ≤ Real.sqrt (n * s) * ((2 + Real.sqrt 2) * Real.sqrt 2 ^ t) := mul_le_mul_of_nonneg_left this hsq
    _ ≤ Real.sqrt (n * s) * ((2 + Real.sqrt 2) * Real.sqrt (d + 1)) := by gcongr
    _ = (2 + Real.sqrt 2) * (Real.sqrt (n * s) * Real.sqrt (d + 1)) := by ring

/-- **Total cost.** If group `g` costs at most `C √(n s_g e_g)`, with `∑ s_g ≤ S` and
`∑ e_g ≤ D`, the total is at most `C √n √S √D` (Cauchy-Schwarz). -/
theorem total_cost {ι : Type*} (G : Finset ι) (cost s e : ι → ℝ) (C n S D : ℝ) (hC : 0 ≤ C)
    (hn : 0 ≤ n) (hs : ∀ g, 0 ≤ s g) (he : ∀ g, 0 ≤ e g)
    (hcost : ∀ g ∈ G, cost g ≤ C * Real.sqrt (n * s g * e g))
    (hS : ∑ g ∈ G, s g ≤ S) (hD : ∑ g ∈ G, e g ≤ D) :
    ∑ g ∈ G, cost g ≤ C * Real.sqrt n * Real.sqrt S * Real.sqrt D := by
  have hsplit : ∀ g, Real.sqrt (n * s g * e g) = Real.sqrt n * (Real.sqrt (s g) * Real.sqrt (e g)) := by
    intro g; rw [Real.sqrt_mul (mul_nonneg hn (hs g)), Real.sqrt_mul hn]; ring
  have hcs := Real.sum_sqrt_mul_sqrt_le G hs he
  calc ∑ g ∈ G, cost g ≤ ∑ g ∈ G, C * Real.sqrt (n * s g * e g) := sum_le_sum hcost
    _ = C * Real.sqrt n * ∑ g ∈ G, Real.sqrt (s g) * Real.sqrt (e g) := by
        rw [mul_sum]; refine sum_congr rfl (fun g _ => ?_); rw [hsplit]; ring
    _ ≤ C * Real.sqrt n * (Real.sqrt (∑ g ∈ G, s g) * Real.sqrt (∑ g ∈ G, e g)) := by
        gcongr
    _ ≤ C * Real.sqrt n * (Real.sqrt S * Real.sqrt D) := by
        gcongr
    _ = C * Real.sqrt n * Real.sqrt S * Real.sqrt D := by ring

end ArbGroups
