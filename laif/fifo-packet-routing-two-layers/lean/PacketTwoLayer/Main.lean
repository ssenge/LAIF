import PacketTwoLayer.Equilibrium
import PacketTwoLayer.Potential

/-!
# The bound `3 C ≤ 4 T* + 1`

* `cut_le`: for every `T` there are a split point `Y ≤ T + 1` and a number `k` such that the cut value is at most
  `Phik_A k t + Phik_B k L + k (T + 1 - t - L)` for all `t` and `L`. Here `Phik_A` and `Phik_B` are the contents of
  the `k` shortest edges of each layer, so this is the minimum cut written without sorting.
* `eqm_cut`: for an equilibrium whose player `m` arrives last, at time `C`, every `T` with
  `4 (T + 1) ≤ 3 C + a₁ + b₁` has a cut value at most `m`.
* `makespan_bound`: for every UFR equilibrium `ps` and every state `qs` with the same number of players,
  `3 C(ps) + a₁ + b₁ ≤ 4 C(qs) + 3`, where `a₁` and `b₁` are lower bounds of the transit times of the two layers.
  Equivalently `C(qs) ≥ ⌊(3 C(ps) + a₁ + b₁) / 4⌋` (`opt_ge`).
* `three_mul_makespan_le`: with transit times at least 1, `3 C(ps) ≤ 4 C(qs) + 1`.
-/

namespace PacketTwoLayer

open Finset

section Cut

variable (n : ℕ) (w : ℕ → ℕ) (k : ℕ)

/-- `Phik y - k y`. -/
def Fk (y : ℕ) : ℚ := (Phik n w k y : ℚ) - k * y

theorem Fk_succ (y : ℕ) : Fk n w k (y + 1) = Fk n w k y + (min (Ncnt n w (y + 1)) k : ℕ) - k := by
  unfold Fk Phik
  rw [Finset.sum_range_succ]
  push_cast
  ring

theorem Fk_antitone {y y' : ℕ} (h : y ≤ y') : Fk n w k y' ≤ Fk n w k y := by
  induction y', h using Nat.le_induction with
  | base => exact le_rfl
  | succ y' _ ih =>
    rw [Fk_succ]
    have : ((min (Ncnt n w (y' + 1)) k : ℕ) : ℚ) ≤ k := by exact_mod_cast min_le_right _ _
    linarith

theorem Fk_const {Y : ℕ} (hk : k ≤ Ncnt n w (Y + 1)) {y : ℕ} (h : Y ≤ y) : Fk n w k y = Fk n w k Y := by
  induction y, h using Nat.le_induction with
  | base => rfl
  | succ y hy ih =>
    rw [Fk_succ, ih]
    have := Ncnt_mono n w (show Y + 1 ≤ y + 1 by omega)
    rw [min_eq_right (by omega)]
    ring

theorem Fk_min {Y : ℕ} (hk : k ≤ Ncnt n w (Y + 1)) (y : ℕ) : Fk n w k Y ≤ Fk n w k y := by
  rcases le_total y Y with h | h
  · exact Fk_antitone n w k h
  · rw [Fk_const n w k hk h]

theorem Phi_eq_Phik {Y : ℕ} (hk : Ncnt n w Y ≤ k) : Phi n w Y = Phik n w k Y := by
  rw [Phi_eq_sum]
  unfold Phik
  apply Finset.sum_congr rfl
  intro u hu
  have := Ncnt_mono n w (show u + 1 ≤ Y from Finset.mem_range.mp hu)
  rw [min_eq_left (by omega)]

end Cut

/-- A split point of the cut. -/
theorem exists_split (nA : ℕ) (aF : ℕ → ℕ) (nB : ℕ) (bF : ℕ → ℕ) (T : ℕ) :
    ∃ Y ≤ T + 1, ∃ k, Ncnt nA aF Y ≤ k ∧ k ≤ Ncnt nA aF (Y + 1) ∧
      Ncnt nB bF (T + 1 - Y) ≤ k ∧ k ≤ Ncnt nB bF (T + 1 - Y + 1) := by
  suffices H : ∀ Y ≤ T + 1, Ncnt nB bF (T + 1 - Y) ≤ Ncnt nA aF (Y + 1) →
      ∃ Y₀ ≤ Y, ∃ k, Ncnt nA aF Y₀ ≤ k ∧ k ≤ Ncnt nA aF (Y₀ + 1) ∧
        Ncnt nB bF (T + 1 - Y₀) ≤ k ∧ k ≤ Ncnt nB bF (T + 1 - Y₀ + 1) by
    obtain ⟨Y₀, hY₀, k, hk⟩ := H (T + 1) le_rfl (by rw [Nat.sub_self, Ncnt_zero]; exact Nat.zero_le _)
    exact ⟨Y₀, hY₀, k, hk⟩
  intro Y
  induction Y with
  | zero =>
    intro _ hP
    refine ⟨0, le_rfl, Ncnt nB bF (T + 1), ?_, ?_, ?_, ?_⟩
    · rw [Ncnt_zero]; exact Nat.zero_le _
    · simpa using hP
    · simp
    · simpa using Ncnt_mono nB bF (Nat.le_succ (T + 1))
  | succ Y ih =>
    intro hY hP
    by_cases hPY : Ncnt nB bF (T + 1 - Y) ≤ Ncnt nA aF (Y + 1)
    · obtain ⟨Y₀, hY₀, k, hk⟩ := ih (by omega) hPY
      exact ⟨Y₀, by omega, k, hk⟩
    · push Not at hPY
      have hZ : T + 1 - Y = T + 1 - (Y + 1) + 1 := by omega
      rw [hZ] at hPY
      refine ⟨Y + 1, le_rfl, max (Ncnt nA aF (Y + 1)) (Ncnt nB bF (T + 1 - (Y + 1))), le_max_left _ _, ?_,
        le_max_right _ _, ?_⟩
      · exact max_le (Ncnt_mono nA aF (Nat.le_succ _)) hP
      · exact max_le hPY.le (Ncnt_mono nB bF (Nat.le_succ _))

/-- The minimum cut without sorting. -/
theorem cut_le (nA : ℕ) (aF : ℕ → ℕ) (nB : ℕ) (bF : ℕ → ℕ) (T : ℕ) :
    ∃ Y, ∃ k, ∀ ts L, (cutVal nA aF nB bF T Y : ℚ) ≤
      Phik nA aF k ts + Phik nB bF k L + k * ((T : ℚ) + 1 - ts - L) := by
  obtain ⟨Y, hY, k, h1, h2, h3, h4⟩ := exists_split nA aF nB bF T
  refine ⟨Y, k, fun ts L => ?_⟩
  have hA : (∑ x ∈ range nA, (Y - aF x)) = Phik nA aF k Y := Phi_eq_Phik nA aF k h1
  have hB : (∑ g ∈ range nB, (T + 1 - Y - bF g)) = Phik nB bF k (T + 1 - Y) := Phi_eq_Phik nB bF k h3
  have hFA := Fk_min nA aF k h2 ts
  have hFB := Fk_min nB bF k h4 L
  unfold Fk at hFA hFB
  unfold cutVal
  rw [hA, hB]
  push_cast
  rw [Nat.cast_sub hY] at hFB
  push_cast at hFB
  linarith

/-- For an equilibrium and its player `m`, every `T` with `4 (T + 1) ≤ 3 β m + a₁ + b₁` has a cut value at most
`m`. -/
theorem eqm_cut {n nA : ℕ} {aF : ℕ → ℕ} {D : BData} {e f α : ℕ → ℕ} {NF : ℕ → ℕ → ℕ}
    (E : Eqm n nA aF D e f α NF) {m : ℕ} (hm : m < n) (a₁ : ℕ) (ha₁ : ∀ x < nA, a₁ ≤ aF x) (T : ℕ)
    (hT : 4 * (T + 1) ≤ 3 * βv D f α NF m + a₁ + D.b₁) : ∃ Y, cutVal nA aF D.n D.w T Y ≤ m := by
  obtain ⟨Y, k, hcut⟩ := cut_le nA aF D.n D.w T
  refine ⟨Y, ?_⟩
  set ts := α m with hts
  set c := ca α m with hc
  set R := c ts with hR
  set L := D.mu (D.Bh c ts + R) with hL
  have hβ : βv D f α NF m ≤ ts + L := E.β_le hm
  have hαlow : ∀ j < n, a₁ ≤ α j := by
    intro j hj
    have := E.α_eq j hj
    have := ha₁ (e j) (E.e_lt j hj)
    omega
  have hc0 : ∀ t < a₁, c t = 0 := by
    intro t ht
    rw [hc]
    unfold ca
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro j hj hjt
    have := hαlow j (by have := Finset.mem_range.mp hj; omega)
    omega
  have hts1 : a₁ ≤ ts := hαlow m hm
  have h7 := D.phik_le k c a₁ ts R hc0 hts1
  rw [← hL] at h7
  -- the layer-1 edges up to time `t < t*` are all used at time `t`
  have hA : ∀ t < ts, Ncnt nA aF (t + 1) ≤ c t := by
    intro t ht
    rw [hc]
    unfold Ncnt ca
    calc ((range nA).filter (fun x => aF x < t + 1)).card
        ≤ (((range m).filter (fun j => α j = t)).image e).card := by
          apply Finset.card_le_card
          intro x hx
          simp only [Finset.mem_filter, Finset.mem_range] at hx
          have hle := E.α_le m hm x hx.1
          obtain ⟨j, hj, hej, hcj⟩ := exists_of_lt_cnt e x m (t - aF x) (by omega)
          have := E.α_eq j (by omega)
          rw [hej, hcj] at this
          simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_range]
          exact ⟨j, ⟨hj, by omega⟩, hej⟩
      _ ≤ _ := Finset.card_image_le
  have hPA : (Phik nA aF k ts : ℚ) ≤ ∑ t ∈ range ts, (min (c t) k : ℕ) := by
    unfold Phik
    push_cast
    apply Finset.sum_le_sum
    intro t ht
    have := hA t (Finset.mem_range.mp ht)
    exact min_le_min (by exact_mod_cast this) le_rfl
  have hsum : (∑ t ∈ range ts, (min (c t) k : ℕ) : ℚ) + ∑ t ∈ range ts, ((c t - k : ℕ) : ℚ) =
      ∑ t ∈ range ts, (c t : ℚ) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro t _
    have : min (c t) k + (c t - k) = c t := by omega
    exact_mod_cast this
  -- the players before `m` arrive at `v₁` by time `t*`
  have hmc : (m : ℚ) = ∑ t ∈ range ts, (c t : ℚ) + R := by
    have h1 : (range m).card = ∑ t ∈ range (ts + 1), ((range m).filter (fun j => α j = t)).card := by
      apply Finset.card_eq_sum_card_fiberwise
      intro j hj
      simp only [Finset.mem_coe, Finset.mem_range] at hj ⊢
      have := E.α_mono hj.le hm
      omega
    rw [Finset.card_range, Finset.sum_range_succ] at h1
    rw [hR, hc]
    unfold ca
    exact_mod_cast h1
  have hcutq := hcut ts L
  have hLb : D.b₁ ≤ L := D.b₁_le_mu _
  rw [Nat.cast_sub hts1, Nat.cast_sub hLb] at h7
  have hTq : (4 : ℚ) * (T + 1) ≤ 3 * (ts + L) + a₁ + D.b₁ := by
    have : 4 * (T + 1) ≤ 3 * (ts + L) + a₁ + D.b₁ := by omega
    exact_mod_cast this
  have hk0 : (0 : ℚ) ≤ k := by positivity
  have hprod : (k : ℚ) * (4 * (T + 1) - 3 * (ts + L) - a₁ - D.b₁) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hk0 (by linarith)
  have hPA' : (Phik nA aF k ts : ℚ) ≤ ∑ t ∈ range ts, ((min (c t) k : ℕ) : ℚ) := by exact_mod_cast hPA
  have key : (cutVal nA aF D.n D.w T Y : ℚ) ≤ m := by linarith
  exact_mod_cast key

/-- The makespan of the empty state is 0. -/
theorem makespan_nil (a b : List ℕ) : makespan a b [] = 0 := by
  simp [makespan, times, layer]

/-- For every UFR equilibrium `ps` and every state `qs` with the same number of players,
`3 C(ps) + a₁ + b₁ ≤ 4 C(qs) + 3`, where `a₁` and `b₁` are lower bounds of the transit times of the two layers. -/
theorem makespan_bound (a b : List ℕ) (ps qs : List (ℕ × ℕ))
    (hps : ∀ p ∈ ps, p.1 < a.length ∧ p.2 < b.length) (hqs : ∀ p ∈ qs, p.1 < a.length ∧ p.2 < b.length)
    (hlen : qs.length = ps.length) (hne : ps ≠ []) (h : UFR a b ps)
    (a₁ b₁ : ℕ) (ha₁ : ∀ x ∈ a, a₁ ≤ x) (hb₁ : ∀ y ∈ b, b₁ ≤ y) :
    3 * makespan a b ps + a₁ + b₁ ≤ 4 * makespan a b qs + 3 := by
  have hn : 0 < ps.length := List.length_pos_iff.mpr hne
  have hb0 : 0 < b.length := lt_of_le_of_lt (Nat.zero_le _) (valid_getD hps hn).2
  obtain ⟨g₀, hg₀, hmin⟩ := Finset.exists_min_image (range b.length) (fun g => b.getD g 0)
    ⟨0, Finset.mem_range.mpr hb0⟩
  have hg₀' := Finset.mem_range.mp hg₀
  let D : BData := ⟨b.length, fun g => b.getD g 0, b.getD g₀ 0, g₀, hg₀', rfl,
    fun g hg => hmin g (Finset.mem_range.mpr hg)⟩
  obtain ⟨E, _, hl2, hβ⟩ := eqm_of_UFR a b ps hps h D rfl rfl
  have hne2 : (times a b ps).2 ≠ [] := by
    intro h0
    have : (times a b ps).2.length = 0 := by rw [h0]; rfl
    omega
  obtain ⟨m, hm, hmC⟩ := exists_getD_eq_foldl_max _ hne2
  rw [hl2] at hm
  have hC : makespan a b ps = (times a b ps).2.getD m 0 := hmC.symm
  have hbD : b₁ ≤ D.b₁ := by
    show b₁ ≤ b.getD g₀ 0
    rw [getD_of_lt _ hg₀']
    exact hb₁ _ (List.getElem_mem _)
  have ha₁' : ∀ x < a.length, a₁ ≤ a.getD x 0 := by
    intro x hx
    rw [getD_of_lt _ hx]
    exact ha₁ _ (List.getElem_mem _)
  by_contra hcon
  push Not at hcon
  have hT : 4 * (makespan a b qs + 1) ≤ 3 * (times a b ps).2.getD m 0 + a₁ + D.b₁ := by
    rw [← hC]; omega
  rw [hβ m hm] at hT
  obtain ⟨Y, hY⟩ := eqm_cut E hm a₁ ha₁' (makespan a b qs) hT
  have := opt_cut a b qs hqs Y
  have hDn : D.n = b.length := rfl
  have hDw : D.w = fun g => b.getD g 0 := rfl
  rw [hDn, hDw] at hY
  omega

/-- The optimal makespan is at least `⌊(3 C + a₁ + b₁) / 4⌋` for every UFR equilibrium with makespan `C`. -/
theorem opt_ge (a b : List ℕ) (ps qs : List (ℕ × ℕ))
    (hps : ∀ p ∈ ps, p.1 < a.length ∧ p.2 < b.length) (hqs : ∀ p ∈ qs, p.1 < a.length ∧ p.2 < b.length)
    (hlen : qs.length = ps.length) (hne : ps ≠ []) (h : UFR a b ps)
    (a₁ b₁ : ℕ) (ha₁ : ∀ x ∈ a, a₁ ≤ x) (hb₁ : ∀ y ∈ b, b₁ ≤ y) :
    (3 * makespan a b ps + a₁ + b₁) / 4 ≤ makespan a b qs := by
  have := makespan_bound a b ps qs hps hqs hlen hne h a₁ b₁ ha₁ hb₁
  omega

/-- For every two-layer instance with transit times at least 1, every UFR equilibrium `ps` and every state `qs`
with the same number of players, `3 C(ps) ≤ 4 C(qs) + 1`. -/
theorem three_mul_makespan_le (a b : List ℕ) (ha : ∀ x ∈ a, 1 ≤ x) (hb : ∀ x ∈ b, 1 ≤ x)
    (ps qs : List (ℕ × ℕ)) (hps : ∀ p ∈ ps, p.1 < a.length ∧ p.2 < b.length)
    (hqs : ∀ p ∈ qs, p.1 < a.length ∧ p.2 < b.length) (hlen : qs.length = ps.length) (h : UFR a b ps) :
    3 * makespan a b ps ≤ 4 * makespan a b qs + 1 := by
  by_cases hne : ps = []
  · subst hne; rw [makespan_nil]; omega
  · have := makespan_bound a b ps qs hps hqs hlen hne h 1 1 ha hb
    omega

end PacketTwoLayer
