import PacketTwoLayer.Backlog

/-!
# A potential for the worst-case backlog process

Unit `j` of the backlog (the `(j + 1)`-st packet) sits at level `mu j` and has slope `slope j = N (mu j + 1)`, the
number of edges that share it. The fluid level of a backlog `B` is `nu B = b₁ + ∑_{j < B} 1 / slope j`, and
`Psi k B = ∑_{j < B} min (slope j) k / slope j` is the part of the backlog that lies in the `k` shortest edges.
At the backlog `Phi y` both are exact: `nu (Phi y) = y` and `Psi k (Phi y) = Phik k y` (`nu_Psi_Phi`).

* `psi_step`: one step `B ↦ gfun (B + c)` raises `Psi k` by at most `(c - k)⁺ + (k / 4) (1 + Δ nu)`.
* `phik_le`: summed over the loading, `Phik k L ≤ E_k + R + (k / 4) (t* - a₁ + L - b₁)` for
  `L = mu (Bh t* + R)` and `E_k = ∑_{t < t*} (c t - k)⁺`.
-/

namespace PacketTwoLayer

open Finset

namespace BData

variable (D : BData)

/-- The number of edges that share backlog unit `j`. -/
def slope (j : ℕ) : ℕ := Ncnt D.n D.w (D.mu j + 1)

theorem slope_pos (j : ℕ) : 0 < D.slope j := D.N_pos (by have := D.b₁_le_mu j; omega)

/-- The fluid level of a backlog. -/
def nu (B : ℕ) : ℚ := (D.b₁ : ℚ) + ∑ j ∈ range B, 1 / (D.slope j : ℚ)

/-- The part of a backlog that lies in the `k` shortest edges. -/
def Psi (k B : ℕ) : ℚ := ∑ j ∈ range B, min (D.slope j : ℚ) (k : ℚ) / (D.slope j : ℚ)

theorem nu_sub {B B' : ℕ} (h : B ≤ B') : D.nu B' - D.nu B = ∑ j ∈ Ico B B', 1 / (D.slope j : ℚ) := by
  unfold nu
  rw [← Finset.sum_range_add_sum_Ico _ h]
  ring

theorem Psi_sub (k : ℕ) {B B' : ℕ} (h : B ≤ B') :
    D.Psi k B' - D.Psi k B = ∑ j ∈ Ico B B', min (D.slope j : ℚ) (k : ℚ) / (D.slope j : ℚ) := by
  unfold Psi
  rw [← Finset.sum_range_add_sum_Ico _ h]
  ring

theorem Psi_term_nonneg (k j : ℕ) : 0 ≤ min (D.slope j : ℚ) (k : ℚ) / (D.slope j : ℚ) :=
  div_nonneg (le_min (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (Nat.cast_nonneg _)

theorem Psi_term_le_one (k j : ℕ) : min (D.slope j : ℚ) (k : ℚ) / (D.slope j : ℚ) ≤ 1 := by
  have h := D.slope_pos j
  rw [div_le_one (by exact_mod_cast h)]
  exact min_le_left _ _

theorem Psi_mono (k : ℕ) {B B' : ℕ} (h : B ≤ B') : D.Psi k B ≤ D.Psi k B' := by
  have := D.Psi_sub k h
  have : 0 ≤ ∑ j ∈ Ico B B', min (D.slope j : ℚ) (k : ℚ) / (D.slope j : ℚ) :=
    Finset.sum_nonneg (fun j _ => D.Psi_term_nonneg k j)
  linarith

theorem Psi_add_le (k B r : ℕ) : D.Psi k (B + r) ≤ D.Psi k B + r := by
  have h := D.Psi_sub k (Nat.le_add_right B r)
  have : ∑ j ∈ Ico B (B + r), min (D.slope j : ℚ) (k : ℚ) / (D.slope j : ℚ) ≤
      ∑ j ∈ Ico B (B + r), (1 : ℚ) :=
    Finset.sum_le_sum (fun j _ => D.Psi_term_le_one k j)
  simp only [Finset.sum_const, Nat.card_Ico, Nat.add_sub_cancel_left, nsmul_eq_mul, mul_one] at this
  linarith

theorem nu_mono {B B' : ℕ} (h : B ≤ B') : D.nu B ≤ D.nu B' := by
  have := D.nu_sub h
  have : 0 ≤ ∑ j ∈ Ico B B', 1 / (D.slope j : ℚ) := Finset.sum_nonneg (fun j _ => by positivity)
  linarith

theorem slope_of_mem {y j : ℕ} (h1 : Phi D.n D.w y ≤ j) (h2 : j < Phi D.n D.w (y + 1)) :
    D.slope j = Ncnt D.n D.w (y + 1) := by
  unfold slope; rw [D.mu_eq h1 h2]

theorem sum_inv_slope {A B s : ℕ} (h : ∀ j ∈ Ico A B, D.slope j = s) :
    ∑ j ∈ Ico A B, 1 / (D.slope j : ℚ) = ((B - A : ℕ) : ℚ) * (1 / (s : ℚ)) := by
  rw [Finset.sum_congr rfl
    (fun j hj => by rw [h j hj] : ∀ j ∈ Ico A B, 1 / (D.slope j : ℚ) = 1 / (s : ℚ)),
    Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]

theorem sum_min_slope (k : ℕ) {A B s : ℕ} (h : ∀ j ∈ Ico A B, D.slope j = s) :
    ∑ j ∈ Ico A B, min (D.slope j : ℚ) (k : ℚ) / (D.slope j : ℚ) =
      ((B - A : ℕ) : ℚ) * (min (s : ℚ) (k : ℚ) / (s : ℚ)) := by
  rw [Finset.sum_congr rfl
    (fun j hj => by rw [h j hj] :
      ∀ j ∈ Ico A B, min (D.slope j : ℚ) (k : ℚ) / (D.slope j : ℚ) = min (s : ℚ) (k : ℚ) / (s : ℚ)),
    Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]

/-- At the backlog `Phi y` the fluid level is `y` and the potential is `Phik k y`. -/
theorem nu_Psi_Phi (k : ℕ) :
    ∀ y, D.b₁ ≤ y → D.nu (Phi D.n D.w y) = y ∧ D.Psi k (Phi D.n D.w y) = Phik D.n D.w k y := by
  intro y hy
  induction y, hy using Nat.le_induction with
  | base =>
    rw [D.Phi_of_le le_rfl]
    refine ⟨by simp [nu], ?_⟩
    simp only [Psi, Finset.range_zero, Finset.sum_empty, Phik]
    rw [Finset.sum_eq_zero]
    · simp
    intro u hu
    rw [D.N_of_le (by have := Finset.mem_range.mp hu; omega)]
    simp
  | succ y hy ih =>
    obtain ⟨ih1, ih2⟩ := ih
    have hs := Phi_succ D.n D.w y
    have hle : Phi D.n D.w y ≤ Phi D.n D.w (y + 1) := by omega
    have hN : 0 < Ncnt D.n D.w (y + 1) := D.N_pos (by omega)
    have hN' : (Ncnt D.n D.w (y + 1) : ℚ) ≠ 0 := by exact_mod_cast hN.ne'
    have hsl : ∀ j ∈ Ico (Phi D.n D.w y) (Phi D.n D.w (y + 1)), D.slope j = Ncnt D.n D.w (y + 1) := by
      intro j hj
      rw [Finset.mem_Ico] at hj
      exact D.slope_of_mem hj.1 hj.2
    have hdiff : Phi D.n D.w (y + 1) - Phi D.n D.w y = Ncnt D.n D.w (y + 1) := by omega
    constructor
    · have h := D.nu_sub hle
      rw [D.sum_inv_slope hsl, hdiff, mul_one_div_cancel hN'] at h
      push_cast
      linarith
    · have h := D.Psi_sub k hle
      rw [D.sum_min_slope k hsl, hdiff] at h
      have hc : (Ncnt D.n D.w (y + 1) : ℚ) * (min (Ncnt D.n D.w (y + 1) : ℚ) (k : ℚ) /
          (Ncnt D.n D.w (y + 1) : ℚ)) = min (Ncnt D.n D.w (y + 1) : ℚ) (k : ℚ) := by
        field_simp
      rw [hc] at h
      unfold Phik at ih2 ⊢
      rw [Finset.sum_range_succ]
      push_cast at ih2 ⊢
      linarith

/-- The rational inequality behind one step of the potential. -/
theorem step_arith (d D' k : ℕ) (δ : ℚ) (hd : 1 ≤ d) (hδ : (D' : ℚ) ≤ δ * d) :
    (D' : ℚ) ≤ ((D' + d - k : ℕ) : ℚ) + k / 4 * (1 + δ) := by
  have hd' : (1 : ℚ) ≤ d := by exact_mod_cast hd
  have hD0 : (0 : ℚ) ≤ D' := Nat.cast_nonneg _
  have hδ0 : 0 ≤ δ := by
    by_contra h; push Not at h
    have : δ * d < 0 := mul_neg_of_neg_of_pos h (by linarith)
    linarith
  have hk0 : (0 : ℚ) ≤ k := Nat.cast_nonneg _
  have h1 : ((D' : ℚ) + d) ≤ (1 + δ) * d := by linarith
  have hkδ : 0 ≤ (k : ℚ) * δ := mul_nonneg hk0 hδ0
  by_cases hkc : k ≤ D' + d
  · rw [Nat.cast_sub hkc]
    push_cast
    by_cases hkd : k ≤ d
    · have : (k : ℚ) ≤ d := by exact_mod_cast hkd
      linarith
    · push Not at hkd
      have hkd' : (d : ℚ) < k := by exact_mod_cast hkd
      have hkc' : (k : ℚ) ≤ D' + d := by exact_mod_cast hkc
      have h2 : (k : ℚ) * (D' + d) ≤ k * ((1 + δ) * d) := mul_le_mul_of_nonneg_left h1 hk0
      have h2' : (k : ℚ) * k ≤ k * (D' + d) := mul_le_mul_of_nonneg_left hkc' hk0
      have h3 : 4 * d * ((k : ℚ) - d) ≤ k * k := by nlinarith [sq_nonneg ((k : ℚ) - 2 * d)]
      have h4 : 4 * ((k : ℚ) - d) * d ≤ k * (1 + δ) * d := by nlinarith
      have h5 : 4 * ((k : ℚ) - d) ≤ k * (1 + δ) := le_of_mul_le_mul_right h4 (by linarith)
      linarith
  · push Not at hkc
    rw [Nat.sub_eq_zero_of_le hkc.le]
    push_cast
    have hkc' : ((D' : ℚ) + d) < k := by exact_mod_cast hkc
    have h2 : (k : ℚ) * (D' + d) ≤ k * ((1 + δ) * d) := mul_le_mul_of_nonneg_left h1 hk0
    have hc0 : (0 : ℚ) ≤ D' + d := by linarith
    have h2' : ((D' : ℚ) + d) * (D' + d) ≤ k * (D' + d) := mul_le_mul_of_nonneg_right hkc'.le hc0
    have h3 : 4 * d * (D' : ℚ) ≤ (D' + d) * (D' + d) := by nlinarith [sq_nonneg ((D' : ℚ) - d)]
    have h4 : 4 * (D' : ℚ) * d ≤ k * (1 + δ) * d := by nlinarith
    have h5 : 4 * (D' : ℚ) ≤ k * (1 + δ) := le_of_mul_le_mul_right h4 (by linarith)
    linarith

/-- One step of the worst-case process raises the potential by at most `(c - k)⁺ + (k / 4) (1 + Δ nu)`. -/
theorem psi_step (k B c : ℕ) :
    D.Psi k (D.gfun (B + c)) - D.Psi k B ≤
      ((c - k : ℕ) : ℚ) + k / 4 * (1 + D.nu (D.gfun (B + c)) - D.nu B) := by
  set x := B + c with hx
  set θ := D.mu x with hθ
  set B' := D.gfun x with hB'
  have hB'1 : B' ≤ Phi D.n D.w θ := min_le_right _ _
  have hB'2 : B' ≤ x - Ncnt D.n D.w θ := min_le_left _ _
  have hPθ : Phi D.n D.w θ ≤ x := D.Phi_mu_le x
  have hPθ1 : x < Phi D.n D.w (θ + 1) := D.lt_Phi_mu_succ x
  have hNP : Ncnt D.n D.w θ ≤ Phi D.n D.w θ := D.N_le_Phi θ
  have hk0 : (0 : ℚ) ≤ k := Nat.cast_nonneg _
  by_cases hBB : B' ≤ B
  · -- the potential does not rise; the level drops by at most one
    have hPsi := D.Psi_mono k hBB
    have hd : ∀ j ∈ Ico B' x, x - B' ≤ D.slope j := by
      intro j hj
      rw [Finset.mem_Ico] at hj
      by_cases hc : Phi D.n D.w θ ≤ x - Ncnt D.n D.w θ
      · have hB'eq : B' = Phi D.n D.w θ := min_eq_right hc
        have hj1 : θ ≤ D.mu j := D.le_mu (by omega)
        have := Ncnt_mono D.n D.w (show θ + 1 ≤ D.mu j + 1 by omega)
        have h3 := Phi_succ D.n D.w θ
        unfold slope
        omega
      · push Not at hc
        have hB'eq : B' = x - Ncnt D.n D.w θ := min_eq_left hc.le
        rcases Nat.eq_zero_or_pos θ with h0 | hpos
        · rw [h0, Ncnt_zero] at hB'eq
          omega
        · obtain ⟨θ', hθ'⟩ : ∃ θ', θ = θ' + 1 := ⟨θ - 1, by omega⟩
          have h3 := Phi_succ D.n D.w θ'
          rw [← hθ'] at h3
          have hj1 : θ' ≤ D.mu j := D.le_mu (by omega)
          have := Ncnt_mono D.n D.w (show θ ≤ D.mu j + 1 by omega)
          unfold slope
          omega
    have hsum : D.nu x - D.nu B' ≤ 1 := by
      rw [D.nu_sub (show B' ≤ x by omega)]
      rcases Nat.eq_zero_or_pos (x - B') with h0 | hpos
      · rw [Finset.Ico_eq_empty_of_le (by omega)]; simp
      · calc ∑ j ∈ Ico B' x, 1 / (D.slope j : ℚ) ≤ ∑ j ∈ Ico B' x, 1 / ((x - B' : ℕ) : ℚ) := by
              apply Finset.sum_le_sum
              intro j hj
              apply one_div_le_one_div_of_le (by exact_mod_cast hpos)
              exact_mod_cast hd j hj
          _ = 1 := by
              rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
              have : ((x - B' : ℕ) : ℚ) ≠ 0 := by exact_mod_cast hpos.ne'
              field_simp
    have hnux := D.nu_mono (show B ≤ x by omega)
    have hc0 : (0 : ℚ) ≤ ((c - k : ℕ) : ℚ) := Nat.cast_nonneg _
    have h1 : 0 ≤ 1 + D.nu B' - D.nu B := by linarith
    have := mul_nonneg (div_nonneg hk0 (by norm_num : (0 : ℚ) ≤ 4)) h1
    linarith
  · push Not at hBB
    -- the potential rises by at most the backlog increase, the level by at least that over the departures
    set d := x - B' with hdd
    have hslope : ∀ j ∈ Ico B B', D.slope j ≤ d := by
      intro j hj
      rw [Finset.mem_Ico] at hj
      have h1 : D.mu j < θ := D.mu_lt (by omega)
      have := Ncnt_mono D.n D.w (show D.mu j + 1 ≤ θ by omega)
      unfold slope
      omega
    have hd1 : 1 ≤ d := le_trans (D.slope_pos B) (hslope B (Finset.mem_Ico.mpr ⟨le_rfl, hBB⟩))
    have hPsi : D.Psi k B' - D.Psi k B ≤ ((B' - B : ℕ) : ℚ) := by
      rw [D.Psi_sub k hBB.le]
      calc ∑ j ∈ Ico B B', min (D.slope j : ℚ) (k : ℚ) / (D.slope j : ℚ) ≤ ∑ j ∈ Ico B B', (1 : ℚ) :=
            Finset.sum_le_sum (fun j _ => D.Psi_term_le_one k j)
        _ = ((B' - B : ℕ) : ℚ) := by simp
    have hnu : ((B' - B : ℕ) : ℚ) ≤ (D.nu B' - D.nu B) * d := by
      rw [D.nu_sub hBB.le, Finset.sum_mul]
      calc ((B' - B : ℕ) : ℚ) = ∑ j ∈ Ico B B', (1 : ℚ) := by simp
        _ ≤ ∑ j ∈ Ico B B', 1 / (D.slope j : ℚ) * d := by
          apply Finset.sum_le_sum
          intro j hj
          have hs := D.slope_pos j
          rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ (by exact_mod_cast hs), one_mul]
          exact_mod_cast hslope j hj
    have := step_arith d (B' - B) k (D.nu B' - D.nu B) hd1 hnu
    have hc : B' - B + d - k = c - k := by omega
    rw [hc] at this
    linarith

/-- Telescoping the step over the loading. -/
theorem psi_tele (k : ℕ) (c : ℕ → ℕ) (a₁ : ℕ) (hc : ∀ t < a₁, c t = 0) :
    ∀ t, a₁ ≤ t → D.Psi k (D.Bh c t) ≤
      ∑ s ∈ range t, ((c s - k : ℕ) : ℚ) + k / 4 * ((t - a₁ : ℕ) : ℚ) + k / 4 * (D.nu (D.Bh c t) - D.b₁) := by
  intro t ht
  induction t, ht using Nat.le_induction with
  | base =>
    rw [D.Bh_eq_zero c a₁ hc a₁ le_rfl]
    have : (0 : ℚ) ≤ ∑ s ∈ range a₁, ((c s - k : ℕ) : ℚ) := Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _)
    simp only [Psi, nu, Finset.range_zero, Finset.sum_empty, Nat.sub_self, Nat.cast_zero, mul_zero, add_zero,
      sub_self]
    linarith
  | succ t ht ih =>
    have h := D.psi_step k (D.Bh c t) (c t)
    rw [← D.Bh_succ] at h
    rw [Finset.sum_range_succ, show t + 1 - a₁ = (t - a₁) + 1 by omega]
    push_cast
    linarith

/-- The key inequality: `Phik k L ≤ E_k + R + (k / 4) (t* - a₁ + L - b₁)`. -/
theorem phik_le (k : ℕ) (c : ℕ → ℕ) (a₁ ts R : ℕ) (hc : ∀ t < a₁, c t = 0) (hts : a₁ ≤ ts) :
    (Phik D.n D.w k (D.mu (D.Bh c ts + R)) : ℚ) ≤
      ∑ s ∈ range ts, ((c s - k : ℕ) : ℚ) + R +
        k / 4 * (((ts - a₁ : ℕ) : ℚ) + ((D.mu (D.Bh c ts + R) - D.b₁ : ℕ) : ℚ)) := by
  have htele := D.psi_tele k c a₁ hc ts hts
  set Bs := D.Bh c ts with hBs
  set L := D.mu (Bs + R) with hL
  have hL1 : Phi D.n D.w L ≤ Bs + R := D.Phi_mu_le _
  have hL2 : Bs + R < Phi D.n D.w (L + 1) := D.lt_Phi_mu_succ _
  have hLb : D.b₁ ≤ L := D.b₁_le_mu _
  obtain ⟨hnuL, hPsiL⟩ := D.nu_Psi_Phi k L hLb
  have hE : (0 : ℚ) ≤ ∑ s ∈ range ts, ((c s - k : ℕ) : ℚ) :=
    Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _)
  have hk0 : (0 : ℚ) ≤ k := Nat.cast_nonneg _
  have hk4 : (0 : ℚ) ≤ k / 4 := by positivity
  have hcastL : ((L - D.b₁ : ℕ) : ℚ) = L - D.b₁ := by rw [Nat.cast_sub hLb]
  have hts0 : (0 : ℚ) ≤ ((ts - a₁ : ℕ) : ℚ) := Nat.cast_nonneg _
  have hR : (0 : ℚ) ≤ R := Nat.cast_nonneg _
  have hLb' : (D.b₁ : ℚ) ≤ L := by exact_mod_cast hLb
  rw [hcastL]
  by_cases hcase : Bs ≤ Phi D.n D.w L
  · have h1 : D.nu Bs ≤ L := by rw [← hnuL]; exact D.nu_mono hcase
    have h2 : D.Psi k (Phi D.n D.w L) ≤ D.Psi k (Bs + R) := D.Psi_mono k hL1
    have h3 := D.Psi_add_le k Bs R
    rw [hPsiL] at h2
    have h4 := mul_le_mul_of_nonneg_left (show D.nu Bs - D.b₁ ≤ L - D.b₁ by linarith) hk4
    linarith
  · push Not at hcase
    set N' := Ncnt D.n D.w (L + 1) with hN'
    have hs := Phi_succ D.n D.w L
    have hNpos : 0 < N' := D.N_pos (by omega)
    have hsl : ∀ j ∈ Ico (Phi D.n D.w L) Bs, D.slope j = N' := by
      intro j hj
      rw [Finset.mem_Ico] at hj
      exact D.slope_of_mem hj.1 (by omega)
    have hN'q : (N' : ℚ) ≠ 0 := by exact_mod_cast hNpos.ne'
    have hnuB : D.nu Bs = L + ((Bs - Phi D.n D.w L : ℕ) : ℚ) / N' := by
      have h := D.nu_sub hcase.le
      rw [D.sum_inv_slope hsl, hnuL, mul_one_div] at h
      linarith
    have hPsiB : D.Psi k Bs = Phik D.n D.w k L + ((Bs - Phi D.n D.w L : ℕ) : ℚ) * (min (N' : ℚ) (k : ℚ) / N') := by
      have h := D.Psi_sub k hcase.le
      rw [D.sum_min_slope k hsl, hPsiL] at h
      linarith
    rw [hnuB, hPsiB] at htele
    have hφ : (0 : ℚ) ≤ ((Bs - Phi D.n D.w L : ℕ) : ℚ) / N' := by positivity
    have hφ' : ((Bs - Phi D.n D.w L : ℕ) : ℚ) * (min (N' : ℚ) (k : ℚ) / N') = ((Bs - Phi D.n D.w L : ℕ) : ℚ) / N' * min (N' : ℚ) (k : ℚ) := by ring
    rw [hφ'] at htele
    by_cases hs4 : (k : ℚ) ≤ 4 * min (N' : ℚ) (k : ℚ)
    · have h5 := mul_le_mul_of_nonneg_left (show (k : ℚ) / 4 ≤ min (N' : ℚ) (k : ℚ) by linarith) hφ
      have h6 := mul_nonneg hk4 hts0
      linarith
    · push Not at hs4
      -- at most `min N' k` edges below level `L`, each with content at most `L - b₁`
      have hbound : Phik D.n D.w k L ≤ (L - D.b₁) * min N' k := by
        unfold Phik
        rw [← Finset.sum_range_add_sum_Ico _ hLb]
        rw [Finset.sum_eq_zero (s := range D.b₁)]
        · rw [zero_add]
          calc ∑ u ∈ Ico D.b₁ L, min (Ncnt D.n D.w (u + 1)) k ≤ ∑ u ∈ Ico D.b₁ L, min N' k := by
                apply Finset.sum_le_sum
                intro u hu
                rw [Finset.mem_Ico] at hu
                have := Ncnt_mono D.n D.w (show u + 1 ≤ L + 1 by omega)
                exact min_le_min this le_rfl
            _ = (L - D.b₁) * min N' k := by rw [Finset.sum_const, Nat.card_Ico, smul_eq_mul]
        · intro u hu
          rw [D.N_of_le (by have := Finset.mem_range.mp hu; omega)]
          simp
      have hb' : (Phik D.n D.w k L : ℚ) ≤ ((L : ℚ) - D.b₁) * min (N' : ℚ) (k : ℚ) := by
        have := (Nat.cast_le (α := ℚ)).mpr hbound
        push_cast [Nat.cast_sub hLb] at this
        exact this
      have h5 := mul_le_mul_of_nonneg_left (show min (N' : ℚ) (k : ℚ) ≤ k / 4 by linarith)
        (show (0 : ℚ) ≤ L - D.b₁ by linarith)
      have h6 := mul_nonneg hk4 hts0
      linarith

end BData

end PacketTwoLayer
