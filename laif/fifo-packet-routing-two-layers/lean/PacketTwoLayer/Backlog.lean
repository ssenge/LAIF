import Mathlib

/-!
# Levels and backlog in layer 2

Layer-2 edges `g < n` with transit times `w g`. For an integer `y`,
`Phi n w y = ∑_g (y - w g)⁺` and `Ncnt n w y = #{g : w g < y}`, so that `Phi (y + 1) = Phi y + Ncnt (y + 1)`.
For a backlog `x`, `mu x` is the largest `y` with `Phi y ≤ x`, and `gfun x = min (x - Ncnt θ) (Phi θ)` with
`θ = mu x` bounds the backlog one time step later.

A moment of the loading is described by the vector `q g` of packets on edge `g` that have not left yet. Its level
is `w g + q g`. The invariant `Inv` says that every backlogged edge has level at most one more than every edge.

* `inv_tick`, `inv_join`: the invariant survives a time step and a join to an edge of minimum level.
* `mu_bl`: under the invariant, the minimum level is `mu` of the backlog.
* `bl_tick`: under the invariant, the backlog after one time step is at most `gfun` of the backlog.
* `gfun_mono`, `mu_mono`: both maps are monotone.

`Eqm` collects the structure of an equilibrium: layer-1 arrivals are sequential best responses, and in layer 2 the
players are served in index order and each one picks an edge of minimum latency. `makespan_le_Chat` bounds the
arrival of every player by `t* + mu (Bh c t* + c t*)`, where `Bh` is the worst-case backlog process
`Bh (t + 1) = gfun (Bh t + c t)` driven by the numbers `c t` of players that reach `v₁` at time `t`.
-/

namespace PacketTwoLayer

open Finset

/-- `Phi n w y = ∑_{g < n} (y - w g)⁺`. -/
def Phi (n : ℕ) (w : ℕ → ℕ) (y : ℕ) : ℕ := ∑ g ∈ range n, (y - w g)

/-- `Ncnt n w y = #{g < n : w g < y}`. -/
def Ncnt (n : ℕ) (w : ℕ → ℕ) (y : ℕ) : ℕ := ((range n).filter (fun g => w g < y)).card

/-- `Phik n w k y = ∑_{u < y} min (#{g : w g ≤ u}) k`, the content of the `k` shortest edges up to level `y`. -/
def Phik (n : ℕ) (w : ℕ → ℕ) (k y : ℕ) : ℕ := ∑ u ∈ range y, min (Ncnt n w (u + 1)) k

section Generic

variable (n : ℕ) (w : ℕ → ℕ)

theorem Phi_succ (y : ℕ) : Phi n w (y + 1) = Phi n w y + Ncnt n w (y + 1) := by
  unfold Phi Ncnt
  rw [Finset.card_filter, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro g _
  split_ifs <;> omega

theorem Phi_zero : Phi n w 0 = 0 := by simp [Phi]

theorem Phi_eq_sum (y : ℕ) : Phi n w y = ∑ u ∈ range y, Ncnt n w (u + 1) := by
  induction y with
  | zero => simp [Phi_zero]
  | succ y ih => rw [Phi_succ, ih, Finset.sum_range_succ]

theorem Ncnt_mono {y y' : ℕ} (h : y ≤ y') : Ncnt n w y ≤ Ncnt n w y' := by
  unfold Ncnt
  apply Finset.card_le_card
  intro g
  simp only [Finset.mem_filter]
  intro hg; exact ⟨hg.1, by omega⟩

theorem Phi_mono {y y' : ℕ} (h : y ≤ y') : Phi n w y ≤ Phi n w y' := by
  unfold Phi
  apply Finset.sum_le_sum
  intro g _; omega

theorem Ncnt_zero : Ncnt n w 0 = 0 := by simp [Ncnt]

theorem Ncnt_le_card (y : ℕ) : Ncnt n w y ≤ n := by
  unfold Ncnt
  calc _ ≤ (range n).card := Finset.card_filter_le _ _
    _ = n := Finset.card_range n

end Generic

/-- Data of layer 2: `n` edges with transit times `w`, the shortest transit time `b₁ = w g₀`. -/
structure BData where
  n : ℕ
  w : ℕ → ℕ
  b₁ : ℕ
  g₀ : ℕ
  hg₀ : g₀ < n
  hw₀ : w g₀ = b₁
  hw : ∀ g < n, b₁ ≤ w g

namespace BData

variable (D : BData)

theorem Phi_of_le {y : ℕ} (h : y ≤ D.b₁) : Phi D.n D.w y = 0 := by
  unfold Phi
  apply Finset.sum_eq_zero
  intro g hg
  have := D.hw g (Finset.mem_range.mp hg)
  omega

theorem N_of_le {y : ℕ} (h : y ≤ D.b₁) : Ncnt D.n D.w y = 0 := by
  unfold Ncnt
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro g hg
  have := D.hw g (Finset.mem_range.mp hg)
  omega

theorem N_pos {y : ℕ} (h : D.b₁ < y) : 0 < Ncnt D.n D.w y := by
  unfold Ncnt
  apply Finset.card_pos.mpr
  exact ⟨D.g₀, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr D.hg₀, by rw [D.hw₀]; exact h⟩⟩

theorem Phi_ge (y : ℕ) : y - D.b₁ ≤ Phi D.n D.w y := by
  unfold Phi
  have := Finset.single_le_sum (f := fun g => y - D.w g) (fun g _ => Nat.zero_le _)
    (Finset.mem_range.mpr D.hg₀)
  simp only [D.hw₀] at this
  exact this

/-- `mu x`: the largest `y` with `Phi y ≤ x`. -/
def mu (x : ℕ) : ℕ := Nat.findGreatest (fun y => Phi D.n D.w y ≤ x) (x + D.b₁)

theorem Phi_mu_le (x : ℕ) : Phi D.n D.w (D.mu x) ≤ x := by
  have h0 : Phi D.n D.w 0 ≤ x := by rw [Phi_zero]; exact Nat.zero_le _
  exact Nat.findGreatest_spec (P := fun y => Phi D.n D.w y ≤ x) (Nat.zero_le _) h0

theorem lt_Phi_mu_succ (x : ℕ) : x < Phi D.n D.w (D.mu x + 1) := by
  by_contra h
  push Not at h
  by_cases hb : D.mu x + 1 ≤ x + D.b₁
  · have := Nat.le_findGreatest (P := fun y => Phi D.n D.w y ≤ x) hb h
    unfold mu at this
    omega
  · have := D.Phi_ge (D.mu x + 1)
    omega

theorem b₁_le_mu (x : ℕ) : D.b₁ ≤ D.mu x := by
  have h0 : Phi D.n D.w D.b₁ ≤ x := by rw [D.Phi_of_le le_rfl]; exact Nat.zero_le _
  exact Nat.le_findGreatest (P := fun y => Phi D.n D.w y ≤ x) (by omega) h0

theorem le_mu {x y : ℕ} (h : Phi D.n D.w y ≤ x) : y ≤ D.mu x := by
  by_contra hc
  push Not at hc
  have := Phi_mono D.n D.w (show D.mu x + 1 ≤ y by omega)
  have := D.lt_Phi_mu_succ x
  omega

theorem mu_lt {x y : ℕ} (h : x < Phi D.n D.w y) : D.mu x < y := by
  by_contra hc
  push Not at hc
  have := Phi_mono D.n D.w hc
  have := D.Phi_mu_le x
  omega

theorem mu_eq {x θ : ℕ} (h1 : Phi D.n D.w θ ≤ x) (h2 : x < Phi D.n D.w (θ + 1)) : D.mu x = θ :=
  le_antisymm (Nat.lt_succ_iff.mp (D.mu_lt h2)) (D.le_mu h1)

theorem mu_mono {x x' : ℕ} (h : x ≤ x') : D.mu x ≤ D.mu x' :=
  D.le_mu (le_trans (D.Phi_mu_le x) h)

/-- The backlog bound one time step later. -/
def gfun (x : ℕ) : ℕ := min (x - Ncnt D.n D.w (D.mu x)) (Phi D.n D.w (D.mu x))

theorem gfun_zero : D.gfun 0 = 0 := by simp [gfun]

theorem N_le_Phi (θ : ℕ) : Ncnt D.n D.w θ ≤ Phi D.n D.w θ := by
  rcases θ with _ | θ
  · simp [Ncnt_zero]
  · have := Phi_succ D.n D.w θ
    omega

theorem gfun_mono {x x' : ℕ} (h : x ≤ x') : D.gfun x ≤ D.gfun x' := by
  have hθ := D.mu_mono h
  have h3 := D.Phi_mu_le x'
  unfold gfun
  rcases Nat.eq_or_lt_of_le hθ with he | hlt
  · rw [he]; omega
  · obtain ⟨θ, hθ'⟩ : ∃ θ, D.mu x' = θ + 1 := ⟨D.mu x' - 1, by omega⟩
    have h1 : Phi D.n D.w (D.mu x) ≤ Phi D.n D.w θ := Phi_mono D.n D.w (by omega)
    have h2 := Phi_succ D.n D.w θ
    rw [hθ'] at h3 ⊢
    omega

/-! ### The vector state -/

/-- Every backlogged edge has level at most one more than every edge. -/
def Inv (q : ℕ → ℕ) : Prop := ∀ g < D.n, ∀ g' < D.n, 0 < q g → D.w g + q g ≤ D.w g' + q g' + 1

/-- The backlog. -/
def bl (q : ℕ → ℕ) : ℕ := ∑ g ∈ range D.n, q g

/-- A join to edge `g₀`. -/
def join (q : ℕ → ℕ) (g₀ : ℕ) : ℕ → ℕ := fun g => if g = g₀ then q g + 1 else q g

theorem inv_zero : D.Inv (fun _ => 0) := fun _ _ _ _ h => absurd h (lt_irrefl 0)

theorem inv_tick {q : ℕ → ℕ} (h : D.Inv q) : D.Inv (fun g => q g - 1) := by
  intro g hg g' hg' hpos
  simp only at hpos ⊢
  have := h g hg g' hg' (by omega)
  omega

theorem inv_join {q : ℕ → ℕ} (h : D.Inv q) {g₀ : ℕ} (hmin : ∀ g' < D.n, D.w g₀ + q g₀ ≤ D.w g' + q g') :
    D.Inv (BData.join q g₀) := by
  intro g hg g' hg' hpos
  have hmg' := hmin g' hg'
  have hgg' : 0 < q g → D.w g + q g ≤ D.w g' + q g' + 1 := h g hg g' hg'
  simp only [join] at hpos ⊢
  split_ifs at hpos ⊢ <;> subst_vars <;> omega

theorem bl_join (q : ℕ → ℕ) {g₀ : ℕ} (hg₀ : g₀ < D.n) : D.bl (BData.join q g₀) = D.bl q + 1 := by
  unfold bl join
  have : ∀ g ∈ range D.n, (if g = g₀ then q g + 1 else q g) = q g + if g = g₀ then 1 else 0 := by
    intro g _; split_ifs <;> rfl
  rw [Finset.sum_congr rfl this, Finset.sum_add_distrib, Finset.sum_ite_eq']
  simp [hg₀]

/-- Under the invariant, the minimum level is `mu` of the backlog. -/
theorem mu_bl {q : ℕ → ℕ} (h : D.Inv q) {g₀ : ℕ} (hg₀ : g₀ < D.n)
    (hmin : ∀ g' < D.n, D.w g₀ + q g₀ ≤ D.w g' + q g') : D.mu (D.bl q) = D.w g₀ + q g₀ := by
  apply D.mu_eq
  · unfold Phi bl
    apply Finset.sum_le_sum
    intro g hg
    have := hmin g (Finset.mem_range.mp hg)
    omega
  · unfold Phi bl
    apply Finset.sum_lt_sum
    · intro g hg
      by_cases hq : 0 < q g
      · have := h g (Finset.mem_range.mp hg) g₀ hg₀ hq
        omega
      · omega
    · exact ⟨g₀, Finset.mem_range.mpr hg₀, by omega⟩

/-- Under the invariant, the backlog one time step later is at most `gfun` of the backlog. -/
theorem bl_tick {q : ℕ → ℕ} (h : D.Inv q) : D.bl (fun g => q g - 1) ≤ D.gfun (D.bl q) := by
  obtain ⟨g₀, hg₀, hmin⟩ := Finset.exists_min_image (range D.n) (fun g => D.w g + q g)
    ⟨D.g₀, Finset.mem_range.mpr D.hg₀⟩
  have hmin' : ∀ g' < D.n, D.w g₀ + q g₀ ≤ D.w g' + q g' :=
    fun g' hg' => hmin g' (Finset.mem_range.mpr hg')
  have hg₀' := Finset.mem_range.mp hg₀
  have hθ := D.mu_bl h hg₀' hmin'
  unfold gfun
  rw [hθ]
  apply le_min
  · -- the edges below the minimum level are backlogged
    have hsplit : D.bl (fun g => q g - 1) + ((range D.n).filter (fun g => 0 < q g)).card = D.bl q := by
      unfold bl
      rw [Finset.card_filter, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro g _; split_ifs <;> omega
    have hsub : Ncnt D.n D.w (D.w g₀ + q g₀) ≤ ((range D.n).filter (fun g => 0 < q g)).card := by
      unfold Ncnt
      apply Finset.card_le_card
      intro g
      simp only [Finset.mem_filter, Finset.mem_range]
      intro ⟨hg, hlt⟩
      have := hmin' g hg
      exact ⟨hg, by omega⟩
    omega
  · unfold bl Phi
    apply Finset.sum_le_sum
    intro g hg
    by_cases hq : 0 < q g
    · have := h g (Finset.mem_range.mp hg) g₀ hg₀' hq
      omega
    · omega

/-- The worst-case backlog process driven by the arrival numbers `c`. -/
def Bh (c : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | t + 1 => D.gfun (Bh c t + c t)

theorem Bh_succ (c : ℕ → ℕ) (t : ℕ) : D.Bh c (t + 1) = D.gfun (D.Bh c t + c t) := rfl

theorem Bh_eq_zero (c : ℕ → ℕ) (a₁ : ℕ) (hc : ∀ t < a₁, c t = 0) : ∀ t ≤ a₁, D.Bh c t = 0 := by
  intro t ht
  induction t with
  | zero => rfl
  | succ t ih => rw [Bh_succ, ih (by omega), hc t (by omega), Nat.add_zero, D.gfun_zero]

end BData

/-! ### Equilibrium structure -/

/-- Number of players `j < i` on edge `x`. -/
def cnt (e : ℕ → ℕ) (i x : ℕ) : ℕ := ((range i).filter (fun j => e j = x)).card

theorem cnt_succ (e : ℕ → ℕ) (i x : ℕ) : cnt e (i + 1) x = cnt e i x + if e i = x then 1 else 0 := by
  unfold cnt
  rw [Finset.range_add_one, Finset.filter_insert]
  split_ifs with h
  · rw [Finset.card_insert_of_notMem (by simp)]
  · rfl

theorem cnt_mono (e : ℕ → ℕ) {i j : ℕ} (h : i ≤ j) (x : ℕ) : cnt e i x ≤ cnt e j x := by
  unfold cnt
  apply Finset.card_le_card
  intro y; simp only [Finset.mem_filter, Finset.mem_range]; intro hy; exact ⟨by omega, hy.2⟩

theorem exists_of_lt_cnt (e : ℕ → ℕ) (x : ℕ) :
    ∀ m r, r < cnt e m x → ∃ j < m, e j = x ∧ cnt e j x = r := by
  intro m
  induction m with
  | zero => intro r h; simp [cnt] at h
  | succ m ih =>
    intro r h
    rw [cnt_succ] at h
    by_cases hr : r < cnt e m x
    · obtain ⟨j, hj, h1, h2⟩ := ih r hr
      exact ⟨j, by omega, h1, h2⟩
    · split_ifs at h with he
      · exact ⟨m, by omega, he, by omega⟩
      · omega

theorem alpha_mono_of {n nA : ℕ} {aF e α : ℕ → ℕ} (e_lt : ∀ i < n, e i < nA)
    (α_eq : ∀ i < n, α i = aF (e i) + cnt e i (e i)) (α_le : ∀ i < n, ∀ x < nA, α i ≤ aF x + cnt e i x)
    {i j : ℕ} (hij : i ≤ j) (hj : j < n) : α i ≤ α j := by
  induction j, hij using Nat.le_induction with
  | base => exact le_rfl
  | succ j hij ih =>
    have h1 := α_le j (by omega) (e (j + 1)) (e_lt (j + 1) hj)
    have h2 := α_eq (j + 1) hj
    have h3 := cnt_mono e (Nat.le_add_right j 1) (e (j + 1))
    have := ih (by omega)
    omega

/-- The structure of an equilibrium with `n` players. Layer 1 has `nA` edges with transit times `aF`, layer 2 is
`D`. Player `i` uses `(e i, f i)` and reaches `v₁` at `α i`; `NF i g` is the next free departure time of layer-2
edge `g` after the players `0, …, i - 1`. -/
structure Eqm (n nA : ℕ) (aF : ℕ → ℕ) (D : BData) (e f α : ℕ → ℕ) (NF : ℕ → ℕ → ℕ) : Prop where
  e_lt : ∀ i < n, e i < nA
  f_lt : ∀ i < n, f i < D.n
  α_eq : ∀ i < n, α i = aF (e i) + cnt e i (e i)
  α_le : ∀ i < n, ∀ x < nA, α i ≤ aF x + cnt e i x
  NF_zero : ∀ g, NF 0 g = 0
  NF_succ : ∀ i < n, ∀ g, NF (i + 1) g = if g = f i then max (α i) (NF i g) + 1 else NF i g
  lat : ∀ i < n, ∀ g < D.n, max (α i) (NF i (f i)) + D.w (f i) ≤ max (α i) (NF i g) + D.w g

/-- Per-edge backlog at the moment before player `i` at time `t`. -/
def qv (NF : ℕ → ℕ → ℕ) (i t : ℕ) : ℕ → ℕ := fun g => NF i g - t

/-- Number of players `j < i` that reach `v₁` at time `v`. -/
def ca (α : ℕ → ℕ) (i v : ℕ) : ℕ := ((range i).filter (fun j => α j = v)).card

theorem ca_succ (α : ℕ → ℕ) (i v : ℕ) : ca α (i + 1) v = ca α i v + if α i = v then 1 else 0 := by
  unfold ca
  rw [Finset.range_add_one, Finset.filter_insert]
  split_ifs with h
  · rw [Finset.card_insert_of_notMem (by simp)]
  · rfl

/-- The arrival time of player `i` at the sink. -/
def βv (D : BData) (f α : ℕ → ℕ) (NF : ℕ → ℕ → ℕ) (i : ℕ) : ℕ := max (α i) (NF i (f i)) + D.w (f i)

namespace Eqm

variable {n nA : ℕ} {aF : ℕ → ℕ} {D : BData} {e f α : ℕ → ℕ} {NF : ℕ → ℕ → ℕ}
  (E : Eqm n nA aF D e f α NF)
include E

theorem α_mono {i j : ℕ} (hij : i ≤ j) (hj : j < n) : α i ≤ α j :=
  alpha_mono_of E.e_lt E.α_eq E.α_le hij hj

theorem q_tick (i t : ℕ) : qv NF i (t + 1) = fun g => qv NF i t g - 1 := by
  funext g; simp only [qv]; omega

theorem q_join {i : ℕ} (hi : i < n) : qv NF (i + 1) (α i) = BData.join (qv NF i (α i)) (f i) := by
  funext g
  simp only [qv, BData.join, E.NF_succ i hi g]
  split_ifs <;> omega

theorem q_min {i : ℕ} (hi : i < n) :
    ∀ g' < D.n, D.w (f i) + qv NF i (α i) (f i) ≤ D.w g' + qv NF i (α i) g' := by
  intro g' hg'
  have := E.lat i hi g' hg'
  simp only [qv]
  omega

theorem inv_ticks (i s : ℕ) (h : D.Inv (qv NF i s)) : ∀ t, s ≤ t → D.Inv (qv NF i t) := by
  intro t hst
  induction t, hst using Nat.le_induction with
  | base => exact h
  | succ t _ ih => rw [E.q_tick]; exact D.inv_tick ih

/-- The invariant holds at every moment. -/
theorem inv_q : ∀ i ≤ n, ∀ t, (∀ j < i, α j ≤ t) → D.Inv (qv NF i t) := by
  intro i
  induction i with
  | zero =>
    intro _ t _
    intro g _ g' _ hpos
    simp [qv, E.NF_zero] at hpos
  | succ i ih =>
    intro hi t ht
    have h1 : D.Inv (qv NF i (α i)) := ih (by omega) (α i) (fun j hj => E.α_mono (by omega) (by omega))
    have h2 : D.Inv (qv NF (i + 1) (α i)) := by
      rw [E.q_join (by omega)]; exact D.inv_join h1 (E.q_min (by omega))
    exact E.inv_ticks (i + 1) (α i) h2 t (ht i (by omega))

theorem ca_zero_of_lt {i v : ℕ} (hi : i < n) (h : α i < v) : ca α (i + 1) v = 0 := by
  unfold ca
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro j hj
  have := E.α_mono (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)) hi
  omega

/-- The backlog at each arrival is dominated by the worst-case process plus the earlier arrivals at the same time. -/
theorem bl_le_Bh {m : ℕ} (hm : m < n) :
    ∀ i ≤ m, D.bl (qv NF i (α i)) ≤ D.Bh (ca α m) (α i) + ca α i (α i) := by
  intro i
  induction i with
  | zero =>
    intro _
    have : D.bl (qv NF 0 (α 0)) = 0 := by
      unfold BData.bl; apply Finset.sum_eq_zero; intro g _; simp [qv, E.NF_zero]
    rw [this]; exact Nat.zero_le _
  | succ i ih =>
    intro hi
    have hin : i < n := by omega
    have IH := ih (by omega)
    have hx : D.bl (qv NF (i + 1) (α i)) = D.bl (qv NF i (α i)) + 1 := by
      rw [E.q_join hin, D.bl_join _ (E.f_lt i hin)]
    have hca := ca_succ α i (α i)
    rw [if_pos rfl] at hca
    have hmono := E.α_mono (Nat.le_add_right i 1) (show i + 1 < n by omega)
    rcases Nat.eq_or_lt_of_le hmono with heq | hlt
    · rw [← heq, hx, hca]; omega
    · -- all players with arrival `α i` come before `i + 1`
      have hcm : ca α (i + 1) (α i) = ca α m (α i) := by
        unfold ca
        congr 1
        ext j
        simp only [Finset.mem_filter, Finset.mem_range]
        constructor
        · intro ⟨hj, hj'⟩; exact ⟨by omega, hj'⟩
        · intro ⟨hj, hj'⟩
          refine ⟨?_, hj'⟩
          by_contra hc
          have := E.α_mono (show i + 1 ≤ j by omega) (by omega)
          omega
      have hxle : D.bl (qv NF (i + 1) (α i)) ≤ D.Bh (ca α m) (α i) + ca α m (α i) := by
        rw [hx, ← hcm, hca]; omega
      have hinv : ∀ s, α i ≤ s → D.Inv (qv NF (i + 1) s) := fun s hs =>
        E.inv_q (i + 1) (by omega) s (fun j hj => le_trans (E.α_mono (by omega) hin) hs)
      have key : ∀ s, α i + 1 ≤ s → s ≤ α (i + 1) → D.bl (qv NF (i + 1) s) ≤ D.Bh (ca α m) s := by
        intro s hs1
        induction s, hs1 using Nat.le_induction with
        | base =>
          intro _
          rw [E.q_tick, D.Bh_succ]
          exact le_trans (D.bl_tick (hinv (α i) le_rfl)) (D.gfun_mono hxle)
        | succ s hs ih2 =>
          intro hs2
          have hc0 : ca α m s = 0 := by
            unfold ca
            rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
            intro j hj hjs
            have hj' := Finset.mem_range.mp hj
            by_cases hji : j ≤ i
            · have := E.α_mono hji hin; omega
            · have := E.α_mono (show i + 1 ≤ j by omega) (by omega); omega
          rw [E.q_tick, D.Bh_succ, hc0, Nat.add_zero]
          exact le_trans (D.bl_tick (hinv s (by omega))) (D.gfun_mono (ih2 (by omega)))
      have := key (α (i + 1)) (by omega) le_rfl
      rw [E.ca_zero_of_lt hin hlt]
      omega

/-- The arrival of player `m` is at most `t* + mu (Bh t* + R)` with `t* = α m` and `R` the earlier arrivals at
`t*`. -/
theorem β_le {m : ℕ} (hm : m < n) :
    βv D f α NF m ≤ α m + D.mu (D.Bh (ca α m) (α m) + ca α m (α m)) := by
  have hinv := E.inv_q m hm.le (α m) (fun j hj => E.α_mono hj.le hm)
  have hmu := D.mu_bl hinv (E.f_lt m hm) (E.q_min hm)
  have hb := E.bl_le_Bh hm m le_rfl
  have := D.mu_mono hb
  have hq : qv NF m (α m) (f m) = NF m (f m) - α m := rfl
  rw [hq] at hmu
  unfold βv
  omega

end Eqm

end PacketTwoLayer
