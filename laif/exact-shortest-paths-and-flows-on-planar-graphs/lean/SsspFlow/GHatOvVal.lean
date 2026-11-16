import SsspFlow.OverlapSum
import SsspFlow.GHatLevelState

/-!
# The lengths of the overlap sides of a level from local tests

Let every annulus of a list `Q` of annuli of a level, at its middle index, carry its range and its
two overlap bits, and let the corners of its component hold these values. For a side `σ` with its bit
set, let a distance `dA` from a visited corner `c` of that side be known at the corners of the
component. A corner `κ0(μ)` of the top annulus whose values say that `μ` lies on the side is a source
with value `dA`, and the least source value at the face of a corner is known there. A corner `κ1(μ)`
whose values say the same adds its own `dA`. By the sum of the overlap through `c`, this is `λ_μ`, and
every other corner gets `⊤`.

* `RotSystem.ovIn`: the test of an index for a side, from the range and the bits.
* `CutPath.Live.SideC`: the corners of a side.
* `CutPath.ovSrc`, `CutPath.ovTgt`: the values at the sources and at the targets.
* `CutPath.ovTgt_eq`: the value at every corner is the least `λ_μ` over the annuli of `Q` and the
  indices `μ` of the side whose corner `κ1(μ)` it is.
-/

set_option autoImplicit false

namespace SsspFlow

open FourColor
open scoped ENNReal

namespace RotSystem

/-- The test of an index `μ` for a side, from the range and indices `p` and the two bits `b`: the
bit of the side is set and `μ` lies on the side of the middle index, the middle index included and
the end of the range excluded. -/
def ovIn : Fin 2 → ℕ × ℕ × ℕ × ℕ → Bool × Bool → ℕ → Prop
  | 0 => fun p b μ => b.1 = true ∧ p.1 < μ ∧ μ ≤ (p.1 + p.2.1) / 2
  | 1 => fun p b μ => b.2 = true ∧ (p.1 + p.2.1) / 2 ≤ μ ∧ μ < p.2.1

/-- The bit of a side. -/
def ovBit : Fin 2 → Bool × Bool → Bool
  | 0 => fun b => b.1
  | 1 => fun b => b.2

theorem ovIn_bit {σ : Fin 2} {p : ℕ × ℕ × ℕ × ℕ} {b : Bool × Bool} {μ : ℕ} (h : ovIn σ p b μ) :
    ovBit σ b = true := by
  match σ, h with
  | 0, h => exact h.1
  | 1, h => exact h.1

theorem ovIn_range {σ : Fin 2} {p : ℕ × ℕ × ℕ × ℕ} {b : Bool × Bool} {μ : ℕ} (hp : p.1 + 2 ≤ p.2.1)
    (h : ovIn σ p b μ) : p.1 < μ ∧ μ < p.2.1 := by
  match σ, h with
  | 0, h => exact ⟨h.2.1, by have := h.2.2; omega⟩
  | 1, h => exact ⟨by have := h.2.1; omega, h.2.2⟩

/-- The test of a corner for a side: its values are below `M` and some index `μ` of its flags passes
the test of the side. -/
def ovTest (σ : Fin 2) (M : ℕ) (vT vS : ℕ∞) (kap : ℕ → Bool) : Prop :=
  vT < M ∧ vS < M ∧ ∃ μ, kap μ = true ∧ ovIn σ (decT vT.toNat) (decS vS.toNat) μ

universe u

variable {D : Type u} [Fintype D] [DecidableEq D] {R : RotSystem D}

namespace CutPath

variable {C : R.CutPath} {g : D → ℝ≥0∞}

/-- The corners of a side: those of the side of `κ0(x_a)` and those of the side of `κ0(x_b)`. -/
def Live.SideC {Γ : Finset (D × Bool)} (L : C.Live g Γ) : Fin 2 → D × Bool → Prop
  | 0 => L.CornerA
  | 1 => L.CornerB

open Classical in
/-- The value at a source corner: its capped distance if it passes the test with its flags of
`κ0`, `⊤` otherwise. -/
noncomputable def ovSrc (σ : Fin 2) (M : ℕ) (pT pS : D × Bool → ℕ∞) (k0 : D × Bool → ℕ → Bool)
    (dA : D × Bool → ℝ≥0∞) (z : D × Bool) : ℝ≥0∞ :=
  if ovTest σ M (pT z) (pS z) (k0 z) then min (dA z) M else ⊤

open Classical in
/-- The value at a target corner: the capped least source value at its face plus its capped
distance if it passes the test with its flags of `κ1`, `⊤` otherwise. -/
noncomputable def ovTgt (σ : Fin 2) (M : ℕ) (pT pS : D × Bool → ℕ∞) (k1 : D × Bool → ℕ → Bool)
    (fm dA : D × Bool → ℝ≥0∞) (y : D × Bool) : ℝ≥0∞ :=
  if ovTest σ M (pT y) (pS y) (k1 y) then min (fm y) M + min (dA y) M else ⊤

variable {hR : R.Planar} {hC : R.Connected} {hg : ∀ x, g (R.rev x) = g x}
  {Γ₀ : Finset (D × Bool)} {L₀ : C.Live g Γ₀} {j k : ℕ}

/-- The sum of the overlap through a visited corner of a side, for an index of the side. -/
theorem Live.ov_sum (hR : R.Planar) (hC : R.Connected) (hg : ∀ x, g (R.rev x) = g x)
    {Γ : Finset (D × Bool)} (L : C.Live g Γ) (σ : Fin 2) {i μ : ℕ} {q : List (D × Bool)}
    (hq : L.Shortest i q) {c : D × Bool} (hc : L.SideC σ c) (hv : L.Visits i q c)
    {p : ℕ × ℕ × ℕ × ℕ} {b : Bool × Bool} (hov : ovIn σ p b μ) (hi : i = (p.1 + p.2.1) / 2)
    (hxμ : L.xa ≤ μ) (hyμ : L.ya ≤ μ) (hμx : μ ≤ L.xb) (hμy : μ ≤ L.yb)
    (hxi : L.xa ≤ i) (hyi : L.ya ≤ i) (hix : i ≤ L.xb) (hiy : i ≤ L.yb) :
    (R.double.split Γ).walkDist (g ∘ Prod.fst) ((R.double.split Γ).tail (L.κ0 μ))
        ((R.double.split Γ).tail c) +
      (R.double.split Γ).walkDist (g ∘ Prod.fst) ((R.double.split Γ).tail c)
        ((R.double.split Γ).tail (L.κ1 μ)) = C.lamD g μ := by
  match σ, hc, hov with
  | 0, hc, hov => exact L.ov_sum_a hR hC hg hq hc hv hxμ hyμ (hi ▸ hov.2.2) hix hiy
  | 1, hc, hov => exact L.ov_sum_b hR hC hg hq hc hv hxi hyi (hi ▸ hov.2.1) hμx hμy

open Classical in
/-- **The values of a side at the corners.** -/
theorem ovTgt_eq (r : Run hR hC hg Γ₀ L₀ j k) (ℓ : ℕ) (σ : Fin 2) (M : ℕ)
    (hMl : ∀ t, t ≤ C.m → C.lamD g t < M)
    (Q : List ((Σ Γ' : Finset (D × Bool), C.Live g Γ') × ℕ)) (hQ : ∀ q ∈ Q, q.1 ∈ r.nodes ℓ)
    (hQu : ∀ q ∈ Q, ∀ q' ∈ Q, q.1 = q'.1 → q.2 = q'.2)
    (rng : (Σ Γ' : Finset (D × Bool), C.Live g Γ') × ℕ → ℕ × ℕ)
    (hmid : ∀ q ∈ Q, q.2 = ((rng q).1 + (rng q).2) / 2 ∧ (rng q).1 + 2 ≤ (rng q).2)
    (hin : ∀ q ∈ Q, ∀ μ, (rng q).1 < μ → μ < (rng q).2 → q.1.2.κ0 μ = L₀.κ0 μ ∧
      q.1.2.κ1 μ = L₀.κ1 μ ∧ q.1.2.xa ≤ μ ∧ q.1.2.ya ≤ μ ∧ μ ≤ q.1.2.xb ∧ μ ≤ q.1.2.yb)
    (pT pS : D × Bool → ℕ∞) (payT payS : (Σ Γ' : Finset (D × Bool), C.Live g Γ') × ℕ → ℕ)
    (hreg : ∀ q ∈ Q, ∀ z, (R.double.split q.1.1).toHypermap.gcomp (q.1.2.κ0 q.1.2.xa) z →
      pT z = payT q ∧ pS z = payS q)
    (hguard : ∀ z, pT z < M → pS z < M →
      ∃ q ∈ Q, (R.double.split q.1.1).toHypermap.gcomp (q.1.2.κ0 q.1.2.xa) z)
    (hpay : ∀ q ∈ Q, payT q < M ∧ payS q < M ∧ (decT (payT q)).1 = (rng q).1 ∧
      (decT (payT q)).2.1 = (rng q).2)
    (dA : D × Bool → ℝ≥0∞)
    (hbit : ∀ q ∈ Q, ovBit σ (decS (payS q)) = true → ∃ p c, q.1.2.Shortest q.2 p ∧
      q.1.2.SideC σ c ∧ q.1.2.Visits q.2 p c ∧
      ∀ z, (R.double.split q.1.1).toHypermap.gcomp (q.1.2.κ0 q.1.2.xa) z →
        min (dA z) M = min ((R.double.split q.1.1).walkDist (g ∘ Prod.fst)
          ((R.double.split q.1.1).tail c) ((R.double.split q.1.1).tail z)) M)
    (k0 k1 : D × Bool → ℕ → Bool) (hk0 : ∀ z t, k0 z t = true ↔ z = L₀.κ0 t)
    (hk1 : ∀ z t, k1 z t = true ↔ z = L₀.κ1 t) (fm : D × Bool → ℝ≥0∞)
    (hfm : ∀ y, min (fm y) M =
      min (⨅ z, ⨅ (_ : R.tail z.1 = R.tail y.1), ovSrc σ M pT pS k0 dA z) M) (y : D × Bool) :
    ovTgt σ M pT pS k1 fm dA y = ⨅ q ∈ Q, ⨅ μ, ⨅ (_ : ovIn σ (decT (payT q)) (decS (payS q)) μ),
      ⨅ (_ : y = q.1.2.κ1 μ), C.lamD g μ := by
  -- the test passes at the corners `κ0(μ)` and `κ1(μ)` of an annulus of `Q` for an index of the side
  have pass : ∀ q ∈ Q, ∀ μ, ovIn σ (decT (payT q)) (decS (payS q)) μ →
      ovTest σ M (pT (q.1.2.κ0 μ)) (pS (q.1.2.κ0 μ)) (k0 (q.1.2.κ0 μ)) ∧
        ovTest σ M (pT (q.1.2.κ1 μ)) (pS (q.1.2.κ1 μ)) (k1 (q.1.2.κ1 μ)) := by
    intro q hq μ hov
    have hr := ovIn_range (by rw [(hpay q hq).2.2.1, (hpay q hq).2.2.2]; exact (hmid q hq).2) hov
    rw [(hpay q hq).2.2.1, (hpay q hq).2.2.2] at hr
    obtain ⟨e0, e1, h1, h2, h3, h4⟩ := hin q hq μ hr.1 hr.2
    obtain ⟨a0, b0⟩ := hreg q hq _ (q.1.2.gcomp_κ0 h1 h3)
    obtain ⟨a1, b1⟩ := hreg q hq _ (q.1.2.gcomp_κ1 h2 h4)
    have hT : ((payT q : ℕ) : ℕ∞) < M := by exact_mod_cast (hpay q hq).1
    have hS : ((payS q : ℕ) : ℕ∞) < M := by exact_mod_cast (hpay q hq).2.1
    refine ⟨⟨a0 ▸ hT, b0 ▸ hS, μ, (hk0 _ _).2 e0, ?_⟩, ⟨a1 ▸ hT, b1 ▸ hS, μ, (hk1 _ _).2 e1, ?_⟩⟩
    · rw [a0, b0, ENat.toNat_coe, ENat.toNat_coe]; exact hov
    · rw [a1, b1, ENat.toNat_coe, ENat.toNat_coe]; exact hov
  -- a corner that passes the test lies in an annulus of `Q` at an index of the side
  have back : ∀ z (κ : C.Live g Γ₀ → ℕ → D × Bool) (kap : D × Bool → ℕ → Bool),
      (∀ t, kap z t = true ↔ z = κ L₀ t) → ovTest σ M (pT z) (pS z) (kap z) →
      ∃ q ∈ Q, (R.double.split q.1.1).toHypermap.gcomp (q.1.2.κ0 q.1.2.xa) z ∧
        ∃ μ, ovIn σ (decT (payT q)) (decS (payS q)) μ ∧ z = κ L₀ μ := by
    intro z κ kap hkap ⟨hTz, hSz, μ, hkμ, hov⟩
    obtain ⟨q, hq, hz⟩ := hguard z hTz hSz
    obtain ⟨a, b⟩ := hreg q hq z hz
    rw [a, b, ENat.toNat_coe, ENat.toNat_coe] at hov
    exact ⟨q, hq, hz, μ, hov, (hkap μ).1 hkμ⟩
  -- the range and the corners at an index of the side
  have facts : ∀ q ∈ Q, ∀ μ, ovIn σ (decT (payT q)) (decS (payS q)) μ →
      μ ≤ C.m ∧ q.1.2.κ0 μ = L₀.κ0 μ ∧ q.1.2.κ1 μ = L₀.κ1 μ ∧ q.1.2.xa ≤ μ ∧ q.1.2.ya ≤ μ ∧
        μ ≤ q.1.2.xb ∧ μ ≤ q.1.2.yb := by
    intro q hq μ hov
    have hr := ovIn_range (by rw [(hpay q hq).2.2.1, (hpay q hq).2.2.2]; exact (hmid q hq).2) hov
    rw [(hpay q hq).2.2.1, (hpay q hq).2.2.2] at hr
    obtain ⟨e0, e1, h1, h2, h3, h4⟩ := hin q hq μ hr.1 hr.2
    exact ⟨h3.trans q.1.2.xb_le, e0, e1, h1, h2, h3, h4⟩
  by_cases hT : ovTest σ M (pT y) (pS y) (k1 y)
  · unfold ovTgt
    rw [if_pos hT]
    obtain ⟨q, hq, hyq, μ, hov, rfl⟩ := back y Live.κ1 k1 (hk1 y) hT
    obtain ⟨hμm, e0, e1, h1, h2, h3, h4⟩ := facts q hq μ hov
    -- the right side is `λ_μ`
    have hrhs : (⨅ q' ∈ Q, ⨅ μ', ⨅ (_ : ovIn σ (decT (payT q')) (decS (payS q')) μ'),
        ⨅ (_ : L₀.κ1 μ = q'.1.2.κ1 μ'), C.lamD g μ') = C.lamD g μ := by
      refine le_antisymm (iInf₂_le_of_le q hq (iInf_le_of_le μ (iInf_le_of_le hov (iInf_le_of_le e1.symm le_rfl))))
        (le_iInf₂ fun q' hq' => le_iInf fun μ' => le_iInf fun hov' => le_iInf fun he => ?_)
      obtain ⟨hμm', -, e1', h1', h2', h3', h4'⟩ := facts q' hq' μ' hov'
      have hz' : (R.double.split q'.1.1).toHypermap.gcomp (q'.1.2.κ0 q'.1.2.xa) (L₀.κ1 μ) :=
        he ▸ q'.1.2.gcomp_κ1 h2' h4'
      have ea : q'.1 = q.1 := r.sep ℓ q'.1 (hQ q' hq') q.1 (hQ q hq) _ hz' (e1 ▸ q.1.2.gcomp_κ1 h2 h4)
      have eq : q' = q := Prod.ext ea (hQu q' hq' q hq ea)
      subst eq
      have hv : C.v μ = C.v μ' := by
        rw [← q'.1.2.tail_κ1 h2 h4, ← q'.1.2.tail_κ1 h2' h4', e1, he]
      rw [C.inj μ μ' hμm hμm' hv]
    rw [hrhs]
    obtain ⟨p, c, hsh, hsc, hvis, hdA⟩ := hbit q hq (ovIn_bit hov)
    -- the least source value at the face is the value at `κ0(μ)`
    have hface : (⨅ z, ⨅ (_ : R.tail z.1 = R.tail (L₀.κ1 μ).1), ovSrc σ M pT pS k0 dA z) =
        ovSrc σ M pT pS k0 dA (q.1.2.κ0 μ) := by
      refine le_antisymm (iInf₂_le_of_le _ ?_ le_rfl) (le_iInf₂ fun z hz => ?_)
      · rw [q.1.2.tail_κ0 h1 h3, ← e1, q.1.2.tail_κ1 h2 h4]
      · by_cases hTz : ovTest σ M (pT z) (pS z) (k0 z)
        · obtain ⟨q'', hq'', -, μ'', hov'', rfl⟩ := back z Live.κ0 k0 (hk0 z) hTz
          obtain ⟨hμm'', e0'', -, h1'', -, h3'', -⟩ := facts q'' hq'' μ'' hov''
          have hv : C.v μ'' = C.v μ := by
            rw [← q''.1.2.tail_κ0 h1'' h3'', ← q.1.2.tail_κ1 h2 h4, e0'', e1, hz]
          rw [C.inj μ'' μ hμm'' hμm hv, e0]
        · unfold ovSrc
          rw [if_neg hTz]
          exact le_top
    have hsrc : ovSrc σ M pT pS k0 dA (q.1.2.κ0 μ) = min (dA (q.1.2.κ0 μ)) M := by
      unfold ovSrc
      rw [if_pos (pass q hq μ hov).1]
    have hfy := hfm (L₀.κ1 μ)
    rw [hface, hsrc, min_assoc, min_self] at hfy
    rw [hfy, hdA _ (q.1.2.gcomp_κ0 h1 h3), ← e1, hdA _ (q.1.2.gcomp_κ1 h2 h4)]
    obtain ⟨hm, hlo⟩ := hmid q hq
    have hr := ovIn_range (by rw [(hpay q hq).2.2.1, (hpay q hq).2.2.2]; exact hlo) hov
    rw [(hpay q hq).2.2.1, (hpay q hq).2.2.2] at hr
    have hlo' : (rng q).1 < q.2 := by omega
    have hhi' : q.2 < (rng q).2 := by omega
    obtain ⟨-, -, i1, i2, i3, i4⟩ := hin q hq q.2 hlo' hhi'
    have hsum := q.1.2.ov_sum hR hC hg σ hsh hsc hvis hov
      (by rw [hm, (hpay q hq).2.2.1, (hpay q hq).2.2.2]) h1 h2 h3 h4 i1 i2 i3 i4
    rw [walkDist_comm _ (fun z => hg z.1)] at hsum
    have hlt := hMl μ hμm
    have hA : (R.double.split q.1.1).walkDist (g ∘ Prod.fst) ((R.double.split q.1.1).tail c)
        ((R.double.split q.1.1).tail (q.1.2.κ0 μ)) < M :=
      lt_of_le_of_lt (le_self_add.trans hsum.le) hlt
    have hB : (R.double.split q.1.1).walkDist (g ∘ Prod.fst) ((R.double.split q.1.1).tail c)
        ((R.double.split q.1.1).tail (q.1.2.κ1 μ)) < M :=
      lt_of_le_of_lt (le_add_self.trans hsum.le) hlt
    rw [min_eq_left hA.le, min_eq_left hB.le, hsum]
  · unfold ovTgt
    rw [if_neg hT]
    refine (iInf_eq_top.2 fun q => iInf_eq_top.2 fun hq => iInf_eq_top.2 fun μ =>
      iInf_eq_top.2 fun hov => iInf_eq_top.2 fun hy => ?_).symm
    subst hy
    exact absurd (pass q hq μ hov).2 hT

end CutPath

end RotSystem

end SsspFlow
