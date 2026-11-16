import SsspFlow.GHatLevelEnds
import SsspFlow.MinFlood

/-!
# Theorem D as one algorithm of the message model

Every node starts with its stored state of level `0` of the recursion on a shortest cut path. The
algorithm runs the lengths at the two ends (`levelEnds_local`), then `2 log n` repetitions of the
levels with their values (`levelLoop_local`), caps the least value of each node at `M`, and floods
the minimum for `D` rounds (`minFlood`). A cut path has fewer than `n²` indices, so `2 log n` levels
cover every index the recursion computes (`CutPath.Run.loc_deep`). Every node then holds the least
computed length `v`, and `v / K` is the minimum `st`-cut (`theoremD_correct`).

* `RData.cutPath_m_lt`: `m + 1 ≤ n²` for a cut path of the dual of a network on `n` nodes.
* `RData.theoremD_local`: the algorithm, its rounds and its output.
-/

set_option autoImplicit false

namespace SsspFlow

open FourColor SsspFlow.Congest
open scoped ENNReal

namespace RotSystem

namespace RData

/-- A cut path of the dual of a network on `n` nodes has at most `n²` vertices. -/
theorem cutPath_m_lt {n : ℕ} {N : Net (Fin n)} (Cp : N.toRot.dual.CutPath) : Cp.m + 1 ≤ n * n := by
  have h1 : Fintype.card (Fin (Cp.m + 1)) ≤ Fintype.card N.G.Dart :=
    Fintype.card_le_of_injective (fun t : Fin (Cp.m + 1) => (Cp.v t).out) fun a b h =>
      Fin.ext (Cp.inj a b (Nat.lt_succ_iff.1 a.2) (Nat.lt_succ_iff.1 b.2) (Quotient.out_inj.1 h))
  have h2 : Fintype.card N.G.Dart ≤ Fintype.card (Fin n × Fin n) :=
    Fintype.card_le_of_injective _ SimpleGraph.Dart.toProd_injective
  simp only [Fintype.card_fin, Fintype.card_prod] at h1 h2
  omega

open Classical Cslib.Congest.Algorithm in
/-- **Theorem D as one algorithm.** Let the dual map be planar and connected, the capacities `c₀`
agree on the two darts of an edge, `K₀` exceed the number of darts, the cut path be shortest for the
lengths `K₀ c₀ + 1`, and the cut duality hold. Every node starts with its stored state of level `0`.
After `T ≤ (2 log n + 1)(110 + 68 C log^c n' · (12 D + 16)) + D` rounds, with messages of
`O(log^c n')` bits, every node holds a number `v` with `v / K₀` the minimum `st`-cut. -/
theorem theoremD_local (hE : ExactSsspBound) (K : ℕ) : ∃ C c : ℕ, ∀ n D : ℕ,
    ∃ (σ : Type) (A : Cslib.Congest.Algorithm (Fin n) (LvX n) σ
        (4 * (C * logN (n * (n * 21)) ^ c + 3) + (3 * (K * logN (n * (n * 21)) + 1) + 5)))
      (T : ℕ) (out : Fin n → σ → ℕ),
    T ≤ (2 * logN n + 1) * (110 + 68 * (C * logN (n * (n * 21)) ^ c * (12 * D + 16))) + D ∧
    ∀ (N : Net (Fin n)) (hN : ∀ u, ∃ w, N.G.Adj u w) (Cp : N.toRot.dual.CutPath) (c₀ : N.G.Dart → ℕ)
      (K₀ : ℕ) (hR : N.toRot.dual.Planar) (hC : N.toRot.dual.Connected)
      (hgc : ∀ x, (Nat.cast ∘ (fun x => K₀ * c₀ x + 1) : N.G.Dart → ℝ≥0∞) (N.toRot.dual.rev x) =
        (Nat.cast ∘ (fun x => K₀ * c₀ x + 1)) x)
      (modeL hostT : N.G.Dart → Bool) (hhost : ∀ d, hostT (N.toRot.rev d) = !hostT d) (M : ℕ)
      (X₀ : Fin n → LvX n) (w₀ : Fin n),
      N.toRot.Planar → N.toRot.Connected → N.DiamLE D → CutDuality N.G.Dart →
      (∀ d, c₀ (N.toRot.rev d) = c₀ d) → Fintype.card N.G.Dart < K₀ →
      (∀ q, N.toRot.dual.IsWalk (Cp.v 0) q (Cp.v Cp.m) →
        Cp.pos (fun x => K₀ * c₀ x + 1) Cp.m ≤ (q.map fun x => K₀ * c₀ x + 1).sum) →
      (∀ d, K₀ * c₀ d + 1 ≤ (n * (n * 21) + 2) ^ K) → M ≤ (n * (n * 21) + 2) ^ K →
      (∀ t, t ≤ Cp.m → Cp.lamD (Nat.cast ∘ fun x => K₀ * c₀ x + 1) t < M) → (Cp.m + 2) ^ 8 ≤ M →
      (∃ r₀ : CutPath.Run hR hC hgc Cp.Γ (Cp.liveOne (Nat.cast ∘ fun x => K₀ * c₀ x + 1)) 0 Cp.m,
        LvInv hN modeL hostT hhost hE K D M r₀ w₀ 0 X₀) →
      ∀ w, IsLeast (N.toRot.cutVals c₀ (N.toRot.tail Cp.cs) (N.toRot.tail Cp.ct))
        (out w (A.run N.G X₀ T w) / K₀) := by
  obtain ⟨C₁, c₁, hEn⟩ := levelEnds_local hE K
  obtain ⟨C₂, c₂, hLp⟩ := levelLoop_local hE K
  refine ⟨C₁ + C₂, c₁ + c₂, fun n D => ?_⟩
  obtain ⟨σ₁, A₁, T₁, voE, hT₁, hA₁⟩ := hEn n D
  obtain ⟨σ₂, A₂, T₂, xI, ac, hT0, hT₂, hA₂⟩ := hLp n D
  have hL : 1 ≤ logN (n * (n * 21)) := by unfold logN; omega
  have hp₁ : logN (n * (n * 21)) ^ c₁ ≤ logN (n * (n * 21)) ^ (c₁ + c₂) := Nat.pow_le_pow_right hL (by omega)
  have hp₂ : logN (n * (n * 21)) ^ c₂ ≤ logN (n * (n * 21)) ^ (c₁ + c₂) := Nat.pow_le_pow_right hL (by omega)
  have hm₁ := Nat.mul_le_mul (show C₁ ≤ C₁ + C₂ by omega) hp₁
  have hm₂ := Nat.mul_le_mul (show C₂ ≤ C₁ + C₂ by omega) hp₂
  have w₁ : 4 * (C₁ * logN (n * (n * 21)) ^ c₁) + (3 * (K * logN (n * (n * 21)) + 1) + 5) ≤
      4 * ((C₁ + C₂) * logN (n * (n * 21)) ^ (c₁ + c₂) + 3) + (3 * (K * logN (n * (n * 21)) + 1) + 5) := by omega
  have w₂ : 4 * (C₂ * logN (n * (n * 21)) ^ c₂ + 3) + (3 * (K * logN (n * (n * 21)) + 1) + 5) ≤
      4 * ((C₁ + C₂) * logN (n * (n * 21)) ^ (c₁ + c₂) + 3) + (3 * (K * logN (n * (n * 21)) + 1) + 5) := by omega
  let P₁ := (A₁.widen w₁).keep (fun _ (x : LvX n) => x)
  let P₂ := (A₂.widen w₂).keep (fun _ (y : LvX n × ℕ∞) => y.1)
  let P₁₂ := P₁.seq T₁ (fun w s => (s.1, voE w s.2)) P₂
  let cap : Fin n → (ℕ × (LvX n × σ₁)) ⊕ ((LvX n × ℕ∞) × σ₂) → ℕ := fun w s => match s with
    | .inr p => (min ((p.1.1.1.bnd : ℕ) : ℕ∞) (min p.1.2 (ac w p.2))).toNat
    | .inl _ => 0
  refine ⟨_, P₁₂.seq (T₁ + 2 * logN n * T₂) cap (minFlood _), T₁ + 2 * logN n * T₂ + D,
    fun _ s => match s with
      | .inr p => p.1
      | .inl _ => 0, ?_, ?_⟩
  · have h : C₁ * logN (n * (n * 21)) ^ c₁ * (12 * D + 16) ≤ (C₁ + C₂) * logN (n * (n * 21)) ^ (c₁ + c₂) * (12 * D + 16) := Nat.mul_le_mul_right _ hm₁
    have h' : C₂ * logN (n * (n * 21)) ^ c₂ * (12 * D + 16) ≤ (C₁ + C₂) * logN (n * (n * 21)) ^ (c₁ + c₂) * (12 * D + 16) := Nat.mul_le_mul_right _ hm₂
    have hY : T₂ ≤ 110 + 68 * ((C₁ + C₂) * logN (n * (n * 21)) ^ (c₁ + c₂) * (12 * D + 16)) := by omega
    have hY' := Nat.mul_le_mul_left (2 * logN n) hY
    rw [add_mul, one_mul]
    omega
  intro N hN Cp c₀ K₀ hR hC hgc modeL hostT hhost M X₀ w₀ hP hc hD hDual hcr₀ hK hPath hcb hM hMl hM8 ⟨r₀, h0⟩ w
  have hc1 : ∀ d, 1 ≤ K₀ * c₀ d + 1 := fun _ => Nat.le_add_left _ _
  have hcr : ∀ d, K₀ * c₀ (N.toRot.rev d) + 1 = K₀ * c₀ d + 1 := fun d => by rw [hcr₀]
  have hS : ∀ ℓ, (lvS modeL hostT hhost (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ).NoConflict :=
    fun ℓ => CutPath.Run.noConflict _ ℓ modeL hostT _
  have hcut : ∀ ℓ, (lvS modeL hostT hhost (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ).cut.card ≤ 3 := by
    intro ℓ
    refine (Finset.card_le_card (t := {Cp.cs, Cp.ct}) fun c hc => ?_).trans (Finset.card_le_two.trans (by norm_num))
    rcases CutPath.Run.cut_data _ ℓ modeL hostT _ hc with rfl | rfl <;> simp
  obtain ⟨-, lo, up⟩ := hA₂ N hN modeL hostT hhost M r₀ X₀ w₀ hP hc hS hcut hD hc1 hcr hcb hM hMl hM8 h0
    (2 * logN n)
  obtain ⟨elo, ej, ek⟩ := hA₁ N hN modeL hostT hhost M r₀ X₀ w₀ hP hc (hS 0) (hcut 0) hD hcr hcb hM hMl
    rfl rfl h0
  -- the least computed length
  have hg₀ : ∀ x, K₀ * c₀ (N.toRot.dual.rev x) + 1 = K₀ * c₀ x + 1 := fun x => by rw [dual_rev, hcr₀]
  have hpos : ∀ t, t < Cp.m → 1 ≤ K₀ * c₀ (Cp.e t) + 1 := fun _ _ => Nat.le_add_left 1 _
  obtain ⟨-, hrc⟩ := CutPath.recursion_cut (C := Cp) hR hC hgc hg₀ hpos hPath
  let rF := lvSeq hN modeL hostT hhost hE K D M r₀ (2 * logN n)
  obtain ⟨-, t₀, ht₀, hmin, hleast⟩ := hrc rF
  obtain ⟨-, hthm⟩ := theoremD_correct hR hC Cp c₀ hgc hcr₀ hK hPath hDual
  obtain ⟨v₀, hv₀, hcutv⟩ := hthm rF
  have he : (v₀ : ℝ≥0∞) = Cp.lamD (Nat.cast ∘ fun x => K₀ * c₀ x + 1) t₀ := hv₀.unique hleast
  let F : Fin n → ℕ∞ := fun v => min (voE v (A₁.run N.G X₀ T₁ v)) (ac v (A₂.run N.G X₀ (2 * logN n * T₂) v))
  have hΛ : (v₀ : ℝ≥0∞) ≤ ⨅ t, ⨅ (_ : t ≤ Cp.m), Cp.lamD (Nat.cast ∘ fun x => K₀ * c₀ x + 1) t :=
    le_iInf₂ fun q hq => he ▸ hmin q hq
  have hlowR : ∀ v, (v₀ : ℝ≥0∞) ≤ ((F v : ℕ∞) : ℝ≥0∞) := fun v => by
    simp only [F, ENat.toENNReal_min]
    exact le_min (hΛ.trans (elo v)) (hΛ.trans (lo v))
  have hF1 : ∀ v, ((F v : ℕ∞) : ℝ≥0∞) ≤ voE v (A₁.run N.G X₀ T₁ v) := fun v => by
    simp only [F, ENat.toENNReal_min]; exact min_le_left _ _
  have hF2 : ∀ v, ((F v : ℕ∞) : ℝ≥0∞) ≤ ac v (A₂.run N.G X₀ (2 * logN n * T₂) v) := fun v => by
    simp only [F, ENat.toENNReal_min]; exact min_le_right _ _
  have hpow : n * n < 2 ^ (2 * logN n) := by
    have h : n + 2 < 2 ^ logN n := by unfold logN; exact Nat.lt_pow_succ_log_self (by norm_num) _
    rw [two_mul, pow_add]
    exact Nat.mul_lt_mul'' (by omega) (by omega)
  have hmn := cutPath_m_lt Cp
  have hwitR : ∃ v, ((F v : ℕ∞) : ℝ≥0∞) ≤ v₀ := by
    obtain ⟨x, hx, hx2⟩ := hleast.1
    have hxe := rF.vals_eq x hx
    have hxv : Cp.lamD (Nat.cast ∘ fun x => K₀ * c₀ x + 1) x.1 = (v₀ : ℝ≥0∞) := by rw [← hxe, hx2, he]
    rcases rF.vals_cover x hx with h | h | ⟨ℓ, s, hs, hl⟩
    · obtain ⟨v, hv⟩ := ej
      rw [h] at hxv
      exact ⟨v, (hF1 v).trans (hv.trans_eq hxv)⟩
    · obtain ⟨v, hv⟩ := ek
      rw [h] at hxv
      exact ⟨v, (hF1 v).trans (hv.trans_eq hxv)⟩
    · by_cases hlt : ℓ < 2 * logN n
      · obtain ⟨v, hv⟩ := up ℓ hlt (2 * logN n) hlt s hs x.1 hl
        exact ⟨v, (hF2 v).trans (hv.trans_eq hxv)⟩
      · have h2 := Nat.pow_le_pow_right (show 0 < 2 by norm_num) (show 2 * logN n ≤ ℓ by omega)
        have h0' := rF.loc_deep (ℓ := ℓ) (by omega) s hs
        rw [h0'] at hl
        exact absurd hl (Set.notMem_empty _)
  have hlow : ∀ v, (v₀ : ℕ∞) ≤ F v := fun v => by
    have h := hlowR v
    rw [← ENat.toENNReal_coe] at h
    exact ENat.toENNReal_le.1 h
  obtain ⟨wm, hwm⟩ := hwitR
  have hwm' : F wm ≤ v₀ := by
    rw [← ENat.toENNReal_coe] at hwm
    exact ENat.toENNReal_le.1 hwm
  have hv₀M : v₀ < M := by
    have h := hMl t₀ ht₀
    rw [← he] at h
    exact_mod_cast h
  have hcapc : ∀ y : ℕ∞, (((min (M : ℕ∞) y).toNat : ℕ) : ℕ∞) = min (M : ℕ∞) y := fun y =>
    ENat.natCast_toNat (ne_top_of_le_ne_top (ENat.natCast_ne_top M) (min_le_left _ _))
  have hb : ∀ v, (X₀ v).1.bnd = M := fun v => by rw [h0.1 v]; rfl
  have hP12 : ∀ v, P₁₂.run N.G X₀ (T₁ + 2 * logN n * T₂) v = .inr ((X₀ v, voE v (A₁.run N.G X₀ T₁ v)),
      A₂.run N.G X₀ (2 * logN n * T₂) v) := by
    intro v
    rw [run_seq]
    simp only [P₁, P₂, run_keep, run_widen]
  have hx : (fun v => cap v (P₁₂.run N.G X₀ (T₁ + 2 * logN n * T₂) v)) = fun v => (min (M : ℕ∞) (F v)).toNat :=
    funext fun v => by
      rw [hP12 v]
      simp only [cap, hb]
      rfl
  have hbits : ∀ v, (min (M : ℕ∞) (F v)).toNat <
      2 ^ (4 * ((C₁ + C₂) * logN (n * (n * 21)) ^ (c₁ + c₂) + 3) + (3 * (K * logN (n * (n * 21)) + 1) + 5)) := fun v => by
    have h1 : (min (M : ℕ∞) (F v)).toNat ≤ M := by
      have h := hcapc (F v)
      exact_mod_cast h.le.trans (min_le_left _ _)
    exact (lam_lt_pow (h1.trans hM)).trans_le (Nat.pow_le_pow_right (by norm_num) (by omega))
  have hge : ∀ u, v₀ ≤ (min (M : ℕ∞) (F u)).toNat := fun u => by
    have h : ((v₀ : ℕ) : ℕ∞) ≤ (((min (M : ℕ∞) (F u)).toNat : ℕ) : ℕ∞) := by
      rw [hcapc]
      exact le_min (by exact_mod_cast hv₀M.le) (hlow u)
    exact_mod_cast h
  have heq : (min (M : ℕ∞) (F wm)).toNat = v₀ := by
    have h : (((min (M : ℕ∞) (F wm)).toNat : ℕ) : ℕ∞) = (v₀ : ℕ∞) := by
      rw [hcapc, le_antisymm hwm' (hlow wm)]
      exact min_eq_right (by exact_mod_cast hv₀M.le)
    exact_mod_cast h
  have hrun : (P₁₂.seq (T₁ + 2 * logN n * T₂) cap (minFlood (4 * ((C₁ + C₂) * logN (n * (n * 21)) ^ (c₁ + c₂) + 3) + (3 * (K * logN (n * (n * 21)) + 1) + 5)))).run N.G X₀ (T₁ + 2 * logN n * T₂ + D) w =
      .inr ((minFlood (4 * ((C₁ + C₂) * logN (n * (n * 21)) ^ (c₁ + c₂) + 3) + (3 * (K * logN (n * (n * 21)) + 1) + 5))).run N.G (fun v => cap v (P₁₂.run N.G X₀ (T₁ + 2 * logN n * T₂) v)) D w) := by
    rw [run_seq]
  rw [hrun]
  show IsLeast _ (((minFlood (4 * ((C₁ + C₂) * logN (n * (n * 21)) ^ (c₁ + c₂) + 3) + (3 * (K * logN (n * (n * 21)) + 1) + 5))).run N.G (fun v => cap v (P₁₂.run N.G X₀ (T₁ + 2 * logN n * T₂) v)) D w).1 / K₀)
  rw [hx, run_minFlood N.G _ hbits hD hge ⟨wm, heq⟩ w]
  exact hcutv

end RData

end RotSystem

end SsspFlow
