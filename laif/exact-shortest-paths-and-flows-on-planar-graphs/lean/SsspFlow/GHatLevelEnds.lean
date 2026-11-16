import SsspFlow.GHatLevelLoop

/-!
# The lengths at the two ends of the cut, as one algorithm

On the stored state of level `0` every node knows the indices of the top annulus at its corners, and
the number `m`. Two runs of the oracle, with the source corner `κ0(t)` and the target corner `κ1(t)`
for `t = 0` and for `t = m`, give the node that hosts the target copy the length `λ_t`, and every
other node the value `⊤`.

* `RData.levelEnds_local`: the algorithm and its output.
-/

set_option autoImplicit false

namespace SsspFlow

open FourColor SsspFlow.Congest
open scoped ENNReal

namespace RotSystem

namespace RData

open Classical Cslib.Congest.Algorithm in
/-- **The lengths at the two ends, as one algorithm.** Every node starts with its stored state of
level `0`. After `T` rounds every value is at least the least `λ_t` over `t ≤ m`, and some node holds
a value at most `λ_j`, and some node a value at most `λ_k`, for the range `(j, k) = (0, m)` of the
run. -/
theorem levelEnds_local (hE : ExactSsspBound) (K : ℕ) : ∃ C c : ℕ, ∀ n D : ℕ,
    ∃ (σ : Type) (A : Cslib.Congest.Algorithm (Fin n) (LvX n) σ
        (4 * (C * logN (n * (n * 21)) ^ c) + (3 * (K * logN (n * (n * 21)) + 1) + 5)))
      (T : ℕ) (vo : Fin n → σ → ℕ∞),
    T ≤ 4 + 2 * (C * logN (n * (n * 21)) ^ c * (12 * D + 16)) ∧
    ∀ (N : Net (Fin n)) (hN : ∀ u, ∃ w, N.G.Adj u w) {Cp : N.toRot.dual.CutPath} {cc : N.G.Dart → ℕ}
      {hR : N.toRot.dual.Planar} {hC : N.toRot.dual.Connected}
      {hgc : ∀ x, (Nat.cast ∘ cc : N.G.Dart → ℝ≥0∞) (N.toRot.dual.rev x) = (Nat.cast ∘ cc) x}
      {Γ₀ : Finset (N.G.Dart × Bool)} {L₀ : Cp.Live (Nat.cast ∘ cc) Γ₀} {j k : ℕ}
      (modeL hostT : N.G.Dart → Bool) (hhost : ∀ d, hostT (N.toRot.rev d) = !hostT d) (M : ℕ)
      (r₀ : CutPath.Run hR hC hgc Γ₀ L₀ j k) (X : Fin n → LvX n) (w₀ : Fin n),
      N.toRot.Planar → N.toRot.Connected → (lvS modeL hostT hhost (lvSeq hN modeL hostT hhost hE K D M r₀ 0) 0).NoConflict → (lvS modeL hostT hhost (lvSeq hN modeL hostT hhost hE K D M r₀ 0) 0).cut.card ≤ 3 → N.DiamLE D →
      (∀ d, cc (N.toRot.rev d) = cc d) → (∀ d, cc d ≤ (n * (n * 21) + 2) ^ K) → M ≤ (n * (n * 21) + 2) ^ K →
      (∀ t, t ≤ Cp.m → Cp.lamD (Nat.cast ∘ cc) t < M) → j = 0 → k = Cp.m →
      LvInv hN modeL hostT hhost hE K D M r₀ w₀ 0 X →
      (∀ w, (⨅ t, ⨅ (_ : t ≤ Cp.m), Cp.lamD (Nat.cast ∘ cc) t) ≤ (vo w (A.run N.G X T w) : ℝ≥0∞)) ∧
      (∃ w, (vo w (A.run N.G X T w) : ℝ≥0∞) ≤ Cp.lamD (Nat.cast ∘ cc) j) ∧
      ∃ w, (vo w (A.run N.G X T w) : ℝ≥0∞) ≤ Cp.lamD (Nat.cast ∘ cc) k := by
  obtain ⟨C, c, hQR⟩ := levelQRun_local hE K
  refine ⟨C, c, fun n D => ?_⟩
  obtain ⟨σ₂, A₂, vmin, hA₂⟩ := hQR n D
  set T₂ := 2 + C * logN (n * (n * 21)) ^ c * (12 * D + 16) with hT₂
  let fl : ℕ → LvX n → LevelIn n × (Fin n → Bool → ℕ∞) × (Fin n → Bool → ℕ∞) := fun t x =>
    (x.1, fun u b => if ((x.2.2.2.1 u b).1 t) then 0 else ⊤, fun u b => if ((x.2.2.2.1 u b).2 t) then 0 else ⊤)
  let B₁ := A₂.keep (fun _ (x : LvX n) => fl 0 x)
  let B₂ := A₂.keep (fun _ (y : LvX n × ℕ∞) => fl y.1.2.1 y.1)
  let Bs := B₁.seq T₂ (fun w s => (s.1, vmin w s.2)) B₂
  refine ⟨_, Bs, T₂ + T₂, fun w s => match s with
    | .inr p => min p.1.2 (vmin w p.2)
    | .inl _ => ⊤, by omega, ?_⟩
  intro N hN Cp cc hR hC hgc Γ₀ L₀ j k modeL hostT hhost M r₀ X w₀ hP hc hS hcut hD hcr hcb hM hMl hj hk hX
  obtain ⟨h1, h2, -, -, h5⟩ := hX
  have key : ∀ t, (t = j ∨ t = k) →
      (∀ w, Cp.lamD (Nat.cast ∘ cc) t ≤ (vmin w (A₂.run N.G (fun v => fl t (X v)) T₂ w) : ℝ≥0∞)) ∧
      ∃ w, (vmin w (A₂.run N.G (fun v => fl t (X v)) T₂ w) : ℝ≥0∞) ≤ Cp.lamD (Nat.cast ∘ cc) t := by
    intro t ht
    obtain ⟨hjk, a1, a2, a3, a4⟩ := r₀.bounds
    have htm : t ≤ Cp.m := by omega
    have e : (fun v => fl t (X v)) = fun v => ((lvS modeL hostT hhost (lvSeq hN modeL hostT hhost hE K D M r₀ 0) 0).levelIn hN (lvLam cc (lvS modeL hostT hhost (lvSeq hN modeL hostT hhost hE K D M r₀ 0) 0)) M ((lvS modeL hostT hhost (lvSeq hN modeL hostT hhost hE K D M r₀ 0) 0).starV hN w₀) v,
        (fl t (X v)).2.1, (fl t (X v)).2.2) := funext fun v => by rw [← h1 v]
    have hrun := fun w => hA₂ N (lvS modeL hostT hhost (lvSeq hN modeL hostT hhost hE K D M r₀ 0) 0) hN (lvLam cc (lvS modeL hostT hhost (lvSeq hN modeL hostT hhost hE K D M r₀ 0) 0)) M ((lvS modeL hostT hhost (lvSeq hN modeL hostT hhost hE K D M r₀ 0) 0).starV hN w₀) (lvSeq hN modeL hostT hhost hE K D M r₀ 0) 0 cc [(⟨Γ₀, L₀⟩, t)]
      (fun v => (fl t (X v)).2.1) (fun v => (fl t (X v)).2.2) hP hc hS hcut hD (fun x => hcb x.1.1) hM hcr
      (fun _ => rfl) (fun _ => rfl) ((lvSeq hN modeL hostT hhost hE K D M r₀ 0).data_Γ 0 modeL hostT _)
      (fun q hq => by
        rw [List.mem_singleton] at hq
        subst hq
        rw [CutPath.Run.nodes_zero]
        dsimp only
        exact ⟨List.mem_singleton_self _, by omega, by omega, by omega, by omega, hMl t htm⟩)
      (fun q hq q' hq' _ => by rw [List.mem_singleton] at hq hq'; rw [hq, hq'])
      (fun d b => by
        simp only [fl, List.mem_singleton, exists_eq_left, qEnd, ite_true]
        exact if_congr (h5 d b t).1 rfl rfl)
      (fun d b => by
        simp only [fl, List.mem_singleton, exists_eq_left, qEnd, show (1 : Fin 2) ≠ 0 by decide, ite_false]
        exact if_congr (h5 d b t).2 rfl rfl) w
    rw [← e] at hrun
    refine ⟨fun w => ?_, ⟨_, (hrun _).trans_le ((iInf₂_le _ (List.mem_singleton_self _)).trans (iInf_le _ rfl))⟩⟩
    rw [hrun w]
    refine le_iInf₂ fun q hq => le_iInf fun _ => ?_
    rw [List.mem_singleton.1 hq]
  have hrun : ∀ w, Bs.run N.G X (T₂ + T₂) w = .inr ((X w, vmin w (A₂.run N.G (fun v => fl 0 (X v)) T₂ w)),
      A₂.run N.G (fun v => fl Cp.m (X v)) T₂ w) := by
    intro w
    rw [run_seq]
    simp only [B₁, B₂, run_keep, h2]
  have hΛ : ∀ t, t ≤ Cp.m → (⨅ t, ⨅ (_ : t ≤ Cp.m), Cp.lamD (Nat.cast ∘ cc) t) ≤ Cp.lamD (Nat.cast ∘ cc) t :=
    fun t ht => iInf₂_le t ht
  obtain ⟨k0l, k0u⟩ := key j (.inl rfl)
  obtain ⟨kml, kmu⟩ := key k (.inr rfl)
  subst hj hk
  simp only [hrun, ENat.toENNReal_min]
  refine ⟨fun w => le_min ((hΛ 0 (Nat.zero_le _)).trans (k0l w)) ((hΛ _ le_rfl).trans (kml w)), ?_, ?_⟩
  · obtain ⟨w, hw⟩ := k0u
    exact ⟨w, (min_le_left _ _).trans hw⟩
  · obtain ⟨w, hw⟩ := kmu
    exact ⟨w, (min_le_right _ _).trans hw⟩

end RData

end RotSystem

end SsspFlow
