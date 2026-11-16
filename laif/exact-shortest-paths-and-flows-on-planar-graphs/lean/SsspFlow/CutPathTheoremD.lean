import SsspFlow.CutPathData
import SsspFlow.CutPathGs

/-!
# Theorem D from the network

Theorem D as one algorithm of the message model whose only input at a node is its rotation list, the
capacities of its darts and whether it is `s` or `t`. Three phases: the cut path with its indices and
length (`Congest.cpAlg_spec`), the base values (`RData.gsAlg_spec`), and the levels of the recursion
(`RData.theoremD_from_local`).

* `CutPath.lamD_le_card`: `λ_t` is at most the weight of `2 |D|` darts.
* `RData.mkX`, `scaleIn`: the local data of level `0`, and the costs `K₀ c + 1`.
* `RData.theoremD_net`: the algorithm and its output.
-/

set_option autoImplicit false

namespace SsspFlow

open FourColor SsspFlow.Congest Cslib.Congest.Algorithm
open scoped ENNReal

namespace RotSystem

namespace CutPath

variable {D : Type*} [Fintype D] [DecidableEq D] {R : RotSystem D}

/-- `λ_t` is at most the weight of `2 |D|` darts. -/
theorem lamD_le_card (C : R.CutPath) (hR : R.Planar) (hC : R.Connected) (g₀ : D → ℕ) {W : ℕ}
    (hW : ∀ x, g₀ x ≤ W) {t : ℕ} (ht : t ≤ C.m) :
    C.lamD (Nat.cast ∘ g₀) t ≤ ((2 * Fintype.card D * W : ℕ) : ℝ≥0∞) := by
  obtain ⟨p, hp⟩ := C.exists_walk hR hC (C.k_mem (σ := 0) ht) (C.k_mem (σ := 1) ht)
  obtain ⟨q, hq, hnd, -, -⟩ := hp.exists_simple
  have hlen : q.length ≤ Fintype.card (D × Bool) := (hnd.of_map _).length_le_card
  have hsum : (q.map (g₀ ∘ Prod.fst)).sum ≤ q.length * W := by
    have := List.sum_le_card_nsmul (q.map (g₀ ∘ Prod.fst)) W (fun y hy => by
      obtain ⟨z, -, rfl⟩ := List.mem_map.1 hy; exact hW _)
    simpa using this
  have hcard : Fintype.card (D × Bool) = 2 * Fintype.card D := by
    rw [Fintype.card_prod, Fintype.card_bool, mul_comm]
  calc C.lamD (Nat.cast ∘ g₀) t ≤ (q.map ((Nat.cast ∘ g₀ : D → ℝ≥0∞) ∘ Prod.fst)).sum :=
        walkDist_le _ hq
    _ = ((q.map (g₀ ∘ Prod.fst)).sum : ℝ≥0∞) := sum_cast_fst g₀ q
    _ ≤ _ := by
        exact_mod_cast hsum.trans (Nat.mul_le_mul_right W (hlen.trans hcard.le))

end CutPath

namespace RData

variable {n : ℕ}

/-- The local data of level `0` that a node computes from its input, its name and the indices and the
length of the cut path; the base values are filled later. -/
def mkX (K₀ M : ℕ) (w : Fin n) (h : DualHostIn (Fin n))
    (r : ℕ × (Fin n → Bool → (ℕ → Bool) × (ℕ → Bool)) × (Fin n → Bool → (ℕ → Bool) × (ℕ → Bool))) :
    ℕ × X0In n :=
  (0, ⟨w, h.nbrs, fun u => K₀ * h.cost u + 1, fun _ => false, fun u => decide (w < u), M, r.1,
    ⟨0, w.pos⟩, fun _ => (fun _ _ => ⊤, fun _ _ => ⊤), r.2.2, r.2.1⟩)

/-- The costs `K₀ c + 1` from the capacities `c`. -/
def scaleIn (K₀ : ℕ) (h : DualHostIn (Fin n)) : DualHostIn (Fin n) :=
  ⟨h.nbrs, fun u => K₀ * h.cost u + 1, h.isS, h.isT⟩

open Classical in
/-- **Theorem D from the network.** Assuming the Exact SSSP bound and the cut duality, there is an
algorithm of the message model, fixed before the network, with messages of `O(log^c n)` bits, that
runs `O(log^c n · D)` rounds on every planar connected network of diameter at most `D` without isolated
nodes. Every node starts with its rotation list, the capacities of its darts, symmetric and at most
`((5 n² + 2) ^ K - 1) / (n² + 1)`, and whether it is `s` or `t`, for `s ≠ t`. At the end every node holds
the minimum `st`-cut. -/
theorem theoremD_net (hE : ExactSsspBound) (K : ℕ) : ∃ C c : ℕ, ∀ n D : ℕ,
    ∃ (σ : Type) (B : ℕ) (A : Cslib.Congest.Algorithm (Fin n) (DualHostIn (Fin n)) σ B) (T : ℕ)
      (out : Fin n → σ → ℕ),
    B ≤ C * logN (n * (n * 21)) ^ c ∧ T ≤ C * logN (n * (n * 21)) ^ c * (D + 1) ∧
    ∀ (N : Net (Fin n)) (c₀ : Fin n → Fin n → ℕ) (s t : Fin n),
      N.toRot.Planar → N.toRot.Connected → N.DiamLE D → CutDuality N.G.Dart →
      (∀ v, ∃ u, N.G.Adj v u) → s ≠ t → (∀ u v, c₀ u v = c₀ v u) →
      (∀ u v, (n * n + 1) * c₀ u v + 1 ≤ (n * (n * 5) + 2) ^ K) →
      ∀ (s' t' : N.toRot.Vertex), N.vnode s' = s → N.vnode t' = t → ∀ w,
        IsLeast (N.toRot.cutVals (fun d => c₀ d.fst d.snd) s' t')
          (out w (A.run N.G (dualHostOf N c₀ s t) T w)) := by
  obtain ⟨C₂, c₂, hG⟩ := gsAlg_spec hE (K + 8)
  obtain ⟨C₃, c₃, hD3⟩ := theoremD_from_local hE (K + 8)
  refine ⟨(2 * hE.cC K + 12 + 4 * C₂ + 4 * C₃ + 6 * (K + 8) + 28) +
    (18 * hE.cC K + 64 * C₂ + 3264 * C₃ + 346), hE.cc K + c₂ + c₃ + 1, fun n D => ?_⟩
  obtain ⟨σ₂, A₂, out₂, hA₂⟩ := hG n D
  obtain ⟨σ₃, A₃, T₃, out₃, hT₃, hA₃⟩ := hD3 n D
  let B₁ := cpBx hE K n
  let B₂ := 4 * (C₂ * logN (n * (n * 21)) ^ c₂) + (3 * ((K + 8) * logN (n * (n * 21)) + 1) + 5)
  let B₃ := 4 * (C₃ * logN (n * (n * 21)) ^ c₃ + 3) + (3 * ((K + 8) * logN (n * (n * 21)) + 1) + 5)
  let T₁ := cpT₁ hE K D n + (1 + (cpT₁ hE K D n + cpT₁ hE K D n)) + (1 + D)
  let T₂ := 4 * (1 + (1 + (1 + C₂ * logN (n * (n * 21)) ^ c₂ * (12 * D + 16))))
  set K₀ := n * n + 1 with hK₀
  set Mb := (n * (n * 21) + 2) ^ (K + 8) with hMb
  let P₁ := ((cpAlg hE K D n).keep (fun _ h => scaleIn K₀ h)).widen
    (Nat.le_add_right B₁ (B₂ + B₃))
  let P₃ := A₃.widen (Nat.le_add_left B₃ B₁ |>.trans (Nat.add_le_add_left (Nat.le_add_left B₃ B₂) B₁))
  let P₂₃ := (A₂.widen (Nat.le_add_left B₂ B₁ |>.trans (Nat.add_le_add_left (Nat.le_add_right B₂ B₃) B₁))).seq T₂ out₂ P₃
  let P := P₁.seq T₁ (fun w s => mkX K₀ Mb w s.1 (cpOut w s.2)) P₂₃
  refine ⟨_, B₁ + (B₂ + B₃), P, T₁ + (T₂ + T₃), fun w s => match s with
    | .inr (.inr s') => out₃ w s' / K₀
    | _ => 0, ?_, ?_, ?_⟩
  · -- the width
    have hL1 : 1 ≤ logN (n * (n * 21)) := by unfold logN; omega
    have h5 : logN (n * (n * 5)) ≤ logN (n * (n * 21)) := by
      unfold logN; exact Nat.succ_le_succ (Nat.log_mono_right (by nlinarith))
    have hn : logN n ≤ logN (n * (n * 21)) := by
      unfold logN; exact Nat.succ_le_succ (Nat.log_mono_right (by nlinarith))
    have hP1 : 1 ≤ logN (n * (n * 21)) ^ (hE.cc K + c₂ + c₃ + 1) := Nat.one_le_pow _ _ hL1
    have hLP : logN (n * (n * 21)) ≤ logN (n * (n * 21)) ^ (hE.cc K + c₂ + c₃ + 1) :=
      (pow_one _).symm.le.trans (Nat.pow_le_pow_right hL1 (by omega))
    have ha := Nat.mul_le_mul_left (hE.cC K) ((Nat.pow_le_pow_left h5 (hE.cc K)).trans
      (Nat.pow_le_pow_right hL1 (show hE.cc K ≤ hE.cc K + c₂ + c₃ + 1 by omega)))
    have hb := Nat.mul_le_mul_left C₂ (Nat.pow_le_pow_right hL1 (show c₂ ≤ hE.cc K + c₂ + c₃ + 1 by omega))
    have hc := Nat.mul_le_mul_left C₃ (Nat.pow_le_pow_right hL1 (show c₃ ≤ hE.cc K + c₂ + c₃ + 1 by omega))
    have hk := Nat.mul_le_mul_left (K + 8) hLP
    have z1 := Nat.zero_le (hE.cC K * logN (n * (n * 21)) ^ (hE.cc K + c₂ + c₃ + 1))
    show ((hE.cC K * logN (n * (n * 5)) ^ hE.cc K + 3) + (hE.cC K * logN (n * (n * 5)) ^ hE.cc K + 3)) +
      (2 * logN n + 4) + ((4 * (C₂ * logN (n * (n * 21)) ^ c₂) + (3 * ((K + 8) * logN (n * (n * 21)) + 1) + 5)) +
        (4 * (C₃ * logN (n * (n * 21)) ^ c₃ + 3) + (3 * ((K + 8) * logN (n * (n * 21)) + 1) + 5))) ≤ _
    nlinarith
  · -- the rounds
    have hL1 : 1 ≤ logN (n * (n * 21)) := by unfold logN; omega
    have h5 : logN (n * (n * 5)) ≤ logN (n * (n * 21)) := by
      unfold logN; exact Nat.succ_le_succ (Nat.log_mono_right (by nlinarith))
    have hn : logN n ≤ logN (n * (n * 21)) := by
      unfold logN; exact Nat.succ_le_succ (Nat.log_mono_right (by nlinarith))
    set Lg := logN (n * (n * 21)) with hLg
    set P := Lg ^ (hE.cc K + c₂ + c₃ + 1) with hP
    have hP1 : 1 ≤ P := Nat.one_le_pow _ _ hL1
    have hLP : Lg ≤ P := (pow_one _).symm.le.trans (Nat.pow_le_pow_right hL1 (by omega))
    have ha := Nat.mul_le_mul (Nat.mul_le_mul_left (hE.cC K) ((Nat.pow_le_pow_left h5 (hE.cc K)).trans
      (Nat.pow_le_pow_right hL1 (show hE.cc K ≤ hE.cc K + c₂ + c₃ + 1 by omega))))
      (show 5 * D + 6 ≤ 6 * (D + 1) by omega)
    have hb := Nat.mul_le_mul (Nat.mul_le_mul_left C₂ (Nat.pow_le_pow_right hL1
      (show c₂ ≤ hE.cc K + c₂ + c₃ + 1 by omega))) (show 12 * D + 16 ≤ 16 * (D + 1) by omega)
    have hq : Lg * Lg ^ c₃ ≤ P := by
      rw [← pow_succ']; exact Nat.pow_le_pow_right hL1 (by omega)
    have hT3 : (2 * logN n + 1) * (110 + 68 * (C₃ * Lg ^ c₃ * (12 * D + 16))) ≤
        330 * (P * (D + 1)) + 204 * (C₃ * P * (16 * (D + 1))) := by
      have h1 : 2 * logN n + 1 ≤ 3 * Lg := by omega
      calc (2 * logN n + 1) * (110 + 68 * (C₃ * Lg ^ c₃ * (12 * D + 16)))
          ≤ (3 * Lg) * (110 + 68 * (C₃ * Lg ^ c₃ * (12 * D + 16))) := Nat.mul_le_mul_right _ h1
        _ = 330 * Lg + 204 * (C₃ * (Lg * Lg ^ c₃) * (12 * D + 16)) := by ring
        _ ≤ 330 * (P * (D + 1)) + 204 * (C₃ * P * (16 * (D + 1))) := by
            have := Nat.mul_le_mul (Nat.mul_le_mul_left C₃ hq) (show 12 * D + 16 ≤ 16 * (D + 1) by omega)
            have h2 : Lg ≤ P * (D + 1) := hLP.trans (Nat.le_mul_of_pos_right _ (by omega))
            omega
    have hD1 : D ≤ P * (D + 1) := by nlinarith
    have hX1 : 1 ≤ P * (D + 1) := by nlinarith
    have e1 : hE.cC K * P * (6 * (D + 1)) = 6 * (hE.cC K * (P * (D + 1))) := by ring
    have e2 : C₂ * P * (16 * (D + 1)) = 16 * (C₂ * (P * (D + 1))) := by ring
    have e3 : C₃ * P * (16 * (D + 1)) = 16 * (C₃ * (P * (D + 1))) := by ring
    rw [e1] at ha
    rw [e2] at hb
    rw [e3] at hT3
    have e4 : ((2 * hE.cC K + 12 + 4 * C₂ + 4 * C₃ + 6 * (K + 8) + 28) +
        (18 * hE.cC K + 64 * C₂ + 3264 * C₃ + 346)) * P * (D + 1) =
        (2 * hE.cC K + 12 + 4 * C₂ + 4 * C₃ + 6 * (K + 8) + 28) * (P * (D + 1)) +
          18 * (hE.cC K * (P * (D + 1))) + 64 * (C₂ * (P * (D + 1))) + 3264 * (C₃ * (P * (D + 1))) +
          346 * (P * (D + 1)) := by ring
    rw [e4]
    show (hE.cC K * logN (n * (n * 5)) ^ hE.cc K * (5 * D + 6) + (1 + (hE.cC K * logN (n * (n * 5)) ^ hE.cc K *
      (5 * D + 6) + hE.cC K * logN (n * (n * 5)) ^ hE.cc K * (5 * D + 6))) + (1 + D)) +
      (4 * (1 + (1 + (1 + C₂ * Lg ^ c₂ * (12 * D + 16)))) + T₃) ≤ _
    omega
  intro N c₀ s t hP hc hDi hDual hN hst hsym hcb s' t' hs' ht' w
  have hs := adj_headD N hN s
  have ht := adj_headD N hN t
  set g : Fin n → Fin n → ℕ := fun u v => K₀ * c₀ u v + 1 with hg
  have hg1 : ∀ d : N.G.Dart, 1 ≤ g d.fst d.snd := fun _ => Nat.le_add_left _ _
  obtain ⟨Cp, hcs, hct, hmin, hm, hkO, hkI⟩ := cpAlg_spec hE K D N g hs ht hst hP hN hDi hc hcb hg1
  set stc := (cpAlg hE K D n).run N.G (dualHostOf N g s t) T₁ with hstc
  set xX : Fin n → X0In n := fun w => (mkX K₀ Mb w (dualHostOf N c₀ s t w) (cpOut w (stc w))).2 with hxX
  have hrun : P.run N.G (dualHostOf N c₀ s t) (T₁ + (T₂ + T₃)) w =
      .inr (.inr (A₃.run N.G (fun v => out₂ v (A₂.run N.G (fun v => (0, xX v)) T₂ v)) T₃ w)) := by
    simp only [P, P₂₃, P₃, P₁]
    rw [run_seq]
    simp only [run_widen, run_keep]
    rw [run_seq]
    simp only [run_widen]
    rfl
  -- the facts of the network
  set c₀' : N.G.Dart → ℕ := fun d => c₀ d.fst d.snd with hc₀'
  set cc : N.G.Dart → ℕ := fun d => K₀ * c₀' d + 1 with hcc
  set modeL : N.G.Dart → Bool := fun _ => false
  set hostT : N.G.Dart → Bool := fun d => decide (d.fst < d.snd)
  have hhost : ∀ d, hostT (N.toRot.rev d) = !hostT d := fun d => by
    show decide (d.snd < d.fst) = !decide (d.fst < d.snd)
    rcases lt_or_gt_of_ne d.adj.ne with h | h
    · simp [h, not_lt.2 h.le]
    · simp [h, not_lt.2 h.le]
  have hsym' : ∀ d, c₀' (N.toRot.rev d) = c₀' d := fun d => by
    show c₀ d.snd d.fst = c₀ d.fst d.snd; exact hsym _ _
  have hR : N.toRot.dual.Planar := N.toRot.planar_dual.2 hP
  have hC : N.toRot.dual.Connected := N.toRot.connected_dual.2 hc
  have hgc : ∀ x, (Nat.cast ∘ cc : N.G.Dart → ℝ≥0∞) (N.toRot.dual.rev x) = (Nat.cast ∘ cc) x := fun x => by
    simp only [Function.comp_apply, dual_rev, hcc, hsym']
  have hg₀ : ∀ x, cc (N.toRot.dual.rev x) = cc x := fun x => by simp only [hcc, dual_rev, hsym']
  have hpos : ∀ t, t < Cp.m → 1 ≤ cc (Cp.e t) := fun _ _ => Nat.le_add_left 1 _
  obtain ⟨⟨r₀⟩, -⟩ := CutPath.recursion_cut (C := Cp) hR hC hgc hg₀ hpos hmin
  -- the bounds
  have hW : (n * (n * 5) + 2) ^ K ≤ (n * (n * 21) + 2) ^ K := Nat.pow_le_pow_left (by nlinarith) K
  have hW8 : (n * (n * 21) + 2) ^ K ≤ Mb := Nat.pow_le_pow_right (by omega) (by omega)
  have hccb : ∀ d, cc d ≤ (n * (n * 21) + 2) ^ (K + 8) := fun d => (hcb d.fst d.snd).trans (hW.trans hW8)
  have hmn := cutPath_m_lt Cp
  have hnM : n * n < Mb := by
    have : n * (n * 21) + 2 ≤ Mb := Nat.le_self_pow (by omega) _
    nlinarith
  have hmM : Cp.m < Mb := by omega
  have hK : Fintype.card N.G.Dart < K₀ := by
    have h2 : Fintype.card N.G.Dart ≤ Fintype.card (Fin n × Fin n) :=
      Fintype.card_le_of_injective _ SimpleGraph.Dart.toProd_injective
    simp only [Fintype.card_fin, Fintype.card_prod] at h2
    omega
  have hMl : ∀ t, t ≤ Cp.m → Cp.lamD (Nat.cast ∘ cc) t < Mb := fun t ht => by
    have h1 := CutPath.lamD_le_card Cp hR hC cc (W := (n * (n * 5) + 2) ^ K) (fun d => hcb d.fst d.snd) ht
    refine h1.trans_lt ?_
    have hc2 : Fintype.card N.G.Dart ≤ n * n := by omega
    have hW1 : 0 < (n * (n * 5) + 2) ^ K := by positivity
    have e1 : 2 * Fintype.card N.G.Dart * (n * (n * 5) + 2) ^ K < (n * (n * 21) + 2) * (n * (n * 5) + 2) ^ K :=
      Nat.mul_lt_mul_of_pos_right (by nlinarith) hW1
    have e2 : (n * (n * 21) + 2) ≤ (n * (n * 21) + 2) ^ 8 := Nat.le_self_pow (by norm_num) _
    have e3 : (n * (n * 21) + 2) * (n * (n * 5) + 2) ^ K ≤ Mb := by
      rw [hMb, pow_add, mul_comm ((n * (n * 21) + 2) ^ K)]
      exact Nat.mul_le_mul e2 hW
    exact_mod_cast e1.trans_le e3
  have hM8 : (Cp.m + 2) ^ 8 ≤ Mb :=
    (Nat.pow_le_pow_left (show Cp.m + 2 ≤ n * (n * 21) + 2 by nlinarith) 8).trans
      (Nat.pow_le_pow_right (by omega) (by omega))
  -- the base values
  set w₀ : Fin n := ⟨0, s.pos⟩
  obtain ⟨h1, h2⟩ := hA₂ N hN Cp cc modeL hostT hhost Mb r₀ xX w₀ hP hc hDi hccb le_rfl hmM
    (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) hm
    (fun _ => Fin.ext rfl) hkI hkO
  set x₃ : Fin n → X0In n := fun v => out₂ v (A₂.run N.G (fun v => (0, xX v)) T₂ v) with hx₃
  have hA := hA₃ N hN Cp c₀' K₀ modeL hostT hhost Mb x₃ w₀ hP hc hDi hDual hsym' hK hmin
    hccb le_rfl hMl hM8
    (fun w => congrArg X0In.me (h1 w)) (fun w => congrArg X0In.rot (h1 w))
    (fun d => congrFun (congrArg X0In.cw (h1 d.fst)) d.snd)
    (fun d => congrFun (congrArg X0In.mL (h1 d.fst)) d.snd)
    (fun d => congrFun (congrArg X0In.hT (h1 d.fst)) d.snd)
    (fun w => congrArg X0In.bnd (h1 w)) (fun w => (congrArg X0In.m (h1 w)).trans (hm w))
    (fun w => (congrArg X0In.src (h1 w)).trans (Fin.ext rfl)) h2
    (fun d b τ => by
      have e := congrArg X0In.kapI (h1 d.snd)
      change (x₃ d.snd).kapI = _ at e
      rw [e]; exact hkI d b τ)
    (fun d b τ => by
      have e := congrArg X0In.kapO (h1 d.fst)
      change (x₃ d.fst).kapO = _ at e
      rw [e]; exact hkO d b τ) w
  have e1 : s' = N.toRot.tail Cp.cs := N.vnode_injective (by rw [hs', hcs, Net.vnode_tail]; rfl)
  have e2 : t' = N.toRot.tail Cp.ct := N.vnode_injective (by rw [ht', hct, Net.vnode_tail]; rfl)
  rw [hrun, e1, e2]
  exact hA

end RData

end RotSystem

end SsspFlow
