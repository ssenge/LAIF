import SsspFlow.GHatStepBit
import SsspFlow.RunPick
import SsspFlow.RunLevel
import SsspFlow.OracleChoice

/-!
# The rule of a level

For a run of the recursion on the dual of a network, the data of level `ℓ` are those of the run at
depth `ℓ`, with any modes and a host rule that alternates on every pair, and token lengths given by the
costs. The rule of the level picks, for every annulus of the level that is not a leaf, the walk given
by the darts of the chain of its target in the output of the chosen oracle, and the step whose darts
are those of the copies on the chain with the step bit read from distances. Every such annulus has
node data that satisfy the rule.

* `RData.lvS`, `RData.lvR`, `RData.lvFl`: the data, the chosen output of the oracle and the true flags
  of a level.
* `RData.lvPof`: the rule of a level.
* `RData.lvPick`: every annulus of a level that is not a leaf has node data that satisfy the rule.
-/

set_option autoImplicit false

namespace SsspFlow

open FourColor SsspFlow.Congest
open scoped ENNReal

namespace RotSystem

namespace RData

variable {n : ℕ} {N : Net (Fin n)} (hN : ∀ u, ∃ w, N.G.Adj u w) {Cp : N.toRot.dual.CutPath}
  {cc : N.G.Dart → ℕ} {hR : N.toRot.dual.Planar} {hC : N.toRot.dual.Connected}
  {hgc : ∀ x, (Nat.cast ∘ cc : N.G.Dart → ℝ≥0∞) (N.toRot.dual.rev x) = (Nat.cast ∘ cc) x}
  {Γ₀ : Finset (N.G.Dart × Bool)} {L₀ : Cp.Live (Nat.cast ∘ cc) Γ₀} {j k : ℕ}
  (modeL hostT : N.G.Dart → Bool) (hhost : ∀ d, hostT (N.toRot.rev d) = !hostT d)

/-- The data of level `ℓ` of a run. -/
noncomputable def lvS (r : CutPath.Run hR hC hgc Γ₀ L₀ j k) (ℓ : ℕ) : N.toRot.RData :=
  r.data ℓ modeL hostT fun d _ => hhost d

/-- The token lengths of a level: the costs of the darts. -/
def lvLam (c : N.G.Dart → ℕ) (S : N.toRot.RData) : S.Tok → ℕ := fun x => c x.1.1

open Classical in
/-- The true flags of a level: the targets and the flags of the nodes for `0` and `1`. -/
noncomputable def lvFl (r : CutPath.Run hR hC hgc Γ₀ L₀ j k) (ℓ : ℕ) (a : Fin (n * (n * 21))) :
    Bool × Bool × Bool :=
  ((lvS modeL hostT hhost r ℓ).tgtFlag hN (r.levelQ ℓ) a,
    decide ((lvS modeL hostT hhost r ℓ).nodeFlag hN Cp 0 a),
    decide ((lvS modeL hostT hhost r ℓ).nodeFlag hN Cp 1 a))

variable (hE : ExactSsspBound) (K D M : ℕ)

/-- The chosen output of the oracle on the network of a level, from the sources of its annuli. -/
noncomputable def lvR (r : CutPath.Run hR hC hgc Γ₀ L₀ j k) (ℓ : ℕ) :
    Fin (n * (n * 21)) → ℕ∞ × Option (Fin (n * (n * 21))) :=
  hE.oracleRun K (12 * D + 16) (by omega) ((lvS modeL hostT hhost r ℓ).levelNet hN)
    ((lvS modeL hostT hhost r ℓ).levelLen hN (lvLam cc _) M)
    ((lvS modeL hostT hhost r ℓ).srcOff hN (r.levelQ ℓ))

/-- **The rule of a level.** The walk is the list of the darts of `kk` valid parent steps of the chain
of the target to a root, and the darts of the step are those of the arcs to the parents of the copies on the chain
with the step bit read from distances. -/
def lvPof (ℓ : ℕ) (r : CutPath.Run hR hC hgc Γ₀ L₀ j k)
    (A : Σ Γ' : Finset (N.G.Dart × Bool), Cp.Live (Nat.cast ∘ cc) Γ') (t : ℕ)
    (q sd : List (N.G.Dart × Bool)) : Prop :=
  ∃ kk, q = (lvS modeL hostT hhost r ℓ).chainDarts hN (lvR hN modeL hostT hhost hE K D M r ℓ)
      ((lvS modeL hostT hhost r ℓ).levelPad hN |>.ι (.inl ((lvS modeL hostT hhost r ℓ).endV (A.2.κ1 t)))) 0 kk ∧
    Net.ParSteps (lvR hN modeL hostT hhost hE K D M r ℓ)
      ((lvS modeL hostT hhost r ℓ).levelPad hN |>.ι (.inl ((lvS modeL hostT hhost r ℓ).endV (A.2.κ1 t)))) kk ∧
    ((lvR hN modeL hostT hhost hE K D M r ℓ) ((Net.parOf (lvR hN modeL hostT hhost hE K D M r ℓ))^[kk]
      ((lvS modeL hostT hhost r ℓ).levelPad hN |>.ι (.inl ((lvS modeL hostT hhost r ℓ).endV (A.2.κ1 t)))))).2 =
        none ∧
    ∀ z, z ∈ sd ↔ ∃ l,
      Net.ParSteps (lvR hN modeL hostT hhost hE K D M r ℓ)
        ((lvS modeL hostT hhost r ℓ).levelPad hN |>.ι (.inl ((lvS modeL hostT hhost r ℓ).endV (A.2.κ1 t)))) l ∧
      (lvS modeL hostT hhost r ℓ).stepBitD hN (lvR hN modeL hostT hhost hE K D M r ℓ)
        (lvFl hN modeL hostT hhost r ℓ)
        ((Net.parOf (lvR hN modeL hostT hhost hE K D M r ℓ))^[l]
          ((lvS modeL hostT hhost r ℓ).levelPad hN |>.ι (.inl ((lvS modeL hostT hhost r ℓ).endV (A.2.κ1 t))))) ∧
      ∃ x, (lvS modeL hostT hhost r ℓ).edgeTok hN
          (Net.parOf (lvR hN modeL hostT hhost hE K D M r ℓ)
            ((Net.parOf (lvR hN modeL hostT hhost hE K D M r ℓ))^[l]
              ((lvS modeL hostT hhost r ℓ).levelPad hN |>.ι (.inl ((lvS modeL hostT hhost r ℓ).endV (A.2.κ1 t))))))
          ((Net.parOf (lvR hN modeL hostT hhost hE K D M r ℓ))^[l]
            ((lvS modeL hostT hhost r ℓ).levelPad hN |>.ι (.inl ((lvS modeL hostT hhost r ℓ).endV (A.2.κ1 t))))) =
          some x ∧ z = N.toRot.tokDart x.1

/-- Lengths `⊤` or at most `1`, and offsets `0` or `⊤`, are valid for the oracle. -/
theorem oracleValid_small {V : Type} [Fintype V] [DecidableEq V] {N' : Net V} {W : ℕ} (hW : 1 ≤ W)
    {ℓ' : V → V → ℕ∞} {φ : V → ℕ∞} (hl : ∀ a b, ℓ' a b = ⊤ ∨ ℓ' a b ≤ 1) (hφ : ∀ a, φ a = ⊤ ∨ φ a = 0) :
    OracleValid N' 0 W ℓ' φ := by
  refine ⟨fun a b _ => ?_, fun a => ?_⟩
  · rcases hl a b with h | h
    · exact .inl h
    · exact .inr ⟨zero_le, h.trans (by exact_mod_cast hW)⟩
  · rcases hφ a with h | h
    · exact .inl h
    · exact .inr (by rw [h]; exact zero_le)

theorem markOffB_cases {V : Type} (isT : V → Bool) (a : V) :
    Net.markOffB isT a = ⊤ ∨ Net.markOffB isT a = 0 := by
  unfold Net.markOffB
  split_ifs
  · exact .inr rfl
  · exact .inl rfl

theorem toNat_le_one (b : Bool) : ((b.toNat : ℕ) : ℕ∞) ≤ 1 := by
  cases b <;> simp

/-- **Every annulus of a level has node data that satisfy the rule.** -/
theorem lvPick (r : CutPath.Run hR hC hgc Γ₀ L₀ j k) (ℓ : ℕ)
    (hP : N.toRot.Planar) (hc : N.toRot.Connected) (hS : (lvS modeL hostT hhost r ℓ).NoConflict)
    (hcut : (lvS modeL hostT hhost r ℓ).cut.card ≤ 3) (hD : N.DiamLE D)
    (hc1 : ∀ d, 1 ≤ cc d) (hcr : ∀ d, cc (N.toRot.rev d) = cc d)
    (hcK : ∀ d, cc d ≤ (n * (n * 21) + 2) ^ K) (hMK : M ≤ (n * (n * 21) + 2) ^ K)
    (hMl : ∀ t, t ≤ Cp.m → Cp.lamD (Nat.cast ∘ cc) t < M) :
    ∀ s ∈ r.subs ℓ, s.2.1.1 + 2 ≤ s.2.1.2 →
      Nonempty {d : CutPath.NodeData s.1.2 s.2.1.1 s.2.1.2 //
        lvPof hN modeL hostT hhost hE K D M ℓ r s.1 ((s.2.1.1 + s.2.1.2) / 2) d.q d.S.darts} := by
  classical
  intro s hs hjk
  set S := lvS modeL hostT hhost r ℓ with hSdef
  set Q := r.levelQ ℓ
  set R := lvR hN modeL hostT hhost hE K D M r ℓ
  set fl := lvFl hN modeL hostT hhost r ℓ
  set t := (s.2.1.1 + s.2.1.2) / 2
  have hW : 1 ≤ (n * (n * 21) + 2) ^ K := Nat.one_le_pow _ _ (by omega)
  have hΓ : S.Γ = Γ₀ ∪ r.steps ℓ := r.data_Γ ℓ modeL hostT _
  have hQ : ∀ q ∈ Q, q.1 ∈ r.nodes ℓ ∧ q.1.2.xa ≤ q.2 ∧ q.1.2.ya ≤ q.2 ∧ q.2 ≤ q.1.2.xb ∧
      q.2 ≤ q.1.2.yb ∧ Cp.lamD (Nat.cast ∘ cc) q.2 < M := fun q hq => by
    obtain ⟨h1, h2, h3, h4, h5⟩ := r.levelQ_range ℓ q hq
    exact ⟨h1, h2, h3, h4, h5, hMl _ (h4.trans q.1.2.xb_le)⟩
  have hQu := r.levelQ_uniq ℓ
  have hAt : (s.1, t) ∈ Q := (r.mem_levelQ ℓ).2 ⟨s, hs, hjk, rfl⟩
  have hlamK : ∀ x, lvLam cc S x ≤ (n * (n * 21) + 2) ^ K := fun x => hcK _
  have hNP := S.levelNet_planar hN hP hc hS hcut hD
  have hND := S.levelNet_diam hN hcut hD
  have hψW : ∀ z, S.srcOff hN Q z = ⊤ ∨ S.srcOff hN Q z ≤ (n * (n * 21) + 2) ^ K := fun z => by
    unfold srcOff
    split_ifs
    · exact .inr zero_le
    · exact .inl rfl
  have hval : OracleValid (S.levelNet hN) 0 ((n * (n * 21) + 2) ^ K) (S.levelLen hN (lvLam cc S) M)
      (S.srcOff hN Q) :=
    ⟨(S.oracleValid_level hN (lvLam cc S) M hlamK hMK (S.endV (s.1.2.κ1 t))).1, hψW⟩
  have hr : (S.levelNet hN).ExactSpec (S.levelLen hN (lvLam cc S) M) (S.srcOff hN Q) R :=
    hE.alg_spec K _ (12 * D + 16) (by omega) _ _ _ hNP hND hval
  have hfl : ∀ a, fl a = (S.tgtFlag hN Q a, decide (S.nodeFlag hN Cp 0 a), decide (S.nodeFlag hN Cp 1 a)) :=
    fun _ => rfl
  have hv2 : OracleValid (S.levelNet hN) 0 ((n * (n * 21) + 2) ^ K)
      (Net.markLenW R fun a => ((fl a).2.1.toNat : ℕ∞)) (Net.markOffB fun a => (fl a).1) :=
    oracleValid_small hW (fun a b => by
      unfold Net.markLenW
      split_ifs
      · exact .inr (toNat_le_one _)
      · exact .inl rfl) (markOffB_cases _)
  have h₂ := hE.alg_spec K _ (12 * D + 16) (by omega) _ _ _ hNP hND hv2
  set r₂ := hE.oracleRun K (12 * D + 16) (by omega) (S.levelNet hN)
    (Net.markLenW R fun a => ((fl a).2.1.toNat : ℕ∞)) (Net.markOffB fun a => (fl a).1)
  have hv3 : OracleValid (S.levelNet hN) 0 ((n * (n * 21) + 2) ^ K)
      (Net.downLenW R fun a => ((fl a).2.2.toNat : ℕ∞))
      (Net.markOffB fun a => (fl a).2.1 && decide ((r₂ a).1 = 0)) :=
    oracleValid_small hW (fun a b => by
      unfold Net.downLenW
      split_ifs
      · exact .inr (toNat_le_one _)
      · exact .inl rfl) (markOffB_cases _)
  have h₃ := hE.alg_spec K _ (12 * D + 16) (by omega) _ _ _ hNP hND hv3
  set r₃ := hE.oracleRun K (12 * D + 16) (by omega) (S.levelNet hN)
    (Net.downLenW R fun a => ((fl a).2.2.toNat : ℕ∞))
    (Net.markOffB fun a => (fl a).2.1 && decide ((r₂ a).1 = 0))
  let ixI : Fin (n * (n * 21)) → ℕ∞ := fun a => ⨅ u, ⨅ (_ : (S.levelPad hN).ι (.inl u) = a),
    ⨅ hu : ∃ x : S.Tok, S.IsEnd x.1 (S.vcopy u), ⨅ r' ∈ S.cutIdx Cp ⟨S.vcopy u, hu⟩, (r' : ℕ∞)
  let jxI : Fin (n * (n * 21)) → ℕ∞ := fun a => ⨅ u, ⨅ (_ : (S.levelPad hN).ι (.inl u) = a),
    ⨅ hu : ∃ x : S.Tok, S.IsEnd x.1 (S.vcopy u), ⨅ r' ∈ S.cutIdx Cp ⟨S.vcopy u, hu⟩, ((Cp.m - r' : ℕ) : ℕ∞)
  have hix : ∀ u (hu : ∃ x : S.Tok, S.IsEnd x.1 (S.vcopy u)),
      ixI ((S.levelPad hN).ι (.inl u)) = ⨅ r' ∈ S.cutIdx Cp ⟨S.vcopy u, hu⟩, (r' : ℕ∞) := fun u hu =>
    le_antisymm (iInf_le_of_le u (iInf_le_of_le rfl (iInf_le_of_le hu le_rfl)))
      (le_iInf fun u' => le_iInf fun h => le_iInf fun hu' => by
        obtain rfl := Sum.inl_injective ((S.levelPad hN).ι_injective h)
        exact le_rfl)
  have hjx : ∀ u (hu : ∃ x : S.Tok, S.IsEnd x.1 (S.vcopy u)),
      jxI ((S.levelPad hN).ι (.inl u)) = ⨅ r' ∈ S.cutIdx Cp ⟨S.vcopy u, hu⟩, ((Cp.m - r' : ℕ) : ℕ∞) :=
    fun u hu =>
    le_antisymm (iInf_le_of_le u (iInf_le_of_le rfl (iInf_le_of_le hu le_rfl)))
      (le_iInf fun u' => le_iInf fun h => le_iInf fun hu' => by
        obtain rfl := Sum.inl_injective ((S.levelPad hN).ι_injective h)
        exact le_rfl)
  obtain ⟨kk, i1, i2, St, hsh, hl, hg', -, -, hSt, hsub, hps, hnone⟩ := S.level_node_data hN r ℓ (lvLam cc S) M cc
    hc1 hcr (fun _ => rfl) (fun _ => rfl) hΓ Q hQ hQu R r₂ r₃ hr fl hfl h₂ h₃ ixI jxI hix hjx hAt _ _ rfl rfl
  refine ⟨⟨⟨hjk, _, hsh, i1, i2, hl, hg', St, hsub⟩, kk, rfl, hps, hnone, fun z => ?_⟩⟩
  show z ∈ (List.range St.n).map St.q ↔ _
  rw [hSt z]
  exact exists_congr fun l => (S.crit_iff hN R r₂ r₃ fl _ l z).trans
    (and_congr_right fun _ => and_congr_left fun _ => S.stepBit_iff_D hN R r₂ r₃ fl h₂ h₃ _)

end RData

end RotSystem

end SsspFlow
