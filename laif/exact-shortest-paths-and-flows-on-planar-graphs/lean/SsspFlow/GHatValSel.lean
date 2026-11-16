import SsspFlow.GHatLevelKids
import SsspFlow.GHatLevelPT

/-!
# Indices chosen from the values of the annuli

At a level, every corner of the component of an annulus that is not a leaf holds the values of the
annulus: its range, the least and greatest index of the walk of its chain and the overlap bits. A
rule `pick` reads an index from these values. The list `selQ` holds, for each annulus of the level,
the index of the rule when it lies strictly inside the range. At such an index the corners of the
annulus are those of the top annulus, so a corner decides from its values and the indices of the top
annulus at it whether it is the source or the target corner of an annulus of the list.

* `RData.selQ`: the annuli of a list with the indices of a rule strictly inside their ranges.
* `RData.mem_selQ`: its members.
* `RData.selQ_range`, `RData.selQ_uniq`: the conditions of a list for a run of the oracle.
* `RData.selQ_corner_iff`: the source and the target corners of the list from local values.
-/

set_option autoImplicit false

namespace SsspFlow

open FourColor SsspFlow.Congest
open scoped ENNReal

namespace RotSystem

namespace RData

variable {n : ℕ} {N : Net (Fin n)} {Cp : N.toRot.dual.CutPath} {cc : N.G.Dart → ℕ}

/-- The annuli of a list with the index of a rule, read from their values, when it lies strictly
inside the range read from the values. -/
def selQ (pick : ℕ × ℕ × ℕ × ℕ → Bool × Bool → Option ℕ)
    (payT payS : (Σ Γ' : Finset (N.G.Dart × Bool), Cp.Live (Nat.cast ∘ cc) Γ') × ℕ → ℕ)
    (Q : List ((Σ Γ' : Finset (N.G.Dart × Bool), Cp.Live (Nat.cast ∘ cc) Γ') × ℕ)) :
    List ((Σ Γ' : Finset (N.G.Dart × Bool), Cp.Live (Nat.cast ∘ cc) Γ') × ℕ) :=
  Q.filterMap fun q => (pick (decT (payT q)) (decS (payS q))).bind fun t =>
    if (decT (payT q)).1 < t ∧ t < (decT (payT q)).2.1 then some (q.1, t) else none

theorem mem_selQ (pick : ℕ × ℕ × ℕ × ℕ → Bool × Bool → Option ℕ)
    (payT payS : (Σ Γ' : Finset (N.G.Dart × Bool), Cp.Live (Nat.cast ∘ cc) Γ') × ℕ → ℕ)
    (Q : List ((Σ Γ' : Finset (N.G.Dart × Bool), Cp.Live (Nat.cast ∘ cc) Γ') × ℕ))
    (q' : (Σ Γ' : Finset (N.G.Dart × Bool), Cp.Live (Nat.cast ∘ cc) Γ') × ℕ) :
    q' ∈ selQ pick payT payS Q ↔ ∃ q ∈ Q, pick (decT (payT q)) (decS (payS q)) = some q'.2 ∧
      (decT (payT q)).1 < q'.2 ∧ q'.2 < (decT (payT q)).2.1 ∧ q'.1 = q.1 := by
  unfold selQ
  rw [List.mem_filterMap]
  refine exists_congr fun q => and_congr_right fun _ => ?_
  constructor
  · intro h
    obtain ⟨t, ht, h'⟩ := Option.bind_eq_some_iff.1 h
    split_ifs at h' with hc
    obtain rfl := (Option.some_injective _ h').symm
    exact ⟨ht, hc.1, hc.2, rfl⟩
  · rintro ⟨ht, h1, h2, h3⟩
    refine Option.bind_eq_some_iff.2 ⟨q'.2, ht, ?_⟩
    rw [if_pos ⟨h1, h2⟩, ← h3]

variable (hN : ∀ u, ∃ w, N.G.Adj u w)
  {hR : N.toRot.dual.Planar} {hC : N.toRot.dual.Connected}
  {hgc : ∀ x, (Nat.cast ∘ cc : N.G.Dart → ℝ≥0∞) (N.toRot.dual.rev x) = (Nat.cast ∘ cc) x}
  {Γ₀ : Finset (N.G.Dart × Bool)} {L₀ : Cp.Live (Nat.cast ∘ cc) Γ₀} {j k : ℕ}
  (modeL hostT : N.G.Dart → Bool) (hhost : ∀ d, hostT (N.toRot.rev d) = !hostT d)
  (hE : ExactSsspBound) (K D M : ℕ)

variable (r₀ : CutPath.Run hR hC hgc Γ₀ L₀ j k) (ℓ : ℕ)
  (hpick : ∀ s ∈ (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ).subs ℓ, s.2.1.1 + 2 ≤ s.2.1.2 →
    Nonempty {d : CutPath.NodeData s.1.2 s.2.1.1 s.2.1.2 //
      lvPof hN modeL hostT hhost hE K D M ℓ (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) s.1
        ((s.2.1.1 + s.2.1.2) / 2) d.q d.S.darts})
  (pick : ℕ × ℕ × ℕ × ℕ → Bool × Bool → Option ℕ)
  (payT payS : (Σ Γ' : Finset (N.G.Dart × Bool), Cp.Live (Nat.cast ∘ cc) Γ') × ℕ → ℕ)
  (h_pay : ∀ s ∈ (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ).subs ℓ, s.2.1.1 + 2 ≤ s.2.1.2 →
    ∀ kk i1 i2, lvDat hN modeL hostT hhost hE K D M (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ s kk i1 i2 →
      decT (payT (s.1, (s.2.1.1 + s.2.1.2) / 2)) = (s.2.1.1, s.2.1.2, i1, i2) ∧
      decS (payS (s.1, (s.2.1.1 + s.2.1.2) / 2)) =
        lvBits hN modeL hostT hhost hE K D M (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ s kk ∧
      payT (s.1, (s.2.1.1 + s.2.1.2) / 2) < M ∧ payS (s.1, (s.2.1.1 + s.2.1.2) / 2) < M)
include hpick h_pay

/-- A member of the list comes from a subrun of the level that is not a leaf, with its index strictly
inside the range of the subrun. -/
theorem selQ_sub {q' : (Σ Γ' : Finset (N.G.Dart × Bool), Cp.Live (Nat.cast ∘ cc) Γ') × ℕ}
    (hq' : q' ∈ selQ pick payT payS ((lvSeq hN modeL hostT hhost hE K D M r₀ ℓ).levelQ ℓ)) :
    ∃ s ∈ (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ).subs ℓ, s.2.1.1 + 2 ≤ s.2.1.2 ∧ q'.1 = s.1 ∧
      s.2.1.1 < q'.2 ∧ q'.2 < s.2.1.2 ∧
      pick (decT (payT (s.1, (s.2.1.1 + s.2.1.2) / 2))) (decS (payS (s.1, (s.2.1.1 + s.2.1.2) / 2))) =
        some q'.2 := by
  obtain ⟨q, hq, hp, h1, h2, h3⟩ := (mem_selQ pick payT payS _ q').1 hq'
  obtain ⟨s, hs, hjk, rfl⟩ := ((lvSeq hN modeL hostT hhost hE K D M r₀ ℓ).mem_levelQ ℓ).1 hq
  obtain ⟨kk, i1, i2, hd, -⟩ := lv_kids hN modeL hostT hhost hE K D M r₀ ℓ hpick hs hjk
  obtain ⟨d1, -⟩ := h_pay s hs hjk kk i1 i2 hd
  rw [d1] at h1 h2
  exact ⟨s, hs, hjk, h3, h1, h2, hp⟩

omit hpick h_pay in
/-- At an index strictly inside the range of a subrun of the level, its corners are those of the top
annulus, and the index lies in the ranges of its annulus. -/
theorem sub_corners {s : CutPath.Sub Cp hR hC hgc}
    (hs : s ∈ (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ).subs ℓ) {t : ℕ} (h1 : s.2.1.1 < t)
    (h2 : t < s.2.1.2) :
    s.1.2.κ0 t = L₀.κ0 t ∧ s.1.2.κ1 t = L₀.κ1 t ∧
      s.1.2.xa ≤ t ∧ s.1.2.ya ≤ t ∧ t ≤ s.1.2.xb ∧ t ≤ s.1.2.yb := by
  have hA : s.1 ∈ (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ).nodes ℓ := by
    rw [CutPath.Run.nodes_eq_subs]
    exact List.mem_map_of_mem hs
  obtain ⟨-, -, -, -, b0, b1⟩ := (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ).below_nodes ℓ s.1 hA
  obtain ⟨-, hxa, hya, hxb, hyb⟩ := s.2.2.bounds
  exact ⟨b0 _ (by omega) (by omega), b1 _ (by omega) (by omega), by omega, by omega, by omega, by omega⟩

/-- **The conditions of the list for a run of the oracle.** -/
theorem selQ_range (hMl : ∀ t, t ≤ Cp.m → Cp.lamD (Nat.cast ∘ cc) t < M) :
    ∀ q ∈ selQ pick payT payS ((lvSeq hN modeL hostT hhost hE K D M r₀ ℓ).levelQ ℓ),
      q.1 ∈ (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ).nodes ℓ ∧ q.1.2.xa ≤ q.2 ∧ q.1.2.ya ≤ q.2 ∧
        q.2 ≤ q.1.2.xb ∧ q.2 ≤ q.1.2.yb ∧ Cp.lamD (Nat.cast ∘ cc) q.2 < M := by
  intro q hq
  obtain ⟨s, hs, -, e, h1, h2, -⟩ := selQ_sub hN modeL hostT hhost hE K D M r₀ ℓ hpick pick payT payS h_pay hq
  obtain ⟨-, -, c1, c2, c3, c4⟩ := sub_corners hN modeL hostT hhost hE K D M r₀ ℓ hs h1 h2
  have hA : s.1 ∈ (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ).nodes ℓ := by
    rw [CutPath.Run.nodes_eq_subs]
    exact List.mem_map_of_mem hs
  rw [e]
  exact ⟨hA, c1, c2, c3, c4, hMl _ (c3.trans s.1.2.xb_le)⟩

/-- **One index per annulus.** -/
theorem selQ_uniq :
    ∀ q ∈ selQ pick payT payS ((lvSeq hN modeL hostT hhost hE K D M r₀ ℓ).levelQ ℓ),
      ∀ q' ∈ selQ pick payT payS ((lvSeq hN modeL hostT hhost hE K D M r₀ ℓ).levelQ ℓ),
        q.1 = q'.1 → q.2 = q'.2 := by
  intro q hq q' hq' he
  obtain ⟨p, hp, h1, -, -, e⟩ := (mem_selQ pick payT payS _ q).1 hq
  obtain ⟨p', hp', h1', -, -, e'⟩ := (mem_selQ pick payT payS _ q').1 hq'
  have hpp : p = p' := Prod.ext (e.symm.trans (he.trans e'))
    ((lvSeq hN modeL hostT hhost hE K D M r₀ ℓ).levelQ_uniq ℓ p hp p' hp' (e.symm.trans (he.trans e')))
  subst hpp
  exact Option.some_injective _ (h1.symm.trans h1')

/-- **The source and the target corners from local values.** Let `oTc` and `oSc` hold the values of
the annuli of the level at the corners of their components, below `M` only there, and let `kap σ z t`
say whether `z` is the corner `κσ(t)` of the top annulus. A corner is the corner `κσ(t)` of an
annulus of the list exactly when its values are below `M`, the rule reads an index strictly inside
the range from them, and `z` is the corner `κσ` of the top annulus at that index. -/
theorem selQ_corner_iff (oTc oSc : N.G.Dart × Bool → ℕ∞)
    (h_reg : ∀ s ∈ (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ).subs ℓ, s.2.1.1 + 2 ≤ s.2.1.2 → ∀ c,
      (N.toRot.dual.double.split s.1.1).toHypermap.gcomp (s.1.2.κ0 s.1.2.xa) c →
      oTc c = payT (s.1, (s.2.1.1 + s.2.1.2) / 2) ∧ oSc c = payS (s.1, (s.2.1.1 + s.2.1.2) / 2))
    (h_guard : ∀ c, oTc c < M → oSc c < M →
      ∃ s ∈ (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ).subs ℓ, s.2.1.1 + 2 ≤ s.2.1.2 ∧
        (N.toRot.dual.double.split s.1.1).toHypermap.gcomp (s.1.2.κ0 s.1.2.xa) c ∧
        oTc c = payT (s.1, (s.2.1.1 + s.2.1.2) / 2) ∧ oSc c = payS (s.1, (s.2.1.1 + s.2.1.2) / 2))
    (σ : Fin 2) (z : N.G.Dart × Bool) :
    (oTc z < M ∧ oSc z < M ∧ ∃ t, pick (decT (oTc z).toNat) (decS (oSc z).toNat) = some t ∧
        (decT (oTc z).toNat).1 < t ∧ t < (decT (oTc z).toNat).2.1 ∧ z = qEnd σ (⟨Γ₀, L₀⟩, t)) ↔
      ∃ q ∈ selQ pick payT payS ((lvSeq hN modeL hostT hhost hE K D M r₀ ℓ).levelQ ℓ), z = qEnd σ q := by
  have hcor : ∀ {s : CutPath.Sub Cp hR hC hgc}, s ∈ (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ).subs ℓ →
      ∀ {t : ℕ}, s.2.1.1 < t → t < s.2.1.2 → qEnd σ (s.1, t) = qEnd σ (⟨Γ₀, L₀⟩, t) := fun hs t h1 h2 => by
    obtain ⟨e0, e1, -⟩ := sub_corners hN modeL hostT hhost hE K D M r₀ ℓ hs h1 h2
    unfold qEnd
    split_ifs
    · exact e0
    · exact e1
  constructor
  · rintro ⟨hT, hS, t, hp, h1, h2, hz⟩
    obtain ⟨s, hs, hjk, -, e1, e2⟩ := h_guard z hT hS
    obtain ⟨kk, i1, i2, hd, -⟩ := lv_kids hN modeL hostT hhost hE K D M r₀ ℓ hpick hs hjk
    obtain ⟨d1, -⟩ := h_pay s hs hjk kk i1 i2 hd
    rw [e1, e2, ENat.toNat_coe, ENat.toNat_coe] at hp
    rw [e1, ENat.toNat_coe] at h1 h2
    have hq0 : (s.1, (s.2.1.1 + s.2.1.2) / 2) ∈ (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ).levelQ ℓ :=
      ((lvSeq hN modeL hostT hhost hE K D M r₀ ℓ).mem_levelQ ℓ).2 ⟨s, hs, hjk, rfl⟩
    refine ⟨(s.1, t), (mem_selQ pick payT payS _ _).2 ⟨_, hq0, hp, h1, h2, rfl⟩, ?_⟩
    rw [d1] at h1 h2
    rw [hz, hcor hs h1 h2]
  · rintro ⟨⟨A, t⟩, hq, rfl⟩
    obtain ⟨s, hs, hjk, e, h1, h2, hp⟩ := selQ_sub hN modeL hostT hhost hE K D M r₀ ℓ hpick pick payT payS h_pay hq
    dsimp only at e h1 h2 hp
    subst e
    obtain ⟨-, -, c1, c2, c3, c4⟩ := sub_corners hN modeL hostT hhost hE K D M r₀ ℓ hs h1 h2
    obtain ⟨kk, i1, i2, hd, -⟩ := lv_kids hN modeL hostT hhost hE K D M r₀ ℓ hpick hs hjk
    obtain ⟨d1, -, l1, l2⟩ := h_pay s hs hjk kk i1 i2 hd
    obtain ⟨e1, e2⟩ := h_reg s hs hjk _ (gcomp_qEnd σ (q := (s.1, t)) c1 c2 c3 c4)
    rw [e1, e2, ENat.toNat_coe, ENat.toNat_coe, d1]
    refine ⟨by exact_mod_cast l1, by exact_mod_cast l2, t, ?_, h1, h2, hcor hs h1 h2⟩
    rw [← d1]
    exact hp

end RData

end RotSystem

end SsspFlow
