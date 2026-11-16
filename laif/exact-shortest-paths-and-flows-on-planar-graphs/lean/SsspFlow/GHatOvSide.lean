import SsspFlow.GHatOvVal
import SsspFlow.GHatOvMark
import SsspFlow.GHatOvDist
import SsspFlow.GHatLevelChainRuns
import SsspFlow.GHatLevelOff
import SsspFlow.GHatFacePair
import SsspFlow.GHatLevelTgt
import SsspFlow.GHatCornerLocal
import SsspFlow.GHatCornerId
import SsspFlow.GHatLevelPrep
import SsspFlow.GHatLevelPick

/-!
# One overlap side of a level, as one algorithm

The nodes know the inputs of a level, the records of the darts of their neighbours, the offsets and
flags of the sources and targets of the annuli of the level and the flags of the corners of the sides,
and at each corner the values of its annulus and its indices of the top annulus. Three runs follow. The
counting run up the chains marks the first flagged node on the chain of each target. The run of the
oracle from the copies of the marked nodes gives every corner its distance from the marked corner of
its annulus. The run on the faces gives every corner the least value of the source corners at its face.
A last local step adds the two values at the target corners and takes the least value at each node.

* `RData.OvIn`: the inputs of a node.
* `Live.sideC_or`, `RData.ovBit_cf`, `RData.levelQ_rng`: the corners of a side, the flag of a side,
  and the ranges of the annuli of a level.
* `RData.levelOvSide_local`: the algorithm and its output, the least `λ_μ` over the annuli of the level
  and the indices `μ` of the side whose target corner the node hosts.
-/

set_option autoImplicit false

namespace SsspFlow

open FourColor SsspFlow.Congest
open scoped ENNReal

namespace RotSystem

theorem CutPath.Live.sideC_or {D : Type*} [Fintype D] [DecidableEq D] {R : RotSystem D}
    {C : R.CutPath} {g : D → ℝ≥0∞} {Γ : Finset (D × Bool)} (L : C.Live g Γ) {σ : Fin 2}
    {c : D × Bool} (h : L.SideC σ c) : L.CornerA c ∨ L.CornerB c := by
  match σ, h with
  | 0, h => exact .inl h
  | 1, h => exact .inr h

namespace RData

/-- The inputs of a node for one overlap side. -/
structure OvIn (n : ℕ) where
  /-- The inputs of the level. -/
  lv : LevelIn n
  /-- The records of the darts of the neighbours towards the node. -/
  inn : Fin n → DInfo
  /-- The offsets of the sources at the identifiers. -/
  off : Fin (n * (n * 21)) → ℕ∞
  /-- The flags of the targets at the identifiers. -/
  tg : Fin (n * (n * 21)) → Bool
  /-- The flags of the corners of the two sides at the identifiers. -/
  cf : Fin (n * (n * 21)) → Bool × Bool
  /-- The first value of the annulus at each corner. -/
  pT : Fin n → Bool → ℕ∞
  /-- The second value of the annulus at each corner. -/
  pS : Fin n → Bool → ℕ∞
  /-- The indices `t` with the corner `κ0(t)` of the top annulus. -/
  k0 : Fin n → Bool → ℕ → Bool
  /-- The indices `t` with the corner `κ1(t)` of the top annulus. -/
  k1 : Fin n → Bool → ℕ → Bool
  /-- The side. -/
  sd : Fin 2

variable {n : ℕ} {N : Net (Fin n)} (S : N.toRot.RData) (hN : ∀ u, ∃ w, N.G.Adj u w)
  {C : N.toRot.dual.CutPath} {g : N.G.Dart → ℝ≥0∞}

open Classical in
/-- The flag of a side is the flag of its corners. -/
theorem ovBit_cf (Q : List ((Σ Γ' : Finset (N.G.Dart × Bool), C.Live g Γ') × ℕ)) (σ : Fin 2)
    (a : Fin (n * (n * 21))) :
    ovBit σ (decide (S.cornerFlag hN Q (fun A c => A.2.CornerA c) a),
      decide (S.cornerFlag hN Q (fun A c => A.2.CornerB c) a)) =
      decide (S.cornerFlag hN Q (fun A c => A.2.SideC σ c) a) := by
  match σ with
  | 0 => rfl
  | 1 => rfl


/-- Pieces of equal copies: the vertex of the piece of a copy of an identifier is that of a corner
exactly when the piece of an equal vertex copy is the piece at the corner. -/
theorem vtx_copy_iff {a : Fin (n * (n * 21))} {v : S.hRot.Vertex} (h : S.copyAt hN a = S.vcopy v)
    (he : ∃ x : S.Tok, S.IsEnd x.1 (S.copyAt hN a)) (he' : ∃ x : S.Tok, S.IsEnd x.1 (S.vcopy v))
    (c : N.G.Dart × Bool) :
    S.vertexEquiv (S.pieceOf ⟨S.copyAt hN a, he⟩) = S.dualSplit.tail c ↔
      S.pieceOf ⟨S.vcopy v, he'⟩ = S.pieceAt c := by
  have e : (⟨S.copyAt hN a, he⟩ : S.EndCopy) = ⟨S.vcopy v, he'⟩ := Subtype.ext h
  rw [e, ← S.vertexEquiv_pieceAt, S.vertexEquiv.apply_eq_iff_eq]

variable {Cp : N.toRot.dual.CutPath} {cc : N.G.Dart → ℕ} {hR : N.toRot.dual.Planar}
  {hC : N.toRot.dual.Connected}
  {hgc : ∀ x, (Nat.cast ∘ cc : N.G.Dart → ℝ≥0∞) (N.toRot.dual.rev x) = (Nat.cast ∘ cc) x}
  {Γ₀ : Finset (N.G.Dart × Bool)} {L₀ : Cp.Live (Nat.cast ∘ cc) Γ₀} {j k : ℕ}

omit S hN in
/-- **The ranges of the annuli of a level.** The index of an annulus of the list of a level is the
middle of its range, the range holds at least two more indices, and strictly inside the range the
corners of the annulus are those of the top annulus and lie in its ranges. -/
theorem levelQ_rng (r : CutPath.Run hR hC hgc Γ₀ L₀ j k) (ℓ : ℕ)
    {q : (Σ Γ' : Finset (N.G.Dart × Bool), Cp.Live (Nat.cast ∘ cc) Γ') × ℕ} (hq : q ∈ r.levelQ ℓ) :
    q.2 = ((rngA r ℓ q.1).1 + (rngA r ℓ q.1).2) / 2 ∧ (rngA r ℓ q.1).1 + 2 ≤ (rngA r ℓ q.1).2 ∧
      ∀ μ, (rngA r ℓ q.1).1 < μ → μ < (rngA r ℓ q.1).2 → q.1.2.κ0 μ = L₀.κ0 μ ∧
        q.1.2.κ1 μ = L₀.κ1 μ ∧ q.1.2.xa ≤ μ ∧ q.1.2.ya ≤ μ ∧ μ ≤ q.1.2.xb ∧ μ ≤ q.1.2.yb := by
  obtain ⟨s, hs, hjk, rfl⟩ := (r.mem_levelQ ℓ).1 hq
  dsimp only
  rw [rngA_sub r ℓ hs]
  have hA : s.1 ∈ r.nodes ℓ := by
    rw [CutPath.Run.nodes_eq_subs]
    exact List.mem_map_of_mem hs
  obtain ⟨-, -, -, -, h0, h1⟩ := r.below_nodes ℓ s.1 hA
  obtain ⟨-, hxa, hya, hxb, hyb⟩ := s.2.2.bounds
  refine ⟨rfl, hjk, fun μ hl hr => ⟨h0 μ (by omega) (by omega), h1 μ (by omega) (by omega),
    by omega, by omega, by omega, by omega⟩⟩

open Classical Cslib.Congest.Algorithm in
/-- **One overlap side of a level, as one algorithm.** Assuming the Exact SSSP bound, one algorithm of
the message model, fixed before the network, starts from the inputs `OvIn` of a side `σ` of a level.
After `T` rounds every node `w` holds the least `λ_μ` over the annuli of the list of the level and the
indices `μ` that pass the test of the side with the values of the annulus and whose corner `κ1(μ)` is
hosted at `w`. -/
theorem levelOvSide_local (hE : ExactSsspBound) (K : ℕ) : ∃ C c : ℕ, ∀ n D : ℕ,
    ∃ (σ : Type) (A : Cslib.Congest.Algorithm (Fin n) (OvIn n) σ
        (4 * (C * logN (n * (n * 21)) ^ c + 3) + (3 * (K * logN (n * (n * 21)) + 1) + 5)))
      (T : ℕ) (val : Fin n → σ → ℕ∞),
    T ≤ 6 + 5 * (C * logN (n * (n * 21)) ^ c * (12 * D + 16)) ∧
    ∀ (N : Net (Fin n)) (S : N.toRot.RData) (hN : ∀ u, ∃ w, N.G.Adj u w) {Cp : N.toRot.dual.CutPath}
      {cc : N.G.Dart → ℕ} {hR : N.toRot.dual.Planar} {hC : N.toRot.dual.Connected}
      {hgc : ∀ x, (Nat.cast ∘ cc : N.G.Dart → ℝ≥0∞) (N.toRot.dual.rev x) = (Nat.cast ∘ cc) x}
      {Γ₀ : Finset (N.G.Dart × Bool)} {L₀ : Cp.Live (Nat.cast ∘ cc) Γ₀} {j k : ℕ}
      (r : CutPath.Run hR hC hgc Γ₀ L₀ j k) (ℓ : ℕ) (σs : Fin 2) (lam : S.Tok → ℕ) (M : ℕ)
      (u₀ : S.hRot.Vertex) (X : Fin n → OvIn n) (pT pS : N.G.Dart × Bool → ℕ∞)
      (payT payS : (Σ Γ' : Finset (N.G.Dart × Bool), Cp.Live (Nat.cast ∘ cc) Γ') × ℕ → ℕ),
      N.toRot.Planar → N.toRot.Connected → S.NoConflict → S.cut.card ≤ 3 → N.DiamLE D →
      (∀ d, cc (N.toRot.rev d) = cc d) → (∀ x, lam x = cc x.1.1) → (∀ d, cc d ≤ (n * (n * 21) + 2) ^ K) →
      M ≤ (n * (n * 21) + 2) ^ K → 1 ≤ M → (∀ d, S.hostT (N.toRot.rev d) = !S.hostT d) →
      S.Γ = Γ₀ ∪ r.steps ℓ → (∀ t, t ≤ Cp.m → Cp.lamD (Nat.cast ∘ cc) t < M) →
      (∀ w, (X w).lv = S.levelIn hN lam M u₀ w) → (∀ w, (X w).inn = fun u => S.dinfoAt u w) →
      (∀ w, (X w).sd = σs) → (∀ a, (X (hostOf a)).off a = S.srcOff hN (r.levelQ ℓ) a) →
      (∀ a, (X (hostOf a)).tg a = S.tgtFlag hN (r.levelQ ℓ) a) →
      (∀ a, (X (hostOf a)).cf a = (decide (S.cornerFlag hN (r.levelQ ℓ) (fun A c => A.2.CornerA c) a),
        decide (S.cornerFlag hN (r.levelQ ℓ) (fun A c => A.2.CornerB c) a))) →
      (∀ (d : N.G.Dart) b, (X d.snd).pT d.fst b = pT (d, b) ∧ (X d.snd).pS d.fst b = pS (d, b)) →
      (∀ (d : N.G.Dart) b t, ((X d.snd).k0 d.fst b t = true ↔ (d, b) = L₀.κ0 t) ∧
        ((X d.snd).k1 d.fst b t = true ↔ (d, b) = L₀.κ1 t)) →
      (∀ q ∈ r.levelQ ℓ, ∀ z, (N.toRot.dual.double.split q.1.1).toHypermap.gcomp (q.1.2.κ0 q.1.2.xa) z →
        pT z = payT q ∧ pS z = payS q) →
      (∀ z, pT z < M → pS z < M →
        ∃ q ∈ r.levelQ ℓ, (N.toRot.dual.double.split q.1.1).toHypermap.gcomp (q.1.2.κ0 q.1.2.xa) z) →
      let R := hE.oracleRun K (12 * D + 16) (by omega) (S.levelNet hN) (S.levelLen hN lam M)
        (S.srcOff hN (r.levelQ ℓ))
      (S.levelNet hN).ExactSpec (S.levelLen hN lam M) (S.srcOff hN (r.levelQ ℓ)) R →
      (∀ q ∈ r.levelQ ℓ, payT q < M ∧ payS q < M ∧ ∀ kk i1 i2,
        Net.ParSteps R ((S.levelPad hN).ι (.inl (S.endV (q.1.2.κ1 q.2)))) kk →
        (R ((Net.parOf R)^[kk] ((S.levelPad hN).ι (.inl (S.endV (q.1.2.κ1 q.2)))))).2 = none →
        IsLeast (Cp.idx (q.1.2.κ0 q.2) (S.chainDarts hN R ((S.levelPad hN).ι (.inl (S.endV (q.1.2.κ1 q.2)))) 0 kk)) i1 →
        IsGreatest (Cp.idx (q.1.2.κ0 q.2) (S.chainDarts hN R ((S.levelPad hN).ι (.inl (S.endV (q.1.2.κ1 q.2)))) 0 kk)) i2 →
        decT (payT q) = ((rngA r ℓ q.1).1, (rngA r ℓ q.1).2, i1, i2) ∧
        decS (payS q) = (decide (∃ c, q.1.2.CornerA c ∧ q.1.2.Visits q.2
            (S.chainDarts hN R ((S.levelPad hN).ι (.inl (S.endV (q.1.2.κ1 q.2)))) 0 kk) c),
          decide (∃ c, q.1.2.CornerB c ∧ q.1.2.Visits q.2
            (S.chainDarts hN R ((S.levelPad hN).ι (.inl (S.endV (q.1.2.κ1 q.2)))) 0 kk) c))) →
      (∀ At ∈ r.levelQ ℓ, ∃ (kk i1 i2 : ℕ),
        At.1.2.Shortest At.2 (S.chainDarts hN R ((S.levelPad hN).ι (.inl (S.endV (At.1.2.κ1 At.2)))) 0 kk) ∧
        IsLeast (Cp.idx (At.1.2.κ0 At.2)
          (S.chainDarts hN R ((S.levelPad hN).ι (.inl (S.endV (At.1.2.κ1 At.2)))) 0 kk)) i1 ∧
        IsGreatest (Cp.idx (At.1.2.κ0 At.2)
          (S.chainDarts hN R ((S.levelPad hN).ι (.inl (S.endV (At.1.2.κ1 At.2)))) 0 kk)) i2 ∧
        (∀ c, At.1.2.Visits At.2 (S.chainDarts hN R ((S.levelPad hN).ι (.inl (S.endV (At.1.2.κ1 At.2)))) 0 kk) c ↔
          ∃ y, (∃ i, (Net.parOf R)^[i] ((S.levelPad hN).ι (.inl (S.endV (At.1.2.κ1 At.2)))) = y) ∧
            ∃ hy : (∃ x : S.Tok, S.IsEnd x.1 (S.copyAt hN y)),
              S.vertexEquiv (S.pieceOf ⟨S.copyAt hN y, hy⟩) = S.dualSplit.tail c) ∧
        Net.ParSteps R ((S.levelPad hN).ι (.inl (S.endV (At.1.2.κ1 At.2)))) kk ∧
        (R ((Net.parOf R)^[kk] ((S.levelPad hN).ι (.inl (S.endV (At.1.2.κ1 At.2)))))).2 = none) →
      ∀ w, (val w (A.run N.G X T w) : ℝ≥0∞) =
        ⨅ q ∈ r.levelQ ℓ, ⨅ μ, ⨅ (_ : ovIn σs (decT (payT q)) (decS (payS q)) μ),
          ⨅ (_ : (q.1.2.κ1 μ).1.snd = w), Cp.lamD (Nat.cast ∘ cc) μ := by
  obtain ⟨Cc, ccc, hCh⟩ := levelChain_local hE K
  obtain ⟨Cs, ccs, hSs⟩ := levelSsspOff_local hE K
  obtain ⟨Cf, ccf, hFp⟩ := facePair_local hE K
  refine ⟨Cc + Cs + Cf, ccc + ccs + ccf, fun n D => ?_⟩
  set b := K * logN (n * (n * 21)) + 1 with hb
  obtain ⟨σc, Ac, Tc, outc, hTc, hAc⟩ := hCh n D
  obtain ⟨σs', As, outs, hAs⟩ := hSs n D
  obtain ⟨σf, Af, outf, hAf⟩ := hFp n D
  have hL : 1 ≤ logN (n * (n * 21)) := by unfold logN; omega
  have hpc : logN (n * (n * 21)) ^ ccc ≤ logN (n * (n * 21)) ^ (ccc + ccs + ccf) :=
    Nat.pow_le_pow_right hL (by omega)
  have hps : logN (n * (n * 21)) ^ ccs ≤ logN (n * (n * 21)) ^ (ccc + ccs + ccf) :=
    Nat.pow_le_pow_right hL (by omega)
  have hpf : logN (n * (n * 21)) ^ ccf ≤ logN (n * (n * 21)) ^ (ccc + ccs + ccf) :=
    Nat.pow_le_pow_right hL (by omega)
  have hmc := Nat.mul_le_mul (show Cc ≤ Cc + Cs + Cf by omega) hpc
  have hms := Nat.mul_le_mul (show Cs ≤ Cc + Cs + Cf by omega) hps
  have hmf := Nat.mul_le_mul (show Cf ≤ Cc + Cs + Cf by omega) hpf
  set W := 4 * ((Cc + Cs + Cf) * logN (n * (n * 21)) ^ (ccc + ccs + ccf) + 3) + (3 * b + 5) with hW
  have w1 : 4 * (Cc * logN (n * (n * 21)) ^ ccc + 3) + (3 * b + 5) ≤ W := by omega
  have w2 : 4 * (Cs * logN (n * (n * 21)) ^ ccs) + (3 * b + 5) ≤ W := by omega
  have w3 : 4 * (Cf * logN (n * (n * 21)) ^ ccf) + (3 * b + 5) ≤ W := by omega
  set Ts := 1 + Cs * logN (n * (n * 21)) ^ ccs * (12 * D + 16) with hTs
  set Tf := 1 + (1 + (1 + Cf * logN (n * (n * 21)) ^ ccf * (12 * D + 16))) with hTf
  let fl : OvIn n → Fin (n * (n * 21)) → Bool × Bool × Bool := fun x a => (x.tg a, ovBit x.sd (x.cf a), false)
  let C1 := (Ac.widen w1).keep (fun _ (x : OvIn n) => (x.lv, (x.off, fl x)))
  let mk : OvIn n × σc → Fin (n * (n * 21)) → Prop := fun s a =>
    (fl s.1 a).2.1 = true ∧ (outc a s.2).2.1.1 = 0
  let cp : Fin n → OvIn n → Fin (n * (n * 21)) → Fin (n * (n * 21)) := fun w x a =>
    cpIdL x.lv.rot x.lv.own x.inn w ((idEquiv.symm a).2.1, (idEquiv.symm a).2.2)
  let off' : Fin n → OvIn n × σc → Fin (n * (n * 21)) → ℕ∞ := fun w s z =>
    if ∃ a, hostOf a = w ∧ mk s a ∧ cp w s.1 a = z then 0 else ⊤
  let C2 := (As.widen w2).keep (fun w (s : OvIn n × σc) => (s.1.lv, off' w s))
  let dC : Fin n → (OvIn n × σc) × σs' → Fin n → Bool → ℕ∞ := fun w s u β =>
    outs (idEquiv (cornerName s.1.1.lv.rot s.1.1.lv.own w u β)) s.2
  let va : Fin n → (OvIn n × σc) × σs' → Fin n → Bool → ℕ∞ := fun w s u β =>
    if ovTest s.1.1.sd s.1.1.lv.bnd (s.1.1.pT u β) (s.1.1.pS u β) (s.1.1.k0 u β) then
      min (dC w s u β) s.1.1.lv.bnd else ⊤
  let C3 := (Af.widen w3).keep (fun w (s : (OvIn n × σc) × σs') => (s.1.1.lv, va w s))
  let tv : Fin n → ((OvIn n × σc) × σs') × σf → Fin n → Bool → ℕ∞ := fun w s u β =>
    if ovTest s.1.1.1.sd s.1.1.1.lv.bnd (s.1.1.1.pT u β) (s.1.1.1.pS u β) (s.1.1.1.k1 u β) then
      min (outf w s.2 u β) s.1.1.1.lv.bnd + min (dC w s.1 u β) s.1.1.1.lv.bnd else ⊤
  refine ⟨_, C1.seq Tc (fun _ s => s) (C2.seq Ts (fun _ s => s) C3), Tc + (Ts + Tf),
    fun w s => match s with
      | .inr (.inr s3) => ⨅ u, ⨅ (_ : u ∈ s3.1.1.1.lv.rot), ⨅ β, tv w s3 u β
      | _ => ⊤, ?_, ?_⟩
  · have h1 : Cc * logN (n * (n * 21)) ^ ccc * (12 * D + 16) ≤
        (Cc + Cs + Cf) * logN (n * (n * 21)) ^ (ccc + ccs + ccf) * (12 * D + 16) := Nat.mul_le_mul_right _ hmc
    have h2 : Cs * logN (n * (n * 21)) ^ ccs * (12 * D + 16) ≤
        (Cc + Cs + Cf) * logN (n * (n * 21)) ^ (ccc + ccs + ccf) * (12 * D + 16) := Nat.mul_le_mul_right _ hms
    have h3 : Cf * logN (n * (n * 21)) ^ ccf * (12 * D + 16) ≤
        (Cc + Cs + Cf) * logN (n * (n * 21)) ^ (ccc + ccs + ccf) * (12 * D + 16) := Nat.mul_le_mul_right _ hmf
    omega
  intro N S hN Cp cc hR hC hgc Γ₀ L₀ j k r ℓ σs lam M u₀ X pT pS payT payS hP hc hS hcut hD hcr hlam hcb
    hM hM1 hh hΓ hMl hlv hinn hsd hoff htg hcf hp hk hreg hguard R hRs hpay hex
  set sc := Ac.run N.G (fun w => ((X w).lv, ((X w).off, fl (X w)))) Tc with hsc
  set ss := As.run N.G (fun w => ((X w).lv, off' w (X w, sc w))) Ts with hss
  set sf := Af.run N.G (fun w => ((X w).lv, va w ((X w, sc w), ss w))) Tf with hsf
  have hrun : (C1.seq Tc (fun _ s => s) (C2.seq Ts (fun _ s => s) C3)).run N.G X (Tc + (Ts + Tf)) =
      fun w => .inr (.inr (((X w, sc w), ss w), sf w)) := by
    funext w
    simp only [C1, C2, C3, run_seq, run_keep, run_widen]
    rfl
  rw [hrun]
  -- basic facts
  have hin1' : ∀ v, S.levelIn hN lam M u₀ v = (X v).lv := fun v => (hlv v).symm
  have hbnd : ∀ v, (X v).lv.bnd = M := fun v => by rw [hlv]; rfl
  have hrot : ∀ v, (X v).lv.rot = N.rotList v := fun v => by rw [hlv]; rfl
  have hown : ∀ v, (X v).lv.own = S.dinfoAt v := fun v => by rw [hlv]; rfl
  have hlamB : ∀ x, lam x ≤ (n * (n * 21) + 2) ^ K := fun x => by rw [hlam]; exact hcb _
  have hQr := r.levelQ_range ℓ
  have hQu := r.levelQ_uniq ℓ
  have hQM : ∀ q ∈ r.levelQ ℓ, Cp.lamD (Nat.cast ∘ cc) q.2 < M := fun q hq =>
    hMl _ ((hQr q hq).2.2.2.1.trans q.1.2.xb_le)
  have hQ6 : ∀ q ∈ r.levelQ ℓ, q.1 ∈ r.nodes ℓ ∧ q.1.2.xa ≤ q.2 ∧ q.1.2.ya ≤ q.2 ∧ q.2 ≤ q.1.2.xb ∧
      q.2 ≤ q.1.2.yb ∧ Cp.lamD (Nat.cast ∘ cc) q.2 < M := fun q hq =>
    ⟨(hQr q hq).1, (hQr q hq).2.1, (hQr q hq).2.2.1, (hQr q hq).2.2.2.1, (hQr q hq).2.2.2.2, hQM q hq⟩
  set P : (Σ Γ' : Finset (N.G.Dart × Bool), Cp.Live (Nat.cast ∘ cc) Γ') → N.G.Dart × Bool → Prop :=
    fun A c => A.2.SideC σs c with hPdef
  -- the counting run
  set fl' : Fin (n * (n * 21)) → Bool × Bool × Bool := fun a => (S.tgtFlag hN (r.levelQ ℓ) a,
    ovBit σs (decide (S.cornerFlag hN (r.levelQ ℓ) (fun A c => A.2.CornerA c) a),
      decide (S.cornerFlag hN (r.levelQ ℓ) (fun A c => A.2.CornerB c) a)), false) with hfl'
  have hfl : ∀ a, fl (X (hostOf a)) a = fl' a := fun a => by simp only [fl, fl', htg, hcf, hsd]
  have hψW : ∀ z, S.srcOff hN (r.levelQ ℓ) z = ⊤ ∨ S.srcOff hN (r.levelQ ℓ) z ≤ (n * (n * 21) + 2) ^ K :=
    fun z => by unfold srcOff; split_ifs <;> simp
  have hch := hAc N S hN lam M u₀ (S.srcOff hN (r.levelQ ℓ)) fl' (fun w => (X w).off) (fun w => fl (X w))
    hP hc hS hcut hD hlamB hM hψW hoff hfl
  simp only [hin1'] at hch
  obtain ⟨-, k2, -, k4⟩ := hch
  set st₁ : Fin (n * (n * 21)) → (ℕ∞ × Option (Fin (n * (n * 21)))) × (ℕ∞ × Option (Fin (n * (n * 21)))) ×
    (ℕ∞ × Option (Fin (n * (n * 21)))) := fun a => outc a (sc (hostOf a)) with hst₁
  have hR' : (fun a => (st₁ a).1) = R := k4
  set r₂ : Fin (n * (n * 21)) → ℕ∞ × Option (Fin (n * (n * 21))) := fun a => (st₁ a).2.1 with hr₂
  have hfl2 : (fun a => (((fl' a).2.1).toNat : ℕ∞)) =
      fun a => ((decide (S.cornerFlag hN (r.levelQ ℓ) P a)).toNat : ℕ∞) := funext fun a => by
    simp only [fl', ovBit_cf, hPdef]
  have h₂ : (S.levelNet hN).ExactSpec
      (Net.markLenW R fun a => ((decide (S.cornerFlag hN (r.levelQ ℓ) P a)).toNat : ℕ∞))
      (Net.markOffB (S.tgtFlag hN (r.levelQ ℓ))) r₂ := by
    rw [← hR', ← hfl2]
    exact k2
  have hT := S.tgtFlag_chains hN r ℓ lam M cc hcr hlam (fun _ => rfl) hΓ (r.levelQ ℓ) hQ6 hQu R hRs
  set mk' : Fin (n * (n * 21)) → Prop := fun a => S.cornerFlag hN (r.levelQ ℓ) P a ∧ (r₂ a).1 = 0
    with hmk'
  have hmk_iff : ∀ a, mk (X (hostOf a), sc (hostOf a)) a ↔ mk' a := fun a => by
    simp only [mk, mk', hfl, fl', ovBit_cf, decide_eq_true_iff]
    rfl
  -- the run from the marked copies
  set cpT : Fin (n * (n * 21)) → Fin (n * (n * 21)) := fun a =>
    cpIdL (N.rotList (hostOf a)) (S.dinfoAt (hostOf a)) (fun u => S.dinfoAt u (hostOf a)) (hostOf a)
      ((idEquiv.symm a).2.1, (idEquiv.symm a).2.2) with hcpT
  have hcp : ∀ a, cp (hostOf a) (X (hostOf a)) a = cpT a := fun a => by
    simp only [cp, cpT, hrot, hown, hinn]
  set ψ' : Fin (n * (n * 21)) → ℕ∞ := fun z => if ∃ a, mk' a ∧ cpT a = z then 0 else ⊤ with hψ'
  have hoff' : ∀ z, off' (hostOf z) (X (hostOf z), sc (hostOf z)) z = ψ' z := fun z => by
    simp only [off', ψ']
    refine if_congr ⟨?_, ?_⟩ rfl rfl
    · rintro ⟨a, ha, hm, he⟩
      rw [← ha] at hm he
      exact ⟨a, (hmk_iff a).1 hm, (hcp a) ▸ he⟩
    · rintro ⟨a, hm, rfl⟩
      rw [S.cpId_host hN a]
      exact ⟨a, rfl, (hmk_iff a).2 hm, hcp a⟩
  have hψtop : ∀ z, (∀ u, z ≠ (S.levelPad hN).ι (.inl u)) → ψ' z = ⊤ := fun z hz => by
    simp only [ψ']
    refine if_neg ?_
    rintro ⟨a, -, rfl⟩
    obtain ⟨v, hv, -⟩ := S.cpId_spec hN a
    exact hz v hv
  have hψW' : ∀ z, ψ' z = ⊤ ∨ ψ' z ≤ (n * (n * 21) + 2) ^ K := fun z => by
    simp only [ψ']; split_ifs <;> simp
  have hss := hAs N S hN lam M u₀ ψ' (fun w => off' w (X w, sc w)) hP hc hS hcut hD hlamB hM hψtop hψW' hoff'
  simp only [hin1'] at hss
  set dA : N.G.Dart × Bool → ℝ≥0∞ := fun z => (outs ((S.levelPad hN).ι (.inl (S.endV z))) (ss z.1.snd) : ℝ≥0∞)
    with hdA
  have hdC : ∀ (d : N.G.Dart) β, dC d.snd ((X d.snd, sc d.snd), ss d.snd) d.fst β =
      outs ((S.levelPad hN).ι (.inl (S.endV (d, β)))) (ss d.snd) := fun d β => by
    simp only [dC, hrot, hown]
    rw [S.cornerName_eq hN d β]
  set mkV : S.hRot.Vertex → Prop := fun u => ∃ a, mk' a ∧ cpT a = (S.levelPad hN).ι (.inl u) with hmkV
  have hdist : ∀ z, dA z = ⨅ u, ⨅ (_ : mkV u), S.arcDist lam M (S.vcopy u) (S.vcopy (S.endV z)) := fun z => by
    have h := hss (S.endV z)
    rw [S.hostOf_endV hN z] at h
    simp only [dA]
    rw [h]
    refine iInf_congr fun u => ?_
    simp only [ψ']
    by_cases hu : ∃ a, mk' a ∧ cpT a = (S.levelPad hN).ι (.inl u)
    · simp [hu, mkV]
    · simp [hu, mkV]
  -- the corners of the marked nodes
  have hreg_c : ∀ q ∈ r.levelQ ℓ, ∀ c, q.1.2.SideC σs c →
      (N.toRot.dual.double.split q.1.1).toHypermap.gcomp (q.1.2.κ0 q.1.2.xa) c := fun q _ c hc =>
    q.1.2.gcomp_bound (q.1.2.κ0_mem le_rfl q.1.2.le_x) (q.1.2.corner_mem (q.1.2.sideC_or hc))
  have hmk : ∀ u, mkV u → ∃ q ∈ r.levelQ ℓ, ∃ y, (N.toRot.dual.double.split q.1.1).toHypermap.gcomp
      (q.1.2.κ0 q.1.2.xa) y ∧ ∃ he : (∃ x : S.Tok, S.IsEnd x.1 (S.vcopy u)), S.pieceOf ⟨_, he⟩ = S.pieceAt y := by
    rintro u ⟨a, ⟨⟨q', hq', c', hc', he', hp'⟩, -⟩, hcu⟩
    obtain ⟨v, hv, hcv⟩ := S.cpId_spec hN a
    obtain rfl : v = u := Sum.inl_injective ((S.levelPad hN).ι_injective (hv.symm.trans hcu))
    have he'' : ∃ x : S.Tok, S.IsEnd x.1 (S.vcopy v) := hcv ▸ he'
    exact ⟨q', hq', c', hreg_c q' hq' c' hc', he'', (S.vtx_copy_iff hN hcv he' he'' c').1 hp'⟩
  have hvcAll : ∀ q ∈ r.levelQ ℓ, ∃ (p : List (N.G.Dart × Bool)) (bv : (N.toRot.dual.double.split q.1.1).Vertex),
      (N.toRot.dual.double.split q.1.1).IsWalk ((N.toRot.dual.double.split q.1.1).tail (q.1.2.κ0 q.2)) p bv ∧
      ∀ c, q.1.2.Visits q.2 p c ↔ ∃ y, (∃ i, (Net.parOf R)^[i] ((S.levelPad hN).ι (.inl (S.endV (q.1.2.κ1 q.2)))) = y) ∧
        ∃ hy : (∃ x : S.Tok, S.IsEnd x.1 (S.copyAt hN y)),
          S.vertexEquiv (S.pieceOf ⟨S.copyAt hN y, hy⟩) = S.dualSplit.tail c := fun q hq => by
    obtain ⟨kk, -, -, hsh, -, -, hvc, -, -⟩ := hex q hq
    exact ⟨_, _, hsh.1, hvc⟩
  have hQ5 : ∀ q ∈ r.levelQ ℓ, q.1 ∈ r.nodes ℓ ∧ q.1.2.xa ≤ q.2 ∧ q.1.2.ya ≤ q.2 ∧ q.2 ≤ q.1.2.xb ∧
      q.2 ≤ q.1.2.yb := hQr
  have hbit : ∀ q ∈ r.levelQ ℓ, ovBit σs (decS (payS q)) = true → ∃ p c, q.1.2.Shortest q.2 p ∧
      q.1.2.SideC σs c ∧ q.1.2.Visits q.2 p c ∧
      ∀ z, (N.toRot.dual.double.split q.1.1).toHypermap.gcomp (q.1.2.κ0 q.1.2.xa) z →
        min (dA z) M = min ((N.toRot.dual.double.split q.1.1).walkDist (Nat.cast ∘ cc ∘ Prod.fst)
          ((N.toRot.dual.double.split q.1.1).tail c) ((N.toRot.dual.double.split q.1.1).tail z)) M := by
    intro q hq hb
    obtain ⟨kk, i1, i2, hsh, hl, hg', hvc, hks, hroot⟩ := hex q hq
    have hdec := ((hpay q hq).2.2 kk i1 i2 hks hroot hl hg').2
    set t := (S.levelPad hN).ι (.inl (S.endV (q.1.2.κ1 q.2))) with ht
    set p := S.chainDarts hN R t 0 kk with hp
    have hside : ∃ c, q.1.2.SideC σs c ∧ q.1.2.Visits q.2 p c := by
      rw [hdec] at hb
      match σs, hb with
      | 0, h => exact of_decide_eq_true h
      | 1, h => exact of_decide_eq_true h
    obtain ⟨c₀, hc₀, hv₀⟩ := hside
    obtain ⟨y, ⟨i, rfl⟩, hy, hye⟩ := (hvc c₀).1 hv₀
    have hfix : Net.parOf R ((Net.parOf R)^[kk] t) = (Net.parOf R)^[kk] t := by
      simp [Net.parOf, hroot]
    have hclamp : (Net.parOf R)^[i] t = (Net.parOf R)^[min i kk] t := by
      rcases le_total i kk with h | h
      · rw [min_eq_left h]
      · obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le h
        rw [min_eq_right h, Nat.add_comm, Function.iterate_add_apply, Function.iterate_fixed hfix]
    have hks' : Net.ParSteps R t (min i kk) := fun l hl => hks l (lt_of_lt_of_le hl (min_le_right _ _))
    have hflag : S.cornerFlag hN (r.levelQ ℓ) P ((Net.parOf R)^[min i kk] t) := by
      rw [← hclamp]
      exact ⟨q, hq, c₀, hc₀, hy, hye⟩
    have htq : S.tgtFlag hN (r.levelQ ℓ) t = true := by
      unfold tgtFlag
      exact decide_eq_true ⟨q, hq, rfl⟩
    obtain ⟨i'', -, hf1, hz1⟩ := S.mark_exists hN (r.levelQ ℓ) P hRs h₂ hT htq hks' hflag
    set a₁ := (Net.parOf R)^[i''] t with ha₁
    obtain ⟨q₁, hq₁, c₁, hc₁, he₁, hp₁⟩ := hf1
    have hv₁ : q.1.2.Visits q.2 p c₁ := (hvc c₁).2 ⟨a₁, ⟨i'', rfl⟩, he₁, hp₁⟩
    have ea : q.1 = q₁.1 := r.corner_eq ℓ (hQr q hq).1 (hQr q₁ hq₁).1 (hQr q hq).2.1 (hQr q hq).2.2.2.1
      hsh.1 hv₁ (q₁.1.2.sideC_or hc₁)
    have hc₁' : q.1.2.SideC σs c₁ := ea ▸ hc₁
    refine ⟨p, c₁, hsh, hc₁', hv₁, fun z hz => ?_⟩
    obtain ⟨v₁, hcv₁, hcopy₁⟩ := S.cpId_spec hN a₁
    have he₁' : ∃ x : S.Tok, S.IsEnd x.1 (S.vcopy v₁) := hcopy₁ ▸ he₁
    have hp₁' := (S.vtx_copy_iff hN hcopy₁ he₁ he₁' c₁).1 hp₁
    have hu₁ : mkV v₁ := ⟨a₁, ⟨⟨q₁, hq₁, c₁, hc₁, he₁, hp₁⟩, hz1⟩, hcv₁⟩
    have huniq : ∀ u, mkV u → ∀ y, (N.toRot.dual.double.split q.1.1).toHypermap.gcomp (q.1.2.κ0 q.1.2.xa) y →
        ∀ he : (∃ x : S.Tok, S.IsEnd x.1 (S.vcopy u)), S.pieceOf ⟨_, he⟩ = S.pieceAt y → u = v₁ := by
      rintro u ⟨a, ⟨hfa, hza⟩, hcu⟩ y' hy' he hpy
      obtain ⟨v, hv, hcv⟩ := S.cpId_spec hN a
      obtain rfl : v = u := Sum.inl_injective ((S.levelPad hN).ι_injective (hv.symm.trans hcu))
      have hea : ∃ x : S.Tok, S.IsEnd x.1 (S.copyAt hN a) := hcv.symm ▸ he
      have e := S.mark_unique hN (r.levelQ ℓ) P hRs h₂ hT hQ5 hQu hvcAll hq hfa hza
        ⟨q₁, hq₁, c₁, hc₁, he₁, hp₁⟩ hz1 hy' (hreg_c q hq c₁ hc₁')
        ⟨hea, (S.vtx_copy_iff hN hcv hea he y').2 hpy⟩ ⟨he₁, hp₁⟩
      exact S.vcopy_injective (hcv.symm.trans (e ▸ hcopy₁))
    rw [hdist z]
    exact S.markDist_region r ℓ lam M cc hcr hlam (fun _ => rfl) hΓ (r.levelQ ℓ) (fun q hq => (hQr q hq).1)
      mkV hmk (hQr q hq).1 hu₁ (hreg_c q hq c₁ hc₁') he₁' hp₁' huniq hz
  intro w
  dsimp only
  -- the run on the faces
  set aV : N.G.Dart × Bool → ℕ∞ := fun z => va z.1.snd ((X z.1.snd, sc z.1.snd), ss z.1.snd) z.1.fst z.2
    with haV
  have hfp := hAf N S hN lam M u₀ hh aV (fun w => va w ((X w, sc w), ss w)) hP hc hD hM1 hM (fun d β => rfl)
  simp only [hin1'] at hfp
  set k0' : N.G.Dart × Bool → ℕ → Bool := fun z t => (X z.1.snd).k0 z.1.fst z.2 t with hk0'
  set k1' : N.G.Dart × Bool → ℕ → Bool := fun z t => (X z.1.snd).k1 z.1.fst z.2 t with hk1'
  have hpz : ∀ z : N.G.Dart × Bool, (X z.1.snd).pT z.1.fst z.2 = pT z ∧ (X z.1.snd).pS z.1.fst z.2 = pS z :=
    fun z => hp z.1 z.2
  have hsrc : ∀ z, (aV z : ℝ≥0∞) = CutPath.ovSrc σs M pT pS k0' dA z := fun z => by
    simp only [aV, va, CutPath.ovSrc, hsd, hbnd, (hpz z).1, (hpz z).2, k0', dA]
    rw [hdC z.1 z.2]
    split_ifs <;> simp
  set fm : N.G.Dart × Bool → ℝ≥0∞ := fun y => (outf y.1.snd (sf y.1.snd) y.1.fst y.2 : ℝ≥0∞) with hfmdef
  have hfm : ∀ y, min (fm y) M = min (⨅ z, ⨅ (_ : N.toRot.dual.tail z.1 = N.toRot.dual.tail y.1),
      CutPath.ovSrc σs M pT pS k0' dA z) M := fun y => by
    rw [show fm y = (outf y.1.snd (sf y.1.snd) y.1.fst y.2 : ℝ≥0∞) from rfl, hfp y.1 y.2]
    simp only [hsrc]
  -- the values of a side at the corners
  have hpayF : ∀ q ∈ r.levelQ ℓ, payT q < M ∧ payS q < M ∧ (decT (payT q)).1 = (rngA r ℓ q.1).1 ∧
      (decT (payT q)).2.1 = (rngA r ℓ q.1).2 := fun q hq => by
    obtain ⟨kk, i1, i2, -, hl, hg', -, hks, hroot⟩ := hex q hq
    have e := ((hpay q hq).2.2 kk i1 i2 hks hroot hl hg').1
    exact ⟨(hpay q hq).1, (hpay q hq).2.1, by rw [e], by rw [e]⟩
  have key := CutPath.ovTgt_eq r ℓ σs M hMl (r.levelQ ℓ) (fun q hq => (hQr q hq).1) hQu
    (fun q => rngA r ℓ q.1) (fun q hq => ⟨(levelQ_rng r ℓ hq).1, (levelQ_rng r ℓ hq).2.1⟩)
    (fun q hq => (levelQ_rng r ℓ hq).2.2) pT pS payT payS hreg hguard hpayF dA hbit k0' k1'
    (fun z t => (hk z.1 z.2 t).1) (fun z t => (hk z.1 z.2 t).2) fm hfm
  have htv : ∀ (d : N.G.Dart) β, d.snd = w →
      (tv w (((X w, sc w), ss w), sf w) d.fst β : ℝ≥0∞) = CutPath.ovTgt σs M pT pS k1' fm dA (d, β) := by
    rintro d β rfl
    simp only [tv, CutPath.ovTgt, hsd, hbnd, (hpz (d, β)).1, (hpz (d, β)).2, k1', dA, fm]
    rw [hdC d β]
    split_ifs <;> simp
  have hmem : ∀ u, u ∈ (X w).lv.rot ↔ N.G.Adj u w := fun u => by
    rw [hrot, ← List.mem_toFinset, ← N.neighborFinset_eq, SimpleGraph.mem_neighborFinset]
    exact ⟨fun h => h.symm, fun h => h.symm⟩
  simp only [ENat.toENNReal_iInf]
  apply le_antisymm
  · refine le_iInf₂ fun q hq => le_iInf fun μ => le_iInf fun hov => le_iInf fun hw => ?_
    refine iInf_le_of_le (q.1.2.κ1 μ).1.fst (iInf_le_of_le ((hmem _).2 (hw ▸ (q.1.2.κ1 μ).1.adj))
      (iInf_le_of_le (q.1.2.κ1 μ).2 ?_))
    rw [htv _ _ hw, Prod.mk.eta, key]
    exact iInf₂_le_of_le q hq (iInf_le_of_le μ (iInf_le_of_le hov (iInf_le_of_le rfl le_rfl)))
  · refine le_iInf fun u => le_iInf fun hu => le_iInf fun β => ?_
    have hd : N.G.Adj u w := (hmem u).1 hu
    have e := htv ⟨(u, w), hd⟩ β rfl
    dsimp only at e
    rw [e, key]
    refine le_iInf₂ fun q hq => le_iInf fun μ => le_iInf fun hov => le_iInf fun hy => ?_
    refine iInf₂_le_of_le q hq (iInf_le_of_le μ (iInf_le_of_le hov (iInf_le_of_le ?_ le_rfl)))
    rw [← hy]

end RData

end RotSystem

end SsspFlow
