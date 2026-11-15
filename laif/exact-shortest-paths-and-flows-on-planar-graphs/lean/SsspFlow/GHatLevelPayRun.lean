import SsspFlow.GHatLevelNodeLocal
import SsspFlow.GHatLevelPay
import SsspFlow.GHatLevelRegion
import SsspFlow.GHatLevelState

/-!
# The values of the annuli of a level at the corners, as one algorithm

After the run of the nodes of a level, each target knows the range of its annulus from the values at
the corners into its host, and its two indices from the run. It puts them into one number, and each
source puts there the two bits of the sides. Two broadcast runs give these numbers to the copies of
all corners in the region of each annulus. A value below the bound at a corner is the value of the
annulus of its region.

* `RData.levelPay_local`: the data of the nodes of a level, and the numbers of the annuli at the
  corners of their regions, from one algorithm with a bound on its rounds.
-/

set_option autoImplicit false

namespace SsspFlow

open FourColor SsspFlow.Congest
open scoped ENNReal

namespace RotSystem

/-- The number of a target from the value at its copy and its two indices. -/
noncomputable def payTL (m : ℕ) (c o1 o2 : ℕ∞) : ℕ∞ :=
  if c = ⊤ then ⊤ else ((encT (c.toNat.unpair.1, c.toNat.unpair.2, o1.toNat, m - o2.toNat) : ℕ) : ℕ∞)

/-- The number of a source from its flag and its two bits. -/
def paySL (c : ℕ∞) (bA bB : Bool) : ℕ∞ := if c = ⊤ then ⊤ else ((encS (bA, bB) : ℕ) : ℕ∞)

namespace RData

open Classical Cslib.Congest.Algorithm in
/-- **The values of the annuli of a level at the corners, as one algorithm.** The algorithm of
`RData.levelNode_local` on the list of the level, then one exchange, then two broadcast runs. Let the
values at the corners numbered `8` be the range of the annulus at its target corner, and the input
carry the length `m` of the cut path. Then there are numbers `payT q` and `payS q` below `M` for every
annulus `q` of the list: the first holds its range and the least and greatest index of every shortest
walk of the chain of its target, the second whether that walk visits a corner of each side. Every
corner in the region of `q` gets both numbers at the identifier of its copy, and a number below `M`
at a corner is that of the annulus of its region. -/
theorem levelPay_local (hE : ExactSsspBound) (K : ℕ) : ∃ C c : ℕ, ∀ n D : ℕ,
    ∃ (σ : Type) (A : Cslib.Congest.Algorithm (Fin n)
        (LevelIn n × ℕ × (ℕ → (Fin n → Bool → ℕ∞) × (Fin n → Bool → ℕ∞))) σ
        (4 * (C * logN (n * (n * 21)) ^ c + 3) + (3 * (K * logN (n * (n * 21)) + 1) + 5)))
      (T : ℕ) (rr r₂ r₃ rA rB : Fin (n * (n * 21)) → σ → ℕ∞ × Option (Fin (n * (n * 21))))
      (o1 o2 : Fin (n * (n * 21)) → σ → ℕ∞) (offO : Fin (n * (n * 21)) → σ → ℕ∞)
      (flgO : Fin (n * (n * 21)) → σ → Bool × Bool × Bool) (cflO : Fin (n * (n * 21)) → σ → Bool × Bool)
      (outT outS : Fin (n * (n * 21)) → σ → ℕ∞),
    T ≤ 26 + 17 * (C * logN (n * (n * 21)) ^ c * (12 * D + 16)) ∧
    ∀ (N : Net (Fin n)) (S : N.toRot.RData) (hN : ∀ u, ∃ w, N.G.Adj u w)
      {Cp : N.toRot.dual.CutPath} {g : N.G.Dart → ℝ≥0∞} {hR : N.toRot.dual.Planar}
      {hC : N.toRot.dual.Connected} {hg : ∀ x, g (N.toRot.dual.rev x) = g x}
      {Γ₀ : Finset (N.G.Dart × Bool)} {L₀ : Cp.Live g Γ₀} {j k : ℕ}
      (r : CutPath.Run hR hC hg Γ₀ L₀ j k) (ℓ : ℕ) (lam : S.Tok → ℕ) (M : ℕ) (cc : N.G.Dart → ℕ)
      (u₀ : S.hRot.Vertex)
      (vals : Fin n → ℕ → (Fin n → Bool → ℕ∞) × (Fin n → Bool → ℕ∞)) (gs : ℕ → N.G.Dart × Bool → ℕ∞)
      (rng : (Σ Γ' : Finset (N.G.Dart × Bool), Cp.Live g Γ') × ℕ → ℕ × ℕ),
      N.toRot.Planar → N.toRot.Connected → S.NoConflict → S.cut.card ≤ 3 → N.DiamLE D →
      (∀ x, lam x ≤ (n * (n * 21) + 2) ^ K) → M ≤ (n * (n * 21) + 2) ^ K →
      (∀ d, 1 ≤ cc d) → (∀ d, cc (N.toRot.rev d) = cc d) → (∀ x, lam x = cc x.1.1) →
      (∀ d, g d = cc d) → S.Γ = Γ₀ ∪ r.steps ℓ →
      (∀ q ∈ (r.levelQ ℓ), Cp.lamD g q.2 < M) →
      1 ≤ M → Cp.m < M → (∀ k z, gs k z = ⊤ ∨ gs k z ≤ (n * (n * 21) + 2) ^ K) →
      (∀ k (d : N.G.Dart) b, (vals d.fst k).1 d.snd b = gs k (d, b)) →
      (∀ k (d : N.G.Dart) b, (vals d.snd k).2 d.fst b = gs k (d, b)) →
      gs 0 = (fun z => ⨅ r ∈ cornerIdx Cp z, (r : ℕ∞)) →
      gs 1 = (fun z => ⨅ r ∈ cornerIdx Cp z, ((Cp.m - r : ℕ) : ℕ∞)) →
      gs 2 = flagVal Cp 0 → gs 3 = flagVal Cp 1 →
      gs 4 = (fun z => if ∃ q ∈ (r.levelQ ℓ), q.1.2.CornerA z then 0 else ⊤) →
      gs 5 = (fun z => if ∃ q ∈ (r.levelQ ℓ), q.1.2.CornerB z then 0 else ⊤) →
      gs 6 = (fun z => if ∃ q ∈ (r.levelQ ℓ), z = qEnd 0 q then 0 else ⊤) →
      gs 7 = (fun z => if ∃ q ∈ (r.levelQ ℓ), z = qEnd 1 q then 0 else ⊤) →
      gs 8 = (fun z => ⨅ q ∈ (r.levelQ ℓ), ⨅ (_ : z = qEnd 1 q), ((Nat.pair (rng q).1 (rng q).2 : ℕ) : ℕ∞)) →
      (∀ q ∈ (r.levelQ ℓ), (rng q).1 ≤ Cp.m ∧ (rng q).2 ≤ Cp.m) → (Cp.m + 2) ^ 8 ≤ M →
      let flg : Fin n → Fin (n * (n * 21)) → Bool × Bool × Bool := fun _ a =>
        (S.tgtFlag hN (r.levelQ ℓ) a, decide (S.nodeFlag hN Cp 0 a), decide (S.nodeFlag hN Cp 1 a))
      let cfl : Fin n → Fin (n * (n * 21)) → Bool × Bool := fun _ a =>
        (decide (S.cornerFlag hN (r.levelQ ℓ) (fun A c => A.2.CornerA c) a), decide (S.cornerFlag hN (r.levelQ ℓ) (fun A c => A.2.CornerB c) a))
      let st := A.run N.G (fun w => (S.levelIn hN lam M u₀ w, Cp.m, vals w)) T
      let R := fun a => rr a (st (hostOf a))
      (∃ payT payS : (Σ Γ' : Finset (N.G.Dart × Bool), Cp.Live g Γ') × ℕ → ℕ,
        (∀ q ∈ (r.levelQ ℓ), payT q < M ∧ payS q < M ∧ ∀ kk i1 i2,
          Net.ParSteps R ((S.levelPad hN).ι (.inl (S.endV (q.1.2.κ1 q.2)))) kk →
          (R ((Net.parOf R)^[kk] ((S.levelPad hN).ι (.inl (S.endV (q.1.2.κ1 q.2)))))).2 = none →
          IsLeast (Cp.idx (q.1.2.κ0 q.2) (S.chainDarts hN R ((S.levelPad hN).ι (.inl (S.endV (q.1.2.κ1 q.2)))) 0 kk))
            i1 →
          IsGreatest (Cp.idx (q.1.2.κ0 q.2) (S.chainDarts hN R ((S.levelPad hN).ι (.inl (S.endV (q.1.2.κ1 q.2)))) 0 kk))
            i2 →
          decT (payT q) = ((rng q).1, (rng q).2, i1, i2) ∧
          decS (payS q) = (decide (∃ c, q.1.2.CornerA c ∧ q.1.2.Visits q.2
              (S.chainDarts hN R ((S.levelPad hN).ι (.inl (S.endV (q.1.2.κ1 q.2)))) 0 kk) c),
            decide (∃ c, q.1.2.CornerB c ∧ q.1.2.Visits q.2
              (S.chainDarts hN R ((S.levelPad hN).ι (.inl (S.endV (q.1.2.κ1 q.2)))) 0 kk) c))) ∧
        (∀ q ∈ (r.levelQ ℓ), ∀ z, (N.toRot.dual.double.split q.1.1).toHypermap.gcomp (q.1.2.κ0 q.1.2.xa) z →
          outT ((S.levelPad hN).ι (.inl (S.endV z))) (st z.1.snd) = payT q ∧
          outS ((S.levelPad hN).ι (.inl (S.endV z))) (st z.1.snd) = payS q) ∧
        (∀ z, outT ((S.levelPad hN).ι (.inl (S.endV z))) (st z.1.snd) < M →
          ∃ q ∈ (r.levelQ ℓ), (N.toRot.dual.double.split q.1.1).toHypermap.gcomp (q.1.2.κ0 q.1.2.xa) z ∧
            outT ((S.levelPad hN).ι (.inl (S.endV z))) (st z.1.snd) = payT q) ∧
        (∀ z, outS ((S.levelPad hN).ι (.inl (S.endV z))) (st z.1.snd) < M →
          ∃ q ∈ (r.levelQ ℓ), (N.toRot.dual.double.split q.1.1).toHypermap.gcomp (q.1.2.κ0 q.1.2.xa) z ∧
            outS ((S.levelPad hN).ι (.inl (S.endV z))) (st z.1.snd) = payS q)) ∧
      (∀ a, offO a (st (hostOf a)) = S.srcOff hN (r.levelQ ℓ) a ∧ flgO a (st (hostOf a)) = flg (hostOf a) a ∧
        cflO a (st (hostOf a)) = cfl (hostOf a) a) ∧
      (S.levelNet hN).ExactSpec (S.levelLen hN lam M) (S.srcOff hN (r.levelQ ℓ)) R ∧
      R = hE.oracleRun K (12 * D + 16) (by omega) (S.levelNet hN) (S.levelLen hN lam M) (S.srcOff hN (r.levelQ ℓ)) ∧
      (S.levelNet hN).ExactSpec (Net.markLenW R fun a => (((flg (hostOf a) a).2.1).toNat : ℕ∞))
        (Net.markOffB fun a => (flg (hostOf a) a).1) (fun a => r₂ a (st (hostOf a))) ∧
      (S.levelNet hN).ExactSpec (Net.downLenW R fun a => (((flg (hostOf a) a).2.2).toNat : ℕ∞))
        (Net.markOffB fun a => (flg (hostOf a) a).2.1 && decide ((r₂ a (st (hostOf a))).1 = 0))
        (fun a => r₃ a (st (hostOf a))) ∧
      ∀ At ∈ (r.levelQ ℓ), ∃ (kk i1 i2 : ℕ) (St : At.1.2.Step),
        At.1.2.Shortest At.2 (S.chainDarts hN R ((S.levelPad hN).ι (.inl (S.endV (At.1.2.κ1 At.2)))) 0 kk) ∧
        IsLeast (Cp.idx (At.1.2.κ0 At.2)
          (S.chainDarts hN R ((S.levelPad hN).ι (.inl (S.endV (At.1.2.κ1 At.2)))) 0 kk)) i1 ∧
        IsGreatest (Cp.idx (At.1.2.κ0 At.2)
          (S.chainDarts hN R ((S.levelPad hN).ι (.inl (S.endV (At.1.2.κ1 At.2)))) 0 kk)) i2 ∧
        min (o1 ((S.levelPad hN).ι (.inl (S.endV (At.1.2.κ1 At.2))))
          (st (hostOf ((S.levelPad hN).ι (.inl (S.endV (At.1.2.κ1 At.2)))))) : ℝ≥0∞) M =
            min (i1 : ℝ≥0∞) M ∧
        min (o2 ((S.levelPad hN).ι (.inl (S.endV (At.1.2.κ1 At.2))))
          (st (hostOf ((S.levelPad hN).ι (.inl (S.endV (At.1.2.κ1 At.2)))))) : ℝ≥0∞) M =
            min ((Cp.m - i2 : ℕ) : ℝ≥0∞) M ∧
        (∀ z, z ∈ (List.range St.n).map St.q ↔ ∃ l,
          Net.ParSteps R ((S.levelPad hN).ι (.inl (S.endV (At.1.2.κ1 At.2)))) (l + 1) ∧
          (r₂ ((Net.parOf R)^[l] ((S.levelPad hN).ι (.inl (S.endV (At.1.2.κ1 At.2)))))
            (st (hostOf ((Net.parOf R)^[l] ((S.levelPad hN).ι (.inl (S.endV (At.1.2.κ1 At.2)))))))).1 = 0 ∧
          (flg (hostOf ((Net.parOf R)^[l] ((S.levelPad hN).ι (.inl (S.endV (At.1.2.κ1 At.2))))))
            ((Net.parOf R)^[l] ((S.levelPad hN).ι (.inl (S.endV (At.1.2.κ1 At.2)))))).2.1 = false ∧
          (r₃ ((Net.parOf R)^[l] ((S.levelPad hN).ι (.inl (S.endV (At.1.2.κ1 At.2)))))
            (st (hostOf ((Net.parOf R)^[l] ((S.levelPad hN).ι (.inl (S.endV (At.1.2.κ1 At.2)))))))).1 = 0 ∧
          ∃ x, S.edgeTok hN ((Net.parOf R)^[l + 1] ((S.levelPad hN).ι (.inl (S.endV (At.1.2.κ1 At.2)))))
              ((Net.parOf R)^[l] ((S.levelPad hN).ι (.inl (S.endV (At.1.2.κ1 At.2))))) = some x ∧
            z = N.toRot.tokDart x.1) ∧
        (∃ p₁ p₃, S.chainDarts hN R ((S.levelPad hN).ι (.inl (S.endV (At.1.2.κ1 At.2)))) 0 kk =
          p₁ ++ (List.range St.n).map St.q ++ p₃) ∧
        (∀ c, At.1.2.Visits At.2 (S.chainDarts hN R ((S.levelPad hN).ι (.inl (S.endV (At.1.2.κ1 At.2)))) 0 kk) c ↔
          ∃ y, (∃ i, (Net.parOf R)^[i] ((S.levelPad hN).ι (.inl (S.endV (At.1.2.κ1 At.2)))) = y) ∧
            ∃ hy : (∃ x : S.Tok, S.IsEnd x.1 (S.copyAt hN y)),
              S.vertexEquiv (S.pieceOf ⟨S.copyAt hN y, hy⟩) = S.dualSplit.tail c) ∧
        Net.ParSteps R ((S.levelPad hN).ι (.inl (S.endV (At.1.2.κ1 At.2)))) kk ∧ (R ((Net.parOf R)^[kk] ((S.levelPad hN).ι (.inl (S.endV (At.1.2.κ1 At.2)))))).2 = none ∧
        ((∃ c, At.1.2.CornerA c ∧ At.1.2.Visits At.2 (S.chainDarts hN R ((S.levelPad hN).ι (.inl (S.endV (At.1.2.κ1 At.2)))) 0 kk) c) ↔
          (rA ((Net.parOf R)^[kk] ((S.levelPad hN).ι (.inl (S.endV (At.1.2.κ1 At.2))))) (st (hostOf ((Net.parOf R)^[kk] ((S.levelPad hN).ι (.inl (S.endV (At.1.2.κ1 At.2)))))))).1 ≠ 0 ∨ (cfl (hostOf ((Net.parOf R)^[kk] ((S.levelPad hN).ι (.inl (S.endV (At.1.2.κ1 At.2)))))) ((Net.parOf R)^[kk] ((S.levelPad hN).ι (.inl (S.endV (At.1.2.κ1 At.2)))))).1 = true) ∧
        ((∃ c, At.1.2.CornerB c ∧ At.1.2.Visits At.2 (S.chainDarts hN R ((S.levelPad hN).ι (.inl (S.endV (At.1.2.κ1 At.2)))) 0 kk) c) ↔
          (rB ((Net.parOf R)^[kk] ((S.levelPad hN).ι (.inl (S.endV (At.1.2.κ1 At.2))))) (st (hostOf ((Net.parOf R)^[kk] ((S.levelPad hN).ι (.inl (S.endV (At.1.2.κ1 At.2)))))))).1 ≠ 0 ∨ (cfl (hostOf ((Net.parOf R)^[kk] ((S.levelPad hN).ι (.inl (S.endV (At.1.2.κ1 At.2)))))) ((Net.parOf R)^[kk] ((S.levelPad hN).ι (.inl (S.endV (At.1.2.κ1 At.2)))))).2 = true) := by
  obtain ⟨C₂, c₂, hNL⟩ := levelNode_local hE K
  obtain ⟨C₃, c₃, hBR⟩ := levelBcast_region hE K
  refine ⟨C₂ + C₃, c₂ + c₃, fun n D => ?_⟩
  set b := K * logN (n * (n * 21)) + 1 with hbdef
  obtain ⟨σ₂, A₂, T₂, rr, r₂, r₃, rA, rB, o1, o2, offO, flgO, cflO, hT₂, hA₂⟩ := hNL n D
  obtain ⟨σ₃, A₃, out₃, hA₃⟩ := hBR n D
  have hL : 1 ≤ logN (n * (n * 21)) := by unfold logN; omega
  have hp₂ : logN (n * (n * 21)) ^ c₂ ≤ logN (n * (n * 21)) ^ (c₂ + c₃) := Nat.pow_le_pow_right hL (by omega)
  have hp₃ : logN (n * (n * 21)) ^ c₃ ≤ logN (n * (n * 21)) ^ (c₂ + c₃) := Nat.pow_le_pow_right hL (by omega)
  have hm₂ := Nat.mul_le_mul (show C₂ ≤ C₂ + C₃ by omega) hp₂
  have hm₃ := Nat.mul_le_mul (show C₃ ≤ C₂ + C₃ by omega) hp₃
  set W := 4 * ((C₂ + C₃) * logN (n * (n * 21)) ^ (c₂ + c₃) + 3) + (3 * b + 5) with hW
  have w₂ : 4 * (C₂ * logN (n * (n * 21)) ^ c₂ + 3) + (3 * b + 5) ≤ W := by omega
  have w₃ : 4 * (C₃ * logN (n * (n * 21)) ^ c₃) + (3 * b + 5) ≤ W := by omega
  set T₃ := 1 + C₃ * logN (n * (n * 21)) ^ c₃ * (12 * D + 16) with hT₃
  let J := LevelIn n × ℕ × (ℕ → (Fin n → Bool → ℕ∞) × (Fin n → Bool → ℕ∞))
  let P := (J × σ₂) × ((Fin n → ℕ) × (Fin n → Option ℕ))
  let offTL : Fin n → P → Fin (n * (n * 21)) → ℕ∞ := fun w p a =>
    payTL p.1.1.2.1 (u0Test b w p.1.1.1 (p.1.1.2.2 8).2 p.2.2 a) (o1 a p.1.2) (o2 a p.1.2)
  let offSL : Fin n → P → Fin (n * (n * 21)) → ℕ∞ := fun _ p a =>
    paySL (offO a p.1.2) (decide ((rA a p.1.2).1 ≠ 0) || (cflO a p.1.2).1)
      (decide ((rB a p.1.2).1 ≠ 0) || (cflO a p.1.2).2)
  let B₁ := (A₂.widen w₂).keep (fun _ (i : J) => (i.1, i.2.2))
  let Bx := (exchTo (Fin n) W).keep (fun _ (q : J × σ₂) => q.1.1.msg b)
  let BT := (A₃.widen w₃).keep (fun w (q : P) => (q.1.1.1.withConst 0, offTL w q))
  let BS := (A₃.widen w₃).keep (fun w (q : P × σ₃) => (q.1.1.1.1.withConst 0, offSL w q.1))
  let A := B₁.seq T₂ (fun _ s => s) (Bx.seq 1 (fun _ s => s) (BT.seq T₃ (fun _ s => s) BS))
  let fin : ∀ {β : Type}, β → ((P × σ₃) × σ₃ → β) →
      ((ℕ × (J × σ₂)) ⊕ ((ℕ × P) ⊕ ((ℕ × (P × σ₃)) ⊕ ((P × σ₃) × σ₃)))) → β :=
    fun d F => Sum.elim (fun _ => d) (Sum.elim (fun _ => d) (Sum.elim (fun _ => d) F))
  refine ⟨_, A, T₂ + (1 + (T₃ + T₃)),
    fun a => fin (⊤, none) (fun q => rr a q.1.1.1.2), fun a => fin (⊤, none) (fun q => r₂ a q.1.1.1.2),
    fun a => fin (⊤, none) (fun q => r₃ a q.1.1.1.2), fun a => fin (⊤, none) (fun q => rA a q.1.1.1.2),
    fun a => fin (⊤, none) (fun q => rB a q.1.1.1.2), fun a => fin 0 (fun q => o1 a q.1.1.1.2),
    fun a => fin 0 (fun q => o2 a q.1.1.1.2), fun a => fin ⊤ (fun q => offO a q.1.1.1.2),
    fun a => fin (false, false, false) (fun q => flgO a q.1.1.1.2),
    fun a => fin (false, false) (fun q => cflO a q.1.1.1.2),
    fun a => fin ⊤ (fun q => out₃ a q.1.2), fun a => fin ⊤ (fun q => out₃ a q.2), ?_, ?_⟩
  · have h : C₃ * logN (n * (n * 21)) ^ c₃ * (12 * D + 16) ≤
        (C₂ + C₃) * logN (n * (n * 21)) ^ (c₂ + c₃) * (12 * D + 16) := Nat.mul_le_mul_right _ hm₃
    have h' : C₂ * logN (n * (n * 21)) ^ c₂ * (12 * D + 16) ≤
        (C₂ + C₃) * logN (n * (n * 21)) ^ (c₂ + c₃) * (12 * D + 16) := Nat.mul_le_mul_right _ hm₂
    omega
  intro N S hN Cp g hR hC hg Γ₀ L₀ j k r ℓ lam M cc u₀ vals gs rng hP hc hS hcut hD hlam hM hc1 hcr hlc hgc hΓ
    hQM hM1 hmM hgs hvo hvi h0 h1 h2 h3 h4 h5 h6 h7 h8 hrng hM8
  have hb : ∀ x, lam x < 2 ^ b := fun x => lam_lt_pow (hlam x)
  have hmsg : ∀ u w, (S.levelIn hN lam M u₀ u).msg b w < 2 ^ W := fun u w =>
    (DInfo.pack_lt _ (S.lamAt_lt lam hb _ _ _) (S.lamAt_lt lam hb _ _ _) (S.lamAt_lt lam hb _ _ _)).trans_le
      (Nat.pow_le_pow_right (by norm_num) (by omega))
  have hQ : ∀ q ∈ r.levelQ ℓ, q.1 ∈ r.nodes ℓ ∧ q.1.2.xa ≤ q.2 ∧ q.1.2.ya ≤ q.2 ∧ q.2 ≤ q.1.2.xb ∧
      q.2 ≤ q.1.2.yb ∧ Cp.lamD g q.2 < M := fun q hq => by
    obtain ⟨a1, a2, a3, a4, a5⟩ := r.levelQ_range ℓ q hq
    exact ⟨a1, a2, a3, a4, a5, hQM q hq⟩
  set st₂ := A₂.run N.G (fun w => (S.levelIn hN lam M u₀ w, vals w)) T₂ with hst₂
  obtain ⟨hloc, hRe, hnode'⟩ := hA₂ N S hN r ℓ lam M cc u₀ (r.levelQ ℓ) vals gs hP hc hS hcut hD hlam hM hc1
    hcr hlc hgc hΓ hQ (r.levelQ_uniq ℓ) hM1 hmM hgs hvo hvi h0 h1 h2 h3 h4 h5 h6 h7
  have hAt := hnode'.2.2.2
  set Pv : Fin n → P := fun w => (((S.levelIn hN lam M u₀ w, Cp.m, vals w), st₂ w),
    ((S.levelIn hN lam M u₀ w).msg b, S.levelRecv hN lam M b u₀ w)) with hPv
  set stT := A₃.run N.G (fun w => ((S.levelIn hN lam M u₀ w).withConst 0, offTL w (Pv w))) T₃ with hstT
  set stS := A₃.run N.G (fun w => ((S.levelIn hN lam M u₀ w).withConst 0, offSL w (Pv w))) T₃ with hstS
  have hrun : A.run N.G (fun w => (S.levelIn hN lam M u₀ w, Cp.m, vals w)) (T₂ + (1 + (T₃ + T₃))) =
      fun w => .inr (.inr (.inr ((Pv w, stT w), stS w))) := by
    funext w
    simp only [A, B₁, Bx, BT, BS, run_seq, run_keep, run_widen, run_exchTo N.G _ hmsg]
    rfl
  have hcode : ∀ a, u0Test b (hostOf a) (S.levelIn hN lam M u₀ (hostOf a)) (vals (hostOf a) 8).2
      (S.levelRecv hN lam M b u₀ (hostOf a)) a =
        S.endVal hN r ℓ 1 (fun q => Nat.pair (rng q).1 (rng q).2) a := fun a => by
    rw [S.locTest_eq hN lam M hb u₀ (gs 8) (fun w => (vals w 8).2) (hvi 8) a]
    exact S.onCopies_endPay hN r ℓ 1 _ (gs 8) (fun z => by rw [h8]) a
  have hoff' : ∀ a, offO a (st₂ (hostOf a)) = S.srcOff hN (r.levelQ ℓ) a := fun a => (hloc a).1
  have hcfl' : ∀ a, cflO a (st₂ (hostOf a)) =
      (decide (S.cornerFlag hN (r.levelQ ℓ) (fun A c => A.2.CornerA c) a),
        decide (S.cornerFlag hN (r.levelQ ℓ) (fun A c => A.2.CornerB c) a)) := fun a => (hloc a).2.2
  have hsrc : ∀ a, S.srcOff hN (r.levelQ ℓ) a = S.endVal hN r ℓ 0 (fun _ => 0) a := fun a => by
    unfold srcOff
    split_ifs with h
    · obtain ⟨q, hq, rfl⟩ := h
      have e := S.endVal_end hN r ℓ hΓ 0 (fun _ => 0) hq
      simp only [qEnd, ↓reduceIte] at e
      rw [e]
      rfl
    · by_contra h'
      obtain ⟨q, hq, e⟩ := S.endVal_ne_top hN r ℓ 0 (fun _ => 0) (Ne.symm h')
      exact h ⟨q, hq, by simpa [qEnd] using e⟩
  have decap : ∀ (x : ℕ∞) (y : ℕ), y < M → min (x : ℝ≥0∞) M = min ((y : ℕ) : ℝ≥0∞) M → x = y := by
    intro x y hy h
    have hy' : ((y : ℕ) : ℝ≥0∞) < M := by exact_mod_cast hy
    rw [min_eq_left hy'.le] at h
    have hx : (x : ℝ≥0∞) < M := by
      by_contra hc
      rw [not_lt] at hc
      rw [min_eq_right hc] at h
      exact absurd h (ne_of_gt hy')
    rw [min_eq_left hx.le] at h
    have h' : (x : ℝ≥0∞) = ((y : ℕ∞) : ℝ≥0∞) := by rw [h]; simp
    exact ENat.toENNReal_inj.1 h'
  let F_T : Fin (n * (n * 21)) → ℕ∞ → ℕ∞ := fun a c =>
    payTL Cp.m c (o1 a (st₂ (hostOf a))) (o2 a (st₂ (hostOf a)))
  let F_S : Fin (n * (n * 21)) → ℕ∞ → ℕ∞ := fun a c =>
    paySL c (decide ((rA a (st₂ (hostOf a))).1 ≠ 0) || (cflO a (st₂ (hostOf a))).1)
      (decide ((rB a (st₂ (hostOf a))).1 ≠ 0) || (cflO a (st₂ (hostOf a))).2)
  let payT : (Σ Γ' : Finset (N.G.Dart × Bool), Cp.Live g Γ') × ℕ → ℕ := fun q =>
    (F_T ((S.levelPad hN).ι (.inl (S.endV (q.1.2.κ1 q.2)))) ((Nat.pair (rng q).1 (rng q).2 : ℕ) : ℕ∞)).toNat
  let payS : (Σ Γ' : Finset (N.G.Dart × Bool), Cp.Live g Γ') × ℕ → ℕ := fun q =>
    (F_S ((S.levelPad hN).ι (.inl (S.endV (q.1.2.κ0 q.2)))) ((0 : ℕ) : ℕ∞)).toNat
  have hoffT : ∀ a, offTL (hostOf a) (Pv (hostOf a)) a = S.endVal hN r ℓ 1 payT a := fun a => by
    show F_T a (u0Test b (hostOf a) (S.levelIn hN lam M u₀ (hostOf a)) (vals (hostOf a) 8).2
      (S.levelRecv hN lam M b u₀ (hostOf a)) a) = _
    rw [hcode a]
    exact S.endVal_map hN r ℓ hΓ 1 _ F_T (fun a => by simp [F_T, payTL]) (fun q _ => by simp [F_T, payTL]) a
  have hoffS : ∀ a, offSL (hostOf a) (Pv (hostOf a)) a = S.endVal hN r ℓ 0 payS a := fun a => by
    show F_S a (offO a (st₂ (hostOf a))) = _
    rw [hoff' a, hsrc a]
    exact S.endVal_map hN r ℓ hΓ 0 _ F_S (fun a => by simp [F_S, paySL]) (fun q _ => by simp [F_S, paySL]) a
  have hpayT : ∀ q ∈ r.levelQ ℓ, ∀ i1 i2 : ℕ,
      min (o1 ((S.levelPad hN).ι (.inl (S.endV (q.1.2.κ1 q.2))))
        (st₂ (hostOf ((S.levelPad hN).ι (.inl (S.endV (q.1.2.κ1 q.2)))))) : ℝ≥0∞) M = min (i1 : ℝ≥0∞) M →
      min (o2 ((S.levelPad hN).ι (.inl (S.endV (q.1.2.κ1 q.2))))
        (st₂ (hostOf ((S.levelPad hN).ι (.inl (S.endV (q.1.2.κ1 q.2)))))) : ℝ≥0∞) M =
          min ((Cp.m - i2 : ℕ) : ℝ≥0∞) M →
      i1 ≤ Cp.m → i2 ≤ Cp.m → payT q = encT ((rng q).1, (rng q).2, i1, i2) ∧ payT q < M :=
    fun q hq i1 i2 ho1 ho2 hi1 hi2 => by
      have e1 := decap _ _ (lt_of_le_of_lt hi1 hmM) ho1
      have e2 := decap _ _ (lt_of_le_of_lt (Nat.sub_le _ _) hmM) ho2
      have ep : payT q = encT ((rng q).1, (rng q).2, i1, i2) := by
        simp only [payT, F_T, payTL, e1, e2, ENat.natCast_ne_top, ite_false, ENat.toNat_natCast, Nat.unpair_pair,
          Nat.sub_sub_self hi2]
      refine ⟨ep, ?_⟩
      rw [ep]
      exact (encT_lt (hrng q hq).1 (hrng q hq).2 hi1 hi2).trans_le hM8
  have hlt : ∀ q ∈ r.levelQ ℓ, payT q < M ∧ payS q < M := fun q hq => by
    obtain ⟨kk, i1, i2, St, -, hl, hgr, ho1, ho2, -⟩ := hAt q hq
    refine ⟨(hpayT q hq i1 i2 ho1 ho2 hl.1.1 hgr.1.1).2, ?_⟩
    have : payS q < 4 := by
      simp only [payS, F_S, paySL, ENat.natCast_ne_top, ite_false, ENat.toNat_natCast]
      exact encS_lt _
    have h4 : 4 ≤ M := le_trans (by
      calc 4 ≤ 2 ^ 8 := by norm_num
        _ ≤ (Cp.m + 2) ^ 8 := Nat.pow_le_pow_left (by omega) 8) hM8
    omega
  have hTb := hA₃ N S hN M u₀ (fun w => offTL w (Pv w)) hP hc hS hcut hD hM1 hM r ℓ hΓ 1 payT
    (fun q hq => (hlt q hq).1.le) hoffT
  have hSb := hA₃ N S hN M u₀ (fun w => offSL w (Pv w)) hP hc hS hcut hD hM1 hM r ℓ hΓ 0 payS
    (fun q hq => (hlt q hq).2.le) hoffS
  simp only [S.levelIn_const hN lam M 0 u₀, S.hostOf_endV] at hTb hSb
  rw [hrun]
  intro flg cfl st R
  refine ⟨⟨payT, payS, fun q hq => ⟨(hlt q hq).1, (hlt q hq).2, fun kk i1 i2 hs hn hl hgr => ?_⟩,
    fun q hq z hz => ⟨hTb.1 q hq z hz, hSb.1 q hq z hz⟩, fun z hz => hTb.2 z hz, fun z hz => hSb.2 z hz⟩, ?_⟩
  · obtain ⟨kk', i1', i2', St, -, hl', hgr', ho1, ho2, -, -, -, hs', hn', hvA, hvB⟩ := hAt q hq
    have ekk : kk = kk' := Net.parSteps_root_unique hs hn hs' hn'
    subst ekk
    have ei1 : i1 = i1' := hl.unique hl'
    have ei2 : i2 = i2' := hgr.unique hgr'
    subst ei1 ei2
    refine ⟨?_, ?_⟩
    · rw [(hpayT q hq i1 i2 ho1 ho2 hl.1.1 hgr.1.1).1, decT_encT]
    · have hroot := S.root_eq_src hN r ℓ lam M cc hcr hlc hgc hΓ (r.levelQ ℓ) hQ (r.levelQ_uniq ℓ) _ hRe hq hs' hn'
      rw [hroot] at hvA hvB
      simp only [decide_eq_true_eq] at hvA hvB
      have ep : payS q = encS (decide ((rA ((S.levelPad hN).ι (.inl (S.endV (q.1.2.κ0 q.2))))
            (st₂ (hostOf ((S.levelPad hN).ι (.inl (S.endV (q.1.2.κ0 q.2))))))).1 ≠ 0) ||
          (cflO ((S.levelPad hN).ι (.inl (S.endV (q.1.2.κ0 q.2))))
            (st₂ (hostOf ((S.levelPad hN).ι (.inl (S.endV (q.1.2.κ0 q.2))))))).1,
          decide ((rB ((S.levelPad hN).ι (.inl (S.endV (q.1.2.κ0 q.2))))
            (st₂ (hostOf ((S.levelPad hN).ι (.inl (S.endV (q.1.2.κ0 q.2))))))).1 ≠ 0) ||
          (cflO ((S.levelPad hN).ι (.inl (S.endV (q.1.2.κ0 q.2))))
            (st₂ (hostOf ((S.levelPad hN).ι (.inl (S.endV (q.1.2.κ0 q.2))))))).2) := by
        simp only [payS, F_S, paySL, ENat.natCast_ne_top, ite_false, ENat.toNat_natCast]
      rw [ep, decS_encS, hcfl']
      refine Prod.ext ?_ ?_
      · rw [Bool.eq_iff_iff]
        simp only [Bool.or_eq_true, decide_eq_true_eq]
        exact hvA.symm
      · rw [Bool.eq_iff_iff]
        simp only [Bool.or_eq_true, decide_eq_true_eq]
        exact hvB.symm
  · exact ⟨hloc, hRe, hnode'⟩

end RData

end RotSystem

end SsspFlow
