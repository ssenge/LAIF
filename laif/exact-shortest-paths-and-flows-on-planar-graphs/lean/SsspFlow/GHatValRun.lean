import SsspFlow.GHatValLow
import SsspFlow.GHatLevelOff
import SsspFlow.GHatLevelFlags

/-!
# The lengths at the targets of a list of annuli, as one algorithm

For a list `Q` of annuli of a level with one index `t` each, every node holds at the corners of the
darts into it a flag for the source corners `κ0(t)` and one for the target corners `κ1(t)`. One
exchange of the inputs of the level gives the offsets of the sources and the flags of the targets at
the copies, and one run of the oracle the distances. At the end each node holds the least distance
at the targets it hosts, which is the least `λ_t` of the annuli of `Q` whose target it hosts.

* `RData.levelQRun_local`: the algorithm and its output.
-/

set_option autoImplicit false

namespace SsspFlow

open FourColor SsspFlow.Congest
open scoped ENNReal

namespace RotSystem

namespace RData

open Classical Cslib.Congest.Algorithm in
/-- **The lengths at the targets, as one algorithm.** Assuming the Exact SSSP bound, one algorithm of
the message model on `N`, fixed before the network, starts from the inputs of a level and, at each
node, the flags of the source and the target corners at the corners of the darts into it, for a list
`Q` of annuli of the level with one index `t` each in their ranges and `λ_t < M`. After
`2 + C log^c n' (12 D + 16)` rounds every node `w` holds the least `λ_t` of the annuli of `Q` whose
target copy it hosts, and `⊤` if there is none. -/
theorem levelQRun_local (hE : ExactSsspBound) (K : ℕ) : ∃ C c : ℕ, ∀ n D : ℕ,
    ∃ (σ : Type) (A : Cslib.Congest.Algorithm (Fin n)
        (LevelIn n × (Fin n → Bool → ℕ∞) × (Fin n → Bool → ℕ∞)) σ
      (4 * (C * logN (n * (n * 21)) ^ c) + (3 * (K * logN (n * (n * 21)) + 1) + 5)))
      (vmin : Fin n → σ → ℕ∞),
    ∀ (N : Net (Fin n)) (S : N.toRot.RData) (hN : ∀ u, ∃ w, N.G.Adj u w) (lam : S.Tok → ℕ) (M : ℕ)
      (u₀ : S.hRot.Vertex) {C' : N.toRot.dual.CutPath} {g : N.G.Dart → ℝ≥0∞}
      {hR : N.toRot.dual.Planar} {hC : N.toRot.dual.Connected} {hg : ∀ x, g (N.toRot.dual.rev x) = g x}
      {Γ₀ : Finset (N.G.Dart × Bool)} {L₀ : C'.Live g Γ₀} {j k : ℕ}
      (r : CutPath.Run hR hC hg Γ₀ L₀ j k) (ℓ : ℕ) (cw : N.G.Dart → ℕ)
      (Q : List ((Σ Γ' : Finset (N.G.Dart × Bool), C'.Live g Γ') × ℕ))
      (v6 v7 : Fin n → Fin n → Bool → ℕ∞),
      N.toRot.Planar → N.toRot.Connected → S.NoConflict → S.cut.card ≤ 3 → N.DiamLE D →
      (∀ x, lam x ≤ (n * (n * 21) + 2) ^ K) → M ≤ (n * (n * 21) + 2) ^ K →
      (∀ d, cw (N.toRot.rev d) = cw d) → (∀ x, lam x = cw x.1.1) → (∀ d, g d = cw d) →
      S.Γ = Γ₀ ∪ r.steps ℓ →
      (∀ q ∈ Q, q.1 ∈ r.nodes ℓ ∧ q.1.2.xa ≤ q.2 ∧ q.1.2.ya ≤ q.2 ∧ q.2 ≤ q.1.2.xb ∧
        q.2 ≤ q.1.2.yb ∧ C'.lamD g q.2 < M) →
      (∀ q ∈ Q, ∀ q' ∈ Q, q.1 = q'.1 → q.2 = q'.2) →
      (∀ (d : N.G.Dart) b, v6 d.snd d.fst b = if ∃ q ∈ Q, (d, b) = qEnd 0 q then 0 else ⊤) →
      (∀ (d : N.G.Dart) b, v7 d.snd d.fst b = if ∃ q ∈ Q, (d, b) = qEnd 1 q then 0 else ⊤) →
      ∀ w, (vmin w (A.run N.G (fun w => (S.levelIn hN lam M u₀ w, v6 w, v7 w))
          (2 + C * logN (n * (n * 21)) ^ c * (12 * D + 16)) w) : ℝ≥0∞) =
        ⨅ q ∈ Q, ⨅ (_ : hostOf ((S.levelPad hN).ι (.inl (S.endV (q.1.2.κ1 q.2)))) = w), C'.lamD g q.2 := by
  obtain ⟨C, c, hOff⟩ := levelSsspOff_local hE K
  refine ⟨C, c, fun n D => ?_⟩
  set b := K * logN (n * (n * 21)) + 1
  set Bw := 4 * (C * logN (n * (n * 21)) ^ c) + (3 * b + 5)
  obtain ⟨σ', A', out', hA'⟩ := hOff n D
  let J := LevelIn n × (Fin n → Bool → ℕ∞) × (Fin n → Bool → ℕ∞)
  let A₁ := (exchTo (Fin n) Bw).keep (fun _ (x : J) => x.1.msg b)
  let f₁ : Fin n → J × ((Fin n → ℕ) × (Fin n → Option ℕ)) →
      (LevelIn n × (Fin (n * (n * 21)) → ℕ∞)) × (Fin (n * (n * 21)) → Bool) :=
    fun w s => ((s.1.1, fun a => u0Test b w s.1.1 s.1.2.1 s.2.2 a),
      fun a => decide (u0Test b w s.1.1 s.1.2.2 s.2.2 a = 0))
  let A₂ := A'.keep (fun _ (x : (LevelIn n × (Fin (n * (n * 21)) → ℕ∞)) × (Fin (n * (n * 21)) → Bool)) => x.1)
  refine ⟨_, A₁.seq 1 f₁ A₂, fun w s => match s with
    | .inr s' => ⨅ a, ⨅ (_ : hostOf a = w ∧ s'.1.2 a = true), out' a s'.2
    | .inl _ => ⊤, ?_⟩
  intro N S hN lam M u₀ C' g hR hC hg Γ₀ L₀ j k r ℓ cw Q v6 v7 hP hc hS hcut hD hlam hM hcr hlc hgc hΓ hQ hQu
    h6 h7 w
  have hb : ∀ x, lam x < 2 ^ b := fun x => lam_lt_pow (hlam x)
  have hmsg : ∀ u w, (S.levelIn hN lam M u₀ u).msg b w < 2 ^ Bw := fun u w =>
    (DInfo.pack_lt _ (S.lamAt_lt lam hb _ _ _) (S.lamAt_lt lam hb _ _ _) (S.lamAt_lt lam hb _ _ _)).trans_le
      (Nat.pow_le_pow_right (by norm_num) (by omega))
  have hex : (fun w => f₁ w (A₁.run N.G (fun w => (S.levelIn hN lam M u₀ w, v6 w, v7 w)) 1 w)) =
      fun w => ((S.levelIn hN lam M u₀ w, fun a => u0Test b w (S.levelIn hN lam M u₀ w) (v6 w)
          (S.levelRecv hN lam M b u₀ w) a),
        fun a => decide (u0Test b w (S.levelIn hN lam M u₀ w) (v7 w) (S.levelRecv hN lam M b u₀ w) a = 0)) := by
    funext w
    show f₁ w (((exchTo (Fin n) Bw).keep (fun _ (x : J) => x.1.msg b)).run N.G _ 1 w) = _
    rw [run_keep]
    show f₁ w ((S.levelIn hN lam M u₀ w, v6 w, v7 w), (exchTo (Fin n) Bw).run N.G _ 1 w) = _
    rw [run_exchTo N.G _ hmsg]
    rfl
  -- the offsets and the flags at the hosts
  have hoff : ∀ a, u0Test b (hostOf a) (S.levelIn hN lam M u₀ (hostOf a)) (v6 (hostOf a))
      (S.levelRecv hN lam M b u₀ (hostOf a)) a = S.srcOff hN Q a := fun a => by
    rw [S.locTest_eq hN lam M hb u₀ (fun z => if ∃ q ∈ Q, z = qEnd 0 q then 0 else ⊤) v6
      (fun d c => h6 d c) a]
    exact S.srcOff_eq hN Q _ (fun z => rfl) a
  have htf : ∀ a, decide (u0Test b (hostOf a) (S.levelIn hN lam M u₀ (hostOf a)) (v7 (hostOf a))
      (S.levelRecv hN lam M b u₀ (hostOf a)) a = 0) = S.tgtFlag hN Q a := fun a => by
    rw [S.locTest_eq hN lam M hb u₀ (fun z => if ∃ q ∈ Q, z = qEnd 1 q then 0 else ⊤) v7
      (fun d c => h7 d c) a]
    exact S.tgtFlag_eq hN Q _ (fun z => rfl) a
  have hψ : ∀ z, (∀ u, z ≠ (S.levelPad hN).ι (.inl u)) → S.srcOff hN Q z = ⊤ := fun z hz => by
    unfold srcOff
    refine ite_eq_right_of_eq_false _ _ (eq_false ?_)
    rintro ⟨q', -, rfl⟩
    exact hz _ rfl
  have hψW : ∀ z, S.srcOff hN Q z = ⊤ ∨ S.srcOff hN Q z ≤ (n * (n * 21) + 2) ^ K := fun z => by
    unfold srcOff
    split_ifs
    · exact .inr zero_le
    · exact .inl rfl
  -- the run of the oracle
  have hW : 1 ≤ (n * (n * 21) + 2) ^ K := Nat.one_le_pow _ _ (by omega)
  have hNP := S.levelNet_planar hN hP hc hS hcut hD
  have hND := S.levelNet_diam hN hcut hD
  have hval : OracleValid (S.levelNet hN) 0 ((n * (n * 21) + 2) ^ K) (S.levelLen hN lam M) (S.srcOff hN Q) :=
    ⟨(S.oracleValid_level hN lam M hlam hM u₀).1, hψW⟩
  obtain ⟨R, hr⟩ : ∃ R, (S.levelNet hN).ExactSpec (S.levelLen hN lam M) (S.srcOff hN Q) R :=
    ⟨_, hE.alg_spec K _ (12 * D + 16) (by omega) _ _ _ hNP hND hval⟩
  have hT := S.tgt_dist_eq hN r ℓ lam M cw hcr hlc hgc hΓ Q hQ hQu R hr
  -- the output at the copies
  have hrun : (A₁.seq 1 f₁ A₂).run N.G (fun w => (S.levelIn hN lam M u₀ w, v6 w, v7 w))
      (2 + C * logN (n * (n * 21)) ^ c * (12 * D + 16)) w =
      .inr (((S.levelIn hN lam M u₀ w, fun a => u0Test b w (S.levelIn hN lam M u₀ w) (v6 w)
          (S.levelRecv hN lam M b u₀ w) a),
        fun a => decide (u0Test b w (S.levelIn hN lam M u₀ w) (v7 w) (S.levelRecv hN lam M b u₀ w) a = 0)),
        A'.run N.G (fun w => (S.levelIn hN lam M u₀ w, fun a => u0Test b w (S.levelIn hN lam M u₀ w) (v6 w)
          (S.levelRecv hN lam M b u₀ w) a)) (1 + C * logN (n * (n * 21)) ^ c * (12 * D + 16)) w) := by
    rw [show 2 + C * logN (n * (n * 21)) ^ c * (12 * D + 16) =
      1 + (1 + C * logN (n * (n * 21)) ^ c * (12 * D + 16)) by omega, run_seq, hex]
    show Sum.inr ((A'.keep _).run N.G _ _ w) = _
    rw [run_keep]
  have hcopy : ∀ v : S.hRot.Vertex,
      (out' ((S.levelPad hN).ι (.inl v)) (A'.run N.G (fun w => (S.levelIn hN lam M u₀ w,
          fun a => u0Test b w (S.levelIn hN lam M u₀ w) (v6 w) (S.levelRecv hN lam M b u₀ w) a))
          (1 + C * logN (n * (n * 21)) ^ c * (12 * D + 16)) (hostOf ((S.levelPad hN).ι (.inl v)))) : ℝ≥0∞) =
        ((R ((S.levelPad hN).ι (.inl v))).1 : ℝ≥0∞) := fun v => by
    rw [hA' N S hN lam M u₀ (S.srcOff hN Q) (fun w a => u0Test b w (S.levelIn hN lam M u₀ w) (v6 w)
      (S.levelRecv hN lam M b u₀ w) a) hP hc hS hcut hD hlam hM hψ hψW hoff v, hr.dist_eq,
      S.dsrcTop_copies hN lam M _ hψ]
  rw [hrun]
  dsimp only
  apply le_antisymm
  · refine le_iInf₂ fun q hq => le_iInf fun hw => ?_
    subst hw
    have hfl := htf ((S.levelPad hN).ι (.inl (S.endV (q.1.2.κ1 q.2))))
    have hfl' : S.tgtFlag hN Q ((S.levelPad hN).ι (.inl (S.endV (q.1.2.κ1 q.2)))) = true := by
      unfold tgtFlag
      exact decide_eq_true ⟨q, hq, rfl⟩
    rw [hfl'] at hfl
    refine (ENat.toENNReal_le.2 (iInf₂_le ((S.levelPad hN).ι (.inl (S.endV (q.1.2.κ1 q.2))))
      ⟨rfl, hfl⟩)).trans (le_of_eq ?_)
    rw [hcopy, hT q hq]
  · rw [ENat.toENNReal_iInf]
    refine le_iInf fun a => ?_
    rw [ENat.toENNReal_iInf]
    refine le_iInf fun ⟨ha, hf⟩ => ?_
    subst ha
    rw [htf] at hf
    unfold tgtFlag at hf
    obtain ⟨q, hq, rfl⟩ := of_decide_eq_true hf
    refine (iInf₂_le q hq).trans ((iInf_le _ rfl).trans (le_of_eq ?_))
    rw [hcopy, hT q hq]

end RData

end RotSystem

end SsspFlow
