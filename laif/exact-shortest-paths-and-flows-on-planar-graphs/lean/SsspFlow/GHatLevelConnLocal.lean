import SsspFlow.GHatLevelSsspLocal
import SsspFlow.GHatLevelConn

/-!
# The components of a level from local inputs

The labels of the components of `Ĝ_ℓ[E_R]` and `Ĝ_ℓ[E_R ∪ E_C]` come from one more shortest-path
computation in which every copy starts at its own offset (`RData.labOff`). The host of a copy computes
that offset from the name of the copy (`rawLabOff`, `RData.labOff_raw`).

* `RData.levelConn_local`: assuming the Exact SSSP bound, one algorithm of the message model, fixed
  before the network, starts from the local inputs `levelIn` and after `C log^c n' · (12 D + 16) + 1`
  rounds holds at every copy a label, and two copies have the same label exactly when they are joined
  by arcs of length `0`. The source field of the inputs is not read.
-/

set_option autoImplicit false

namespace SsspFlow

open FourColor SsspFlow.Congest
open scoped ENNReal

namespace RotSystem

section Raw

variable {n : ℕ}

/-- The offset of the identifier `(w, u, k)` for the labels: `n' - 1 - id` at the name of a copy, and
`∞` otherwise. -/
def rawLabOff (R : List (Fin n)) (f g : Fin n → DInfo) (w : Fin n) (q : Fin n × Fin 21) : ℕ∞ :=
  if rawReal R f g w q = true ∧ q.2 < 5 then
    ((n * (n * 21) - 1 - (RData.idEquiv (w, q.1, q.2)).val : ℕ) : ℕ∞)
  else ⊤

end Raw

namespace LevelIn

variable {n : ℕ}

/-- The input of an identifier hosted at `w` for the labels. -/
def vinC (b : ℕ) (w : Fin n) (d : LevelIn n × (Fin n → Option ℕ)) (a : Fin (n * (n * 21))) :
    OracleIn (Fin (n * (n * 21))) :=
  { vin b w d a with offset := rawLabOff d.1.rot d.1.own (inn b d.2) w (qOf a) }

end LevelIn

namespace RData

variable {n : ℕ} {N : Net (Fin n)} (S : N.toRot.RData) (hN : ∀ u, ∃ w, N.G.Adj u w)
  (lam : S.Tok → ℕ) (M : ℕ)

/-- **The offset of the labels from local data.** -/
theorem labOff_raw (z : Fin (n * (n * 21))) :
    S.labOff hN z = rawLabOff (N.rotList (hostOf z)) (S.dinfoAt (hostOf z))
      (fun u => S.dinfoAt u (hostOf z)) (hostOf z) ((idEquiv.symm z).2.1, (idEquiv.symm z).2.2) := by
  classical
  have hz' : idEquiv (hostOf z, (idEquiv.symm z).2.1, (idEquiv.symm z).2.2) = z :=
    idEquiv.apply_symm_apply z
  unfold labOff rawLabOff
  rw [hz']
  have e : (∃ u, z = (S.levelPad hN).ι (.inl u)) ↔
      (rawReal (N.rotList (hostOf z)) (S.dinfoAt (hostOf z)) (fun u => S.dinfoAt u (hostOf z)) (hostOf z)
        ((idEquiv.symm z).2.1, (idEquiv.symm z).2.2) = true ∧ (idEquiv.symm z).2.2 < 5) := by
    rw [S.rawReal_host hN z]
    constructor
    · rintro ⟨u, rfl⟩
      refine ⟨(S.levelPad hN).isReal_ι _, ?_⟩
      rw [show (S.levelPad hN).ι (.inl u) = idEquiv (N.nameC (S.vcopy u)) from rfl, Equiv.symm_apply_apply]
      exact N.nameC_kind _
    · rintro ⟨hr, hk⟩
      obtain ⟨y, rfl⟩ : ∃ y, z = (S.levelPad hN).ι y := ⟨_, hr⟩
      rcases y with u | x
      · exact ⟨u, rfl⟩
      · rw [show (S.levelPad hN).ι (.inr x) = idEquiv (S.nameD x) from rfl, Equiv.symm_apply_apply] at hk
        have := S.nameD_kind x
        exact absurd hk (by omega)
  by_cases h : ∃ u, z = (S.levelPad hN).ι (.inl u)
  · rw [ite_eq_left_of_eq_true _ _ (eq_true h), ite_eq_left_of_eq_true _ _ (eq_true (e.1 h))]
  · rw [ite_eq_right_of_eq_false _ _ (eq_false h), ite_eq_right_of_eq_false _ _ (eq_false (fun h' => h (e.2 h')))]

theorem vinC_recv {b : ℕ} (hb : ∀ x, lam x < 2 ^ b) (u₀ : S.hRot.Vertex) (a : Fin (n * (n * 21))) :
    (S.levelNet hN).oracleIn (S.levelLen hN lam M) (S.labOff hN) a =
      LevelIn.vinC b (hostOf a) (S.levelIn hN lam M u₀ (hostOf a), S.levelRecv hN lam M b u₀ (hostOf a)) a := by
  have h := S.vin_recv hN lam M hb u₀ a
  unfold LevelIn.vinC
  rw [← h]
  unfold Net.oracleIn
  simp only [OracleIn.mk.injEq, true_and]
  rw [S.labOff_raw hN a, S.inn_recv hN lam M hb]
  rfl

open Cslib.Congest.Algorithm in
/-- **The components of a level from local inputs.** Assuming the Exact SSSP bound, one algorithm of
the message model on `N`, fixed before the network, starts from the inputs `levelIn` and after
`C log^c n' · (12 D + 16) + 1` rounds holds at every copy a label; two copies have the same label
exactly when they are joined by arcs of length `0`. The lengths `λ` are `0` or at least `M`, equal on
the two tokens of a pair, `n' ≤ M`, and `λ`, `M` are at most `(n' + 2)^K`. -/
theorem levelConn_local (hE : ExactSsspBound) (K : ℕ) : ∃ C c : ℕ, ∀ n D : ℕ,
    ∃ (σ : Type) (A : Cslib.Congest.Algorithm (Fin n) (LevelIn n) σ
      (4 * (C * logN (n * (n * 21)) ^ c) + (3 * (K * logN (n * (n * 21)) + 1) + 5)))
      (out : Fin (n * (n * 21)) → σ → ℕ∞),
    ∀ (N : Net (Fin n)) (S : N.toRot.RData) (hN : ∀ u, ∃ w, N.G.Adj u w) (lam : S.Tok → ℕ) (M : ℕ)
      (u₀ : S.hRot.Vertex),
      N.toRot.Planar → N.toRot.Connected → S.NoConflict → S.cut.card ≤ 3 → N.DiamLE D →
      (∀ x, lam x = 0 ∨ M ≤ lam x) → (∀ x, lam (S.partnerTok x) = lam x) → n * (n * 21) ≤ M →
      (∀ x, lam x ≤ (n * (n * 21) + 2) ^ K) → M ≤ (n * (n * 21) + 2) ^ K →
      ∀ u v : S.hRot.Vertex,
        out ((S.levelPad hN).ι (.inl u))
            (A.run N.G (S.levelIn hN lam M u₀) (1 + C * logN (n * (n * 21)) ^ c * (12 * D + 16))
              (hostOf ((S.levelPad hN).ι (.inl u)))) =
          out ((S.levelPad hN).ι (.inl v))
            (A.run N.G (S.levelIn hN lam M u₀) (1 + C * logN (n * (n * 21)) ^ c * (12 * D + 16))
              (hostOf ((S.levelPad hN).ι (.inl v)))) ↔
          Relation.ReflTransGen (S.ZR lam) (S.vcopy u) (S.vcopy v) := by
  obtain ⟨C, c, hC⟩ := levelConn_sim hE K
  refine ⟨C, c, fun n D => ?_⟩
  obtain ⟨σ, A, out, hA⟩ := hC n D
  set b := K * logN (n * (n * 21)) + 1
  set Bw := 4 * (C * logN (n * (n * 21)) ^ c) + (3 * b + 5)
  let Aex := (exchTo (Fin n) Bw).keep (fun _ (j : LevelIn n) => j.msg b)
  let f : Fin n → LevelIn n × ((Fin n → ℕ) × (Fin n → Option ℕ)) → LevelIn n × (Fin n → Option ℕ) :=
    fun _ s => (s.1, s.2.2)
  let Asim := (simulateView (k := 4) A hostOf (LevelIn.view b) (LevelIn.vinC b)).widen
    (show 4 * (C * logN (n * (n * 21)) ^ c) ≤ Bw by omega)
  refine ⟨_, Aex.seq 1 f Asim, fun a s => match s with
    | .inr s' => (out a (s'.2 a)).1
    | .inl _ => ⊤, ?_⟩
  intro N S hN lam M u₀ hP hc hS hcut hD hlam hl hn hlamW hMW u v
  have hb : ∀ x, lam x < 2 ^ b := fun x => lam_lt_pow (hlamW x)
  have hmsg : ∀ u w, (S.levelIn hN lam M u₀ u).msg b w < 2 ^ Bw := fun u w =>
    (DInfo.pack_lt _ (S.lamAt_lt lam hb _ _ _) (S.lamAt_lt lam hb _ _ _) (S.lamAt_lt lam hb _ _ _)).trans_le
      (Nat.pow_le_pow_right (by norm_num) (by omega))
  have hex : (fun w => f w (Aex.run N.G (S.levelIn hN lam M u₀) 1 w)) =
      fun w => (S.levelIn hN lam M u₀ w, S.levelRecv hN lam M b u₀ w) := by
    funext w
    show f w ((exchTo (Fin n) Bw).keep (fun _ (j : LevelIn n) => j.msg b) |>.run N.G _ 1 w) = _
    rw [run_keep]
    show (S.levelIn hN lam M u₀ w, ((exchTo (Fin n) Bw).run N.G _ 1 w).2) = _
    rw [run_exchTo N.G _ hmsg]
    rfl
  rw [run_seq, hex, run_widen]
  dsimp only
  exact hA (LevelIn n × (Fin n → Option ℕ)) (LevelIn.view b) (LevelIn.vinC b) N S hN lam M
    (fun w => (S.levelIn hN lam M u₀ w, S.levelRecv hN lam M b u₀ w)) hP hc hS hcut hD hlam hl hn hlamW hMW
    (S.vinC_recv hN lam M hb u₀) (fun w x y hxy => S.view_recv hN lam M hb u₀ w x y hxy) u v

end RData

end RotSystem

end SsspFlow
