import SsspFlow.GHatLevelOff
import SsspFlow.OracleMark

/-!
# Marking shortest walks of a level from local inputs

The nodes of the network run the marking algorithm `markAlg` on the network of a level: shortest
paths from offsets `ψ` at the copies, one round of child messages, and the marking run from the
identifiers whose flag is set. Each node knows the offsets and flags of the identifiers it hosts.

* `RData.levelMark_local`: assuming the Exact SSSP bound, one algorithm of the message model, fixed
  before the network, starts from the local inputs `levelIn`, the offsets and the flags, and after
  `T ≤ 2 C log^c n' · (12 D + 16) + 2` rounds every node holds, at the identifiers it hosts, outputs
  of both runs that meet the specification of the oracle on the network of the level.
-/

set_option autoImplicit false

namespace SsspFlow

open FourColor SsspFlow.Congest
open scoped ENNReal

namespace RotSystem

namespace RData

open Cslib.Congest.Algorithm in
/-- **Marking from local inputs.** Assuming the Exact SSSP bound, one algorithm of the message model on
`N`, fixed before the network, starts from the inputs `levelIn` and, at each node, offsets and flags
that agree with `ψ` and `isT` at the identifiers it hosts. After `T` rounds its outputs at the
identifiers meet the specification of the oracle for the lengths of the level with offsets `ψ`, and
for the marking run of the parents found from the targets `isT`. -/
theorem levelMark_local (hE : ExactSsspBound) (K : ℕ) : ∃ C c : ℕ, ∀ n D : ℕ,
    ∃ (σ : Type) (A : Cslib.Congest.Algorithm (Fin n)
        (LevelIn n × ((Fin (n * (n * 21)) → ℕ∞) × (Fin (n * (n * 21)) → Bool))) σ
        (4 * (C * logN (n * (n * 21)) ^ c + 1) + (3 * (K * logN (n * (n * 21)) + 1) + 5)))
      (T : ℕ) (out₁ out₂ : Fin (n * (n * 21)) → σ → ℕ∞ × Option (Fin (n * (n * 21)))),
    T ≤ 2 + 2 * (C * logN (n * (n * 21)) ^ c * (12 * D + 16)) ∧
    ∀ (N : Net (Fin n)) (S : N.toRot.RData) (hN : ∀ u, ∃ w, N.G.Adj u w) (lam : S.Tok → ℕ) (M : ℕ)
      (u₀ : S.hRot.Vertex) (ψ : Fin (n * (n * 21)) → ℕ∞) (isT : Fin (n * (n * 21)) → Bool)
      (off : Fin n → Fin (n * (n * 21)) → ℕ∞) (flg : Fin n → Fin (n * (n * 21)) → Bool),
      N.toRot.Planar → N.toRot.Connected → S.NoConflict → S.cut.card ≤ 3 → N.DiamLE D →
      (∀ x, lam x ≤ (n * (n * 21) + 2) ^ K) → M ≤ (n * (n * 21) + 2) ^ K →
      (∀ z, ψ z = ⊤ ∨ ψ z ≤ (n * (n * 21) + 2) ^ K) →
      (∀ a, off (hostOf a) a = ψ a) → (∀ a, flg (hostOf a) a = isT a) →
      (S.levelNet hN).ExactSpec (S.levelLen hN lam M) ψ (fun a =>
          out₁ a (A.run N.G (fun w => (S.levelIn hN lam M u₀ w, (off w, flg w))) T (hostOf a))) ∧
        (S.levelNet hN).ExactSpec
          (Net.markLen fun a => out₁ a (A.run N.G (fun w => (S.levelIn hN lam M u₀ w, (off w, flg w))) T (hostOf a)))
          (Net.markOffB isT)
          (fun a => out₂ a (A.run N.G (fun w => (S.levelIn hN lam M u₀ w, (off w, flg w))) T (hostOf a))) := by
  obtain ⟨C, c, hC⟩ := markAlg_spec hE K
  refine ⟨C, c, fun n D => ?_⟩
  obtain ⟨σ, A, out, hA⟩ := hC (n * (n * 21)) (12 * D + 16) (by omega)
  set b := K * logN (n * (n * 21)) + 1
  set Bw := 4 * (C * logN (n * (n * 21)) ^ c + 1) + (3 * b + 5)
  set T' := C * logN (n * (n * 21)) ^ c * (12 * D + 16)
  let Im := LevelIn n × ((Fin (n * (n * 21)) → ℕ∞) × (Fin (n * (n * 21)) → Bool))
  let Aex := (exchTo (Fin n) Bw).keep (fun _ (j : Im) => j.1.msg b)
  let f : Fin n → Im × ((Fin n → ℕ) × (Fin n → Option ℕ)) → Im × (Fin n → Option ℕ) :=
    fun _ s => (s.1, s.2.2)
  let view' : Im × (Fin n → Option ℕ) → Fin (n * (n * 21)) → Fin (n * (n * 21)) → Prop :=
    fun d => LevelIn.view b (d.1.1, d.2)
  let vin' : Fin n → Im × (Fin n → Option ℕ) → Fin (n * (n * 21)) → OracleIn (Fin (n * (n * 21))) × Bool :=
    fun w d a => ({ LevelIn.vin b w (d.1.1, d.2) a with offset := d.1.2.1 a }, d.1.2.2 a)
  let Asim := (simulateView (k := 4) (markAlg A out T') hostOf view' vin').widen
    (show 4 * (C * logN (n * (n * 21)) ^ c + 1) ≤ Bw by omega)
  refine ⟨_, Aex.seq 1 f Asim, 1 + (T' + (1 + T')),
    fun a s => match s with
      | .inr s' => markFirst out a (s'.2 a)
      | .inl _ => (⊤, none),
    fun a s => match s with
      | .inr s' => markSecond out a (s'.2 a)
      | .inl _ => (⊤, none), by omega, ?_⟩
  intro N S hN lam M u₀ ψ isT off flg hP hc hS hcut hD hlam hM hψW hoff hflg
  have hb : ∀ x, lam x < 2 ^ b := fun x => lam_lt_pow (hlam x)
  have hmsg : ∀ u w, (S.levelIn hN lam M u₀ u).msg b w < 2 ^ Bw := fun u w =>
    (DInfo.pack_lt _ (S.lamAt_lt lam hb _ _ _) (S.lamAt_lt lam hb _ _ _) (S.lamAt_lt lam hb _ _ _)).trans_le
      (Nat.pow_le_pow_right (by norm_num) (by omega))
  have hex : (fun w => f w (Aex.run N.G (fun w => (S.levelIn hN lam M u₀ w, (off w, flg w))) 1 w)) =
      fun w => ((S.levelIn hN lam M u₀ w, (off w, flg w)), S.levelRecv hN lam M b u₀ w) := by
    funext w
    show f w ((exchTo (Fin n) Bw).keep (fun _ (j : Im) => j.1.msg b) |>.run N.G _ 1 w) = _
    rw [run_keep]
    show ((S.levelIn hN lam M u₀ w, (off w, flg w)), ((exchTo (Fin n) Bw).run N.G _ 1 w).2) = _
    rw [run_exchTo N.G _ hmsg]
    rfl
  have hin : ∀ a, ((S.levelNet hN).oracleIn (S.levelLen hN lam M) ψ a, isT a) =
      vin' (hostOf a) ((S.levelIn hN lam M u₀ (hostOf a), (off (hostOf a), flg (hostOf a))),
        S.levelRecv hN lam M b u₀ (hostOf a)) a := fun a => by
    have h := S.vin_recv hN lam M hb u₀ a
    show _ = ({ LevelIn.vin b (hostOf a) (S.levelIn hN lam M u₀ (hostOf a), S.levelRecv hN lam M b u₀ (hostOf a)) a
      with offset := off (hostOf a) a }, flg (hostOf a) a)
    rw [← h, hoff a, hflg a]
    rfl
  have hst : ∀ a, (Aex.seq 1 f Asim).run N.G (fun w => (S.levelIn hN lam M u₀ w, (off w, flg w)))
      (1 + (T' + (1 + T'))) (hostOf a) = .inr ((simulateView (k := 4) (markAlg A out T') hostOf view' vin').run
        N.G (fun w => ((S.levelIn hN lam M u₀ w, (off w, flg w)), S.levelRecv hN lam M b u₀ w))
        (T' + (1 + T')) (hostOf a)) := fun a => by
    rw [run_seq, hex, run_widen]
  have hsim : ∀ a, ((simulateView (k := 4) (markAlg A out T') hostOf view' vin').run N.G
      (fun w => ((S.levelIn hN lam M u₀ w, (off w, flg w)), S.levelRecv hN lam M b u₀ w))
      (T' + (1 + T')) (hostOf a)).2 a =
      (markAlg A out T').run (S.levelNet hN).G
        (fun a => ((S.levelNet hN).oracleIn (S.levelLen hN lam M) ψ a, isT a)) (T' + (1 + T')) a :=
    fun a => S.run_levelSim hN (markAlg A out T') view' vin'
      (fun w => ((S.levelIn hN lam M u₀ w, (off w, flg w)), S.levelRecv hN lam M b u₀ w))
      (fun a => ((S.levelNet hN).oracleIn (S.levelLen hN lam M) ψ a, isT a)) hin
      (fun w x y hxy => S.view_recv hN lam M hb u₀ w x y hxy) (T' + (1 + T')) (hostOf a) a rfl
  have hval : OracleValid (S.levelNet hN) 0 ((n * (n * 21) + 2) ^ K) (S.levelLen hN lam M) ψ :=
    ⟨(S.oracleValid_level hN lam M hlam hM u₀).1, hψW⟩
  have key := hA (S.levelNet hN) (S.levelLen hN lam M) ψ isT (S.levelNet_planar hN hP hc hS hcut hD)
    (S.levelNet_diam hN hcut hD) hval
  simp only [hst, hsim]
  exact key

end RData

end RotSystem

end SsspFlow
