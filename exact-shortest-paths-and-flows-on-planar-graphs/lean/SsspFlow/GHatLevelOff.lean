import SsspFlow.GHatLevelStep

/-!
# Distances of a level from offsets at the copies

A level of the recursion starts shortest paths in every live annulus at once, from a virtual source
joined to the copies by arcs of given offsets. The offsets live only at copies. Each node knows the
offsets of the identifiers it hosts.

* `RData.levelSsspOff_sim`: the nodes compute the distance from the virtual source at every copy,
  the least offset plus distance in `Ĝ_ℓ`, if each node knows the edges and the inputs at its own
  identifiers.
* `RData.levelSsspOff_local`: assuming the Exact SSSP bound, one algorithm of the message model,
  fixed before the network, starts from the local inputs `levelIn` and the offsets at the
  identifiers of each node, and after `C log^c n' · (12 D + 16) + 1` rounds holds this distance at
  every copy.
-/

set_option autoImplicit false

namespace SsspFlow

open FourColor SsspFlow.Congest
open scoped ENNReal

namespace RotSystem

namespace RData

/-- **Distances from offsets at the copies.** The nodes run the algorithm of the Exact SSSP bound on
the network of a level with offsets `ψ` at the copies, round for round, if each node knows the edges
and the inputs at its own identifiers. Every copy then holds the least offset plus distance. -/
theorem levelSsspOff_sim (hE : ExactSsspBound) (K : ℕ) : ∃ C c : ℕ, ∀ n D : ℕ,
    ∃ (σ : Type) (A : Cslib.Congest.Algorithm (Fin (n * (n * 21))) (OracleIn (Fin (n * (n * 21)))) σ
      (C * logN (n * (n * 21)) ^ c)) (out : Fin (n * (n * 21)) → σ → ℕ∞ × Option (Fin (n * (n * 21)))),
    ∀ (I : Type) (view : I → Fin (n * (n * 21)) → Fin (n * (n * 21)) → Prop)
      (vin : Fin n → I → Fin (n * (n * 21)) → OracleIn (Fin (n * (n * 21)))),
    ∀ (N : Net (Fin n)) (S : N.toRot.RData) (hN : ∀ u, ∃ w, N.G.Adj u w) (lam : S.Tok → ℕ) (M : ℕ)
      (ψ : Fin (n * (n * 21)) → ℕ∞) (inp : Fin n → I),
      N.toRot.Planar → N.toRot.Connected → S.NoConflict → S.cut.card ≤ 3 → N.DiamLE D →
      (∀ x, lam x ≤ (n * (n * 21) + 2) ^ K) → M ≤ (n * (n * 21) + 2) ^ K →
      (∀ z, (∀ u, z ≠ (S.levelPad hN).ι (.inl u)) → ψ z = ⊤) →
      (∀ z, ψ z = ⊤ ∨ ψ z ≤ (n * (n * 21) + 2) ^ K) →
      (∀ a, (S.levelNet hN).oracleIn (S.levelLen hN lam M) ψ a = vin (hostOf a) (inp (hostOf a)) a) →
      (∀ w b a, (hostOf b = w ∨ hostOf a = w) → (view (inp w) b a ↔ (S.levelNet hN).G.Adj b a)) →
      ∀ v : S.hRot.Vertex,
        ((out ((S.levelPad hN).ι (.inl v))
          (((Cslib.Congest.Algorithm.simulateView (k := 4) A hostOf view vin).run N.G inp
            (C * logN (n * (n * 21)) ^ c * (12 * D + 16)) (hostOf ((S.levelPad hN).ι (.inl v)))).2
              ((S.levelPad hN).ι (.inl v)))).1 : ℝ≥0∞) =
          ⨅ u, (ψ ((S.levelPad hN).ι (.inl u)) : ℝ≥0∞) + S.arcDist lam M (S.vcopy u) (S.vcopy v) := by
  obtain ⟨C, c, hC⟩ := hE K
  refine ⟨C, c, fun n D => ?_⟩
  obtain ⟨σ, A, out, hA⟩ := hC (n * (n * 21)) (12 * D + 16) (by omega)
  refine ⟨σ, A, out, fun I view vin N S hN lam M ψ inp hP hc hS hcut hD hlam hM hψ hψW hin hview v => ?_⟩
  have hval : OracleValid (S.levelNet hN) 0 ((n * (n * 21) + 2) ^ K) (S.levelLen hN lam M) ψ :=
    ⟨(S.oracleValid_level hN lam M hlam hM v).1, hψW⟩
  rw [S.run_levelSim hN A view vin inp _ hin hview _ _ _ rfl,
    (hA (S.levelNet hN) (S.levelLen hN lam M) ψ (S.levelNet_planar hN hP hc hS hcut hD)
      (S.levelNet_diam hN hcut hD) hval).dist_eq, S.dsrcTop_copies hN lam M ψ hψ v]

open Cslib.Congest.Algorithm in
/-- **Distances from offsets, from local inputs.** Assuming the Exact SSSP bound, one algorithm of the
message model on `N`, fixed before the network, starts from the inputs `levelIn` and, at each node,
offsets that agree with `ψ` at the identifiers it hosts. After `C log^c n' · (12 D + 16) + 1` rounds
it holds at every copy the least offset plus distance in `Ĝ_ℓ`. -/
theorem levelSsspOff_local (hE : ExactSsspBound) (K : ℕ) : ∃ C c : ℕ, ∀ n D : ℕ,
    ∃ (σ : Type) (A : Cslib.Congest.Algorithm (Fin n) (LevelIn n × (Fin (n * (n * 21)) → ℕ∞)) σ
      (4 * (C * logN (n * (n * 21)) ^ c) + (3 * (K * logN (n * (n * 21)) + 1) + 5)))
      (out : Fin (n * (n * 21)) → σ → ℕ∞),
    ∀ (N : Net (Fin n)) (S : N.toRot.RData) (hN : ∀ u, ∃ w, N.G.Adj u w) (lam : S.Tok → ℕ) (M : ℕ)
      (u₀ : S.hRot.Vertex) (ψ : Fin (n * (n * 21)) → ℕ∞) (off : Fin n → Fin (n * (n * 21)) → ℕ∞),
      N.toRot.Planar → N.toRot.Connected → S.NoConflict → S.cut.card ≤ 3 → N.DiamLE D →
      (∀ x, lam x ≤ (n * (n * 21) + 2) ^ K) → M ≤ (n * (n * 21) + 2) ^ K →
      (∀ z, (∀ u, z ≠ (S.levelPad hN).ι (.inl u)) → ψ z = ⊤) →
      (∀ z, ψ z = ⊤ ∨ ψ z ≤ (n * (n * 21) + 2) ^ K) →
      (∀ a, off (hostOf a) a = ψ a) →
      ∀ v : S.hRot.Vertex,
        (out ((S.levelPad hN).ι (.inl v))
          (A.run N.G (fun w => (S.levelIn hN lam M u₀ w, off w)) (1 + C * logN (n * (n * 21)) ^ c * (12 * D + 16))
            (hostOf ((S.levelPad hN).ι (.inl v)))) : ℝ≥0∞) =
          ⨅ u, (ψ ((S.levelPad hN).ι (.inl u)) : ℝ≥0∞) + S.arcDist lam M (S.vcopy u) (S.vcopy v) := by
  obtain ⟨C, c, hC⟩ := levelSsspOff_sim hE K
  refine ⟨C, c, fun n D => ?_⟩
  obtain ⟨σ, A, out, hA⟩ := hC n D
  set b := K * logN (n * (n * 21)) + 1
  set Bw := 4 * (C * logN (n * (n * 21)) ^ c) + (3 * b + 5)
  let Aex := (exchTo (Fin n) Bw).keep (fun _ (j : LevelIn n × (Fin (n * (n * 21)) → ℕ∞)) => j.1.msg b)
  let f : Fin n → (LevelIn n × (Fin (n * (n * 21)) → ℕ∞)) × ((Fin n → ℕ) × (Fin n → Option ℕ)) →
      (LevelIn n × (Fin (n * (n * 21)) → ℕ∞)) × (Fin n → Option ℕ) :=
    fun _ s => (s.1, s.2.2)
  let view' : (LevelIn n × (Fin (n * (n * 21)) → ℕ∞)) × (Fin n → Option ℕ) →
      Fin (n * (n * 21)) → Fin (n * (n * 21)) → Prop :=
    fun d => LevelIn.view b (d.1.1, d.2)
  let vin' : Fin n → (LevelIn n × (Fin (n * (n * 21)) → ℕ∞)) × (Fin n → Option ℕ) →
      Fin (n * (n * 21)) → OracleIn (Fin (n * (n * 21))) :=
    fun w d a => { LevelIn.vin b w (d.1.1, d.2) a with offset := d.1.2 a }
  let Asim := (simulateView (k := 4) A hostOf view' vin').widen
    (show 4 * (C * logN (n * (n * 21)) ^ c) ≤ Bw by omega)
  refine ⟨_, Aex.seq 1 f Asim, fun a s => match s with
    | .inr s' => (out a (s'.2 a)).1
    | .inl _ => ⊤, ?_⟩
  intro N S hN lam M u₀ ψ off hP hc hS hcut hD hlam hM hψ hψW hoff v
  have hb : ∀ x, lam x < 2 ^ b := fun x => lam_lt_pow (hlam x)
  have hmsg : ∀ u w, (S.levelIn hN lam M u₀ u).msg b w < 2 ^ Bw := fun u w =>
    (DInfo.pack_lt _ (S.lamAt_lt lam hb _ _ _) (S.lamAt_lt lam hb _ _ _) (S.lamAt_lt lam hb _ _ _)).trans_le
      (Nat.pow_le_pow_right (by norm_num) (by omega))
  have hex : (fun w => f w (Aex.run N.G (fun w => (S.levelIn hN lam M u₀ w, off w)) 1 w)) =
      fun w => ((S.levelIn hN lam M u₀ w, off w), S.levelRecv hN lam M b u₀ w) := by
    funext w
    show f w ((exchTo (Fin n) Bw).keep (fun _ (j : LevelIn n × (Fin (n * (n * 21)) → ℕ∞)) => j.1.msg b)
      |>.run N.G _ 1 w) = _
    rw [run_keep]
    show ((S.levelIn hN lam M u₀ w, off w), ((exchTo (Fin n) Bw).run N.G _ 1 w).2) = _
    rw [run_exchTo N.G _ hmsg]
    rfl
  rw [run_seq, hex, run_widen]
  dsimp only
  refine hA _ view' vin' N S hN lam M ψ
    (fun w => ((S.levelIn hN lam M u₀ w, off w), S.levelRecv hN lam M b u₀ w)) hP hc hS hcut hD hlam hM hψ hψW
    (fun a => ?_) (fun w x y hxy => S.view_recv hN lam M hb u₀ w x y hxy) v
  have h := S.vin_recv hN lam M hb u₀ a
  show _ = { LevelIn.vin b (hostOf a) (S.levelIn hN lam M u₀ (hostOf a), S.levelRecv hN lam M b u₀ (hostOf a)) a
    with offset := off (hostOf a) a }
  rw [← h, hoff a]
  rfl

end RData

end RotSystem

end SsspFlow
