import SsspFlow.GHatLevelU0
import SsspFlow.GHatPieceRun

/-!
# The common copy of a level, as one algorithm

One round of exchange gives every node the records of the darts into it. Then each node tests the
identifiers it hosts for the copy of a fixed corner `z₀`, and the flood of the least number gives every
node the identifier of that copy. The records do not depend on the copy named in the inputs, so this
runs before that copy is known.

* `RData.u0Test`: the test of an identifier at its host, from the inputs of a level, the values of
  `flag0 z₀` at the corners of the darts into the node and the received records.
* `RData.u0Test_eq`: the test is the least value of `flag0 z₀` at the first ends of the tokens at the
  identifier.
* `RData.levelU0_local`: one algorithm of the message model, fixed before the network, gives every node
  the identifier of the copy `endV z₀` after `1 + D` rounds.
-/

set_option autoImplicit false

namespace SsspFlow

open FourColor SsspFlow.Congest Cslib.Congest.Algorithm
open scoped ENNReal

namespace RotSystem

namespace RData

/-- The test of an identifier `a` at the node `w`, from its inputs `j` of a level, the values `vi0` at
the corners of the darts into it and the received records `r`. -/
noncomputable def u0Test {n : ℕ} (b : ℕ) (w : Fin n) (j : LevelIn n) (vi0 : Fin n → Bool → ℕ∞)
    (r : Fin n → Option ℕ) (a : Fin (n * (n * 21))) : ℕ∞ :=
  locCopy j.own (LevelIn.inn b r) (fun _ _ => ⊤) vi0 (idEquiv.symm a).2.2
    (rawAt j.rot j.own (LevelIn.inn b r) w ((idEquiv.symm a).2.1, (idEquiv.symm a).2.2))

variable {n : ℕ} {N : Net (Fin n)} (S : N.toRot.RData) (hN : ∀ u, ∃ w, N.G.Adj u w)
  (lam : S.Tok → ℕ) (M : ℕ)

/-- **The test of the host is the value at the first ends.** -/
theorem u0Test_eq {b : ℕ} (hb : ∀ x, lam x < 2 ^ b) (u₀ : S.hRot.Vertex) (z₀ : N.G.Dart × Bool)
    (vi0 : Fin n → Fin n → Bool → ℕ∞) (hvi0 : ∀ (d : N.G.Dart) c, vi0 d.snd d.fst c = flag0 z₀ (d, c))
    (a : Fin (n * (n * 21))) :
    u0Test b (hostOf a) (S.levelIn hN lam M u₀ (hostOf a)) (vi0 (hostOf a))
        (S.levelRecv hN lam M b u₀ (hostOf a)) a =
      S.onCopies hN (fun u => S.copyVal0 (flag0 z₀) (S.vcopy u)) a := by
  unfold u0Test
  rw [S.inn_recv hN lam M hb u₀ (hostOf a)]
  show locCopy (S.dinfoAt (hostOf a)) (fun u => S.dinfoAt u (hostOf a)) (fun _ _ => ⊤) (vi0 (hostOf a))
    (idEquiv.symm a).2.2 (rawAt (N.rotList (hostOf a)) (S.dinfoAt (hostOf a))
      (fun u => S.dinfoAt u (hostOf a)) (hostOf a) ((idEquiv.symm a).2.1, (idEquiv.symm a).2.2)) = _
  rw [← S.levelNet_rotList_raw hN a]
  exact S.locCopy_eq0 hN (flag0 z₀) vi0 hvi0 a

/-- The identifier read from a number, with a fallback. -/
def toId {n : ℕ} (w : Fin n) (c : ℕ) : Fin (n * (n * 21)) :=
  if h : c < n * (n * 21) then ⟨c, h⟩ else idEquiv (w, w, 0)

/-- **The common copy of a level, as one algorithm.** For every `K`, `n` and `D`, one algorithm of the
message model on `N`, with `3 (K log n' + 1) + 5 + log n'` bits per message, starts from the inputs of a
level, which may name any copy, and the values of `flag0 z₀` at the corners of the darts into each node.
After `1 + D` rounds on a network of diameter at most `D`, every node holds the identifier of the copy
`endV z₀`. -/
theorem levelU0_local (K : ℕ) : ∀ n D : ℕ,
    ∃ (σ : Type) (A : Cslib.Congest.Algorithm (Fin n) (LevelIn n × (Fin n → Bool → ℕ∞)) σ
      (3 * (K * logN (n * (n * 21)) + 1) + 5 + logN (n * (n * 21))))
      (out : Fin n → σ → Fin (n * (n * 21))),
    ∀ (N : Net (Fin n)) (S : N.toRot.RData) (hN : ∀ u, ∃ w, N.G.Adj u w) (lam : S.Tok → ℕ) (M : ℕ)
      (u₀ : S.hRot.Vertex) (z₀ : N.G.Dart × Bool) (vi0 : Fin n → Fin n → Bool → ℕ∞),
      (∀ x, lam x ≤ (n * (n * 21) + 2) ^ K) →
      (∀ (d : N.G.Dart) c, vi0 d.snd d.fst c = flag0 z₀ (d, c)) → N.DiamLE D →
      ∀ w, out w (A.run N.G (fun w => (S.levelIn hN lam M u₀ w, vi0 w)) (1 + D) w) =
        (S.levelPad hN).ι (.inl (S.endV z₀)) := by
  intro n D
  set b := K * logN (n * (n * 21)) + 1
  set B := 3 * b + 5 + logN (n * (n * 21))
  let Aex := (exchTo (Fin n) B).keep
    (fun _ (j : LevelIn n × (Fin n → Bool → ℕ∞)) => j.1.msg b)
  let f : Fin n → (LevelIn n × (Fin n → Bool → ℕ∞)) × ((Fin n → ℕ) × (Fin n → Option ℕ)) → ℕ :=
    fun w s => seedOf (fun _ a => u0Test b w s.1.1 s.1.2 s.2.2 a) w
  refine ⟨_, Aex.seq 1 f (minFlood B), fun w s => match s with
    | .inr s' => toId w s'.1
    | .inl _ => idEquiv (w, w, 0), ?_⟩
  intro N S hN lam M u₀ z₀ vi0 hlam hvi0 hD w
  have hb : ∀ x, lam x < 2 ^ b := fun x => lam_lt_pow (hlam x)
  have hmsg : ∀ u w, (S.levelIn hN lam M u₀ u).msg b w < 2 ^ B := fun u w =>
    (DInfo.pack_lt _ (S.lamAt_lt lam hb _ _ _) (S.lamAt_lt lam hb _ _ _) (S.lamAt_lt lam hb _ _ _)).trans_le
      (Nat.pow_le_pow_right (by norm_num) (by omega))
  have hex : (fun w => f w (Aex.run N.G (fun w => (S.levelIn hN lam M u₀ w, vi0 w)) 1 w)) =
      seedOf fun w a => u0Test b w (S.levelIn hN lam M u₀ w) (vi0 w) (S.levelRecv hN lam M b u₀ w) a := by
    funext w
    show f w ((exchTo (Fin n) B).keep
      (fun _ (j : LevelIn n × (Fin n → Bool → ℕ∞)) => j.1.msg b) |>.run N.G _ 1 w) = _
    rw [run_keep]
    show seedOf (fun _ a => u0Test b w (S.levelIn hN lam M u₀ w) (vi0 w)
      ((exchTo (Fin n) B).run N.G _ 1 w).2 a) w = _
    rw [run_exchTo N.G _ hmsg]
    rfl
  have hB : n * (n * 21) < 2 ^ B := by
    have h1 : n * (n * 21) < 2 ^ logN (n * (n * 21)) := by
      have := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) (n * (n * 21) + 2)
      unfold logN; omega
    exact h1.trans_le (Nat.pow_le_pow_right (by norm_num) (by omega))
  have e := S.run_u0 hN z₀
    (fun w a => u0Test b w (S.levelIn hN lam M u₀ w) (vi0 w) (S.levelRecv hN lam M b u₀ w) a)
    (fun a => S.u0Test_eq hN lam M hb u₀ z₀ vi0 hvi0 a) hB hD w
  rw [run_seq, hex]
  dsimp only
  rw [e]
  unfold toId
  rw [dite_eq_left ((S.levelPad hN).ι (.inl (S.endV z₀))).isLt]

end RData

end RotSystem

end SsspFlow
