import SsspFlow.NegCode

/-!
# The program of negative weights

`progN`: the program of a node. Step `s` takes three phases: a decomposition, an oracle call and one
exchange of the value of the step. The steps compute the potentials of the phases of `phiS`, the
indices of the decompositions, the values of Lemma 1 and the potentials of the levels. Two more calls
check the arcs and compute the distances. The steps are named by six digits in the radix `Z`
(`sPhi`, `sIdx`, `sAlt`, `sLev`, `sChk`, `sFin`), with the order of the steps in `sPhi_lt_sIdx` and
the lemmas after it. `compV` is the value of a step from the memory of a node.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped ENNReal
open Cslib.Congest Cslib.Congest.Algorithm

namespace SsspFlow.Congest

/-- The numbers of the program. -/
structure NPar where
  /-- The last level. -/
  L : ℕ
  /-- The last repetition. -/
  R : ℕ
  /-- The steps of Lemma 1. -/
  t : ℕ
  /-- The bound of the first phase. -/
  B₀ : ℕ
  /-- The shift of the offsets. -/
  cs : ℕ

namespace NPar

variable (P : NPar)

/-- The number of phases. -/
def J : ℕ := nPhase P.B₀

/-- The radix of the names of the steps. -/
def Z : ℕ := P.L + P.R + P.t + 5

theorem J_pos : 0 < P.J := by
  unfold J nPhase
  omega

/-- The step of the potential of phase `j`. -/
def sPhi (j : ℕ) : ℕ := addr6 P.Z j 0 0 0 0 0

/-- The step of the decomposition `(ℓ, r)` of phase `j`. -/
def sIdx (j ℓ r : ℕ) : ℕ := addr6 P.Z j 0 1 ℓ r 0

/-- Step `i` of Lemma 1 at level `ℓ`, repetition `r` and start `q` of phase `j`. -/
def sAlt (j ℓ r q i : ℕ) : ℕ := addr6 P.Z j (ℓ + 1) 0 r q i

/-- The step of the potential of level `ℓ` and repetition `r` of phase `j`. -/
def sLev (j ℓ r : ℕ) : ℕ := addr6 P.Z j (ℓ + 1) 1 r 0 0

/-- The step of the check. -/
def sChk : ℕ := addr6 P.Z P.J 0 2 0 0 0

/-- The step of the distances. -/
def sFin : ℕ := addr6 P.Z P.J 0 3 0 0 0

theorem dig_sPhi (j : ℕ) : dig P.Z (P.sPhi j) = (j, 0, 0, 0, 0, 0) :=
  dig_addr6 (by unfold Z; omega) (by unfold Z; omega) (by unfold Z; omega) (by unfold Z; omega)
    (by unfold Z; omega)

theorem dig_sIdx {j ℓ r : ℕ} (hℓ : ℓ ≤ P.L) (hr : r ≤ P.R) : dig P.Z (P.sIdx j ℓ r) = (j, 0, 1, ℓ, r, 0) :=
  dig_addr6 (by unfold Z; omega) (by unfold Z; omega) (by unfold Z; omega) (by unfold Z; omega)
    (by unfold Z; omega)

theorem dig_sAlt {j ℓ r q i : ℕ} (hℓ : ℓ ≤ P.L) (hr : r ≤ P.R) (hq : q ≤ P.R) (hi : i ≤ P.t) :
    dig P.Z (P.sAlt j ℓ r q i) = (j, ℓ + 1, 0, r, q, i) :=
  dig_addr6 (by unfold Z; omega) (by unfold Z; omega) (by unfold Z; omega) (by unfold Z; omega)
    (by unfold Z; omega)

theorem dig_sLev {j ℓ r : ℕ} (hℓ : ℓ ≤ P.L) (hr : r ≤ P.R) :
    dig P.Z (P.sLev j ℓ r) = (j, ℓ + 1, 1, r, 0, 0) :=
  dig_addr6 (by unfold Z; omega) (by unfold Z; omega) (by unfold Z; omega) (by unfold Z; omega)
    (by unfold Z; omega)

theorem dig_sChk : dig P.Z P.sChk = (P.J, 0, 2, 0, 0, 0) :=
  dig_addr6 (by unfold Z; omega) (by unfold Z; omega) (by unfold Z; omega) (by unfold Z; omega)
    (by unfold Z; omega)

theorem dig_sFin : dig P.Z P.sFin = (P.J, 0, 3, 0, 0, 0) :=
  dig_addr6 (by unfold Z; omega) (by unfold Z; omega) (by unfold Z; omega) (by unfold Z; omega)
    (by unfold Z; omega)

end NPar

/-- Compare two names of steps digit by digit. -/
syntax "addr_lt" : tactic

macro_rules
  | `(tactic| addr_lt) => `(tactic| first
    | exact mixZ_lt_right (by first | omega | (unfold NPar.Z; omega))
    | (refine mixZ_lt_left (by first | omega | (unfold NPar.Z; omega)) ?_; addr_lt)
    | omega)

namespace NPar

variable (P : NPar)

theorem sPhi_lt_sIdx (j ℓ r : ℕ) : P.sPhi j < P.sIdx j ℓ r := by
  unfold sPhi sIdx addr6
  addr_lt

theorem sPhi_lt_sAlt (j ℓ r q i : ℕ) : P.sPhi j < P.sAlt j ℓ r q i := by
  unfold sPhi sAlt addr6
  addr_lt

theorem sPhi_lt_sLev (j ℓ r : ℕ) : P.sPhi j < P.sLev j ℓ r := by
  unfold sPhi sLev addr6
  addr_lt

theorem sIdx_lt_sAlt {j ℓ r : ℕ} (hℓ : ℓ ≤ P.L) (hr : r ≤ P.R) (ℓ' r' q i : ℕ) :
    P.sIdx j ℓ r < P.sAlt j ℓ' r' q i := by
  unfold sIdx sAlt addr6
  addr_lt

theorem sIdx_lt_sLev {j ℓ r : ℕ} (hℓ : ℓ ≤ P.L) (hr : r ≤ P.R) (ℓ' r' : ℕ) :
    P.sIdx j ℓ r < P.sLev j ℓ' r' := by
  unfold sIdx sLev addr6
  addr_lt

theorem sLev_lt_sAlt {j ℓ q : ℕ} (hq : q ≤ P.R) (r q' i : ℕ) : P.sLev j ℓ q < P.sAlt j (ℓ + 1) r q' i := by
  unfold sLev sAlt addr6
  addr_lt

theorem sLev_lt_sLev {j ℓ q : ℕ} (hq : q ≤ P.R) (r : ℕ) : P.sLev j ℓ q < P.sLev j (ℓ + 1) r := by
  unfold sLev addr6
  addr_lt

theorem sAlt_lt_sAlt (j ℓ r q i : ℕ) : P.sAlt j ℓ r q i < P.sAlt j ℓ r q (i + 1) := by
  unfold sAlt addr6
  addr_lt

theorem sAlt_lt_sLev {j ℓ r q i : ℕ} (hr : r ≤ P.R) (hq : q ≤ P.R) (hi : i ≤ P.t) :
    P.sAlt j ℓ r q i < P.sLev j ℓ r := by
  unfold sAlt sLev addr6
  addr_lt

theorem sPhi_lt_sPhi (j : ℕ) : P.sPhi j < P.sPhi (j + 1) := by
  unfold sPhi addr6
  addr_lt

theorem sLev_lt_sPhi {j ℓ r : ℕ} (hℓ : ℓ ≤ P.L) (hr : r ≤ P.R) : P.sLev j ℓ r < P.sPhi (j + 1) := by
  unfold sLev sPhi addr6
  addr_lt

theorem sPhi_lt_sChk : P.sPhi P.J < P.sChk := by
  unfold sPhi sChk addr6
  addr_lt

theorem sChk_lt_sFin : P.sChk < P.sFin := by
  unfold sChk sFin addr6
  addr_lt

end NPar

/-! ### The program -/

/-- The offsets of the oracle in step `i` of Lemma 1, shifted by `cs`. -/
noncomputable def altOff {V : Type} [Fintype V] (adj : V → V → Prop) (n L : ℕ) (w : V → V → Option ℤ)
    (φ : V → ℤ) (B : ℕ) (idx : ℕ → ℕ → V → ℕ) (ℓ r : ℕ) (φ' A : V → ℤ) (i cs : ℕ) (a : V) : ℕ∞ :=
  (((if i = 0 then -φ' a else negRelax (clArc L (keptS adj n w φ B) idx ℓ r) (ysc n w φ B) φ' A a) +
    cs).toNat : ℕ∞)

namespace NPar

section Node

variable (P : NPar) {n : ℕ} {ρL : Type}

/-- The private string of the decomposition `(ℓ, r)` of phase `j`. -/
def strAt (y : Fin P.J → Fin (P.L + 1) → Fin (P.R + 1) → ρL) (j ℓ r : ℕ) : ρL :=
  y ⟨j % P.J, Nat.mod_lt _ P.J_pos⟩ ⟨ℓ % (P.L + 1), Nat.mod_lt _ (Nat.succ_pos _)⟩
    ⟨r % (P.R + 1), Nat.mod_lt _ (Nat.succ_pos _)⟩

/-- The potential of phase `j` at a node and its neighbours. -/
def phV (v : Fin n) (m : Mem) (j : ℕ) : Fin n → ℤ := viewV v m (P.sPhi j)

/-- The indices of phase `j` at a node and its neighbours. -/
def idxV (v : Fin n) (m : Mem) (j : ℕ) : ℕ → ℕ → Fin n → ℕ :=
  fun ℓ r u => (viewV v m (P.sIdx j ℓ r) u).toNat

/-- The potential that level `ℓ` starts from, at a node and its neighbours. -/
def prevV (v : Fin n) (m : Mem) (j ℓ q : ℕ) : Fin n → ℤ :=
  if ℓ = 0 then fun _ => 0 else viewV v m (P.sLev j (ℓ - 1) q)

/-- The oracle input of step `i` of Lemma 1. -/
noncomputable def oraAlt (v : Fin n) (x : NegIn (Fin n)) (m : Mem) (j ℓ r q i : ℕ) : OracleIn (Fin n) :=
  mkOra x.nbrs v
    (altLen (adjLoc v x) n P.L (wLoc v x) (P.phV v m j) (Bseq P.B₀ j) (P.idxV v m j) ℓ r (P.prevV v m j ℓ q))
    (altOff (adjLoc v x) n P.L (wLoc v x) (P.phV v m j) (Bseq P.B₀ j) (P.idxV v m j) ℓ r (P.prevV v m j ℓ q)
      (viewV v m (P.sAlt j ℓ r q (i - 1))) i P.cs v)

open Classical in
/-- The oracle input of the check. -/
noncomputable def oraChk (v : Fin n) (x : NegIn (Fin n)) (m : Mem) : OracleIn (Fin n) :=
  mkOra x.nbrs v (fun _ _ => 0) (if badAt (adjLoc v x) n (wLoc v x) (P.phV v m P.J) v then 0 else ⊤)

/-- The oracle input of the distances. -/
noncomputable def oraFin (v : Fin n) (x : NegIn (Fin n)) (m : Mem) : OracleIn (Fin n) :=
  mkOra x.nbrs v (finLen (adjLoc v x) n (wLoc v x) (P.phV v m P.J))
    (if x.isSource then ((-(P.phV v m P.J v)).toNat : ℕ∞) else ⊤)

/-- The oracle input of a step. -/
noncomputable def oraIn (v : Fin n) (x : NegIn (Fin n)) (m : Mem) (s : ℕ) : OracleIn (Fin n) :=
  if (dig P.Z s).2.1 = 0 then (if (dig P.Z s).2.2.1 = 2 then P.oraChk v x m else P.oraFin v x m)
  else P.oraAlt v x m (dig P.Z s).1 ((dig P.Z s).2.1 - 1) (dig P.Z s).2.2.2.1 (dig P.Z s).2.2.2.2.1
    (dig P.Z s).2.2.2.2.2

/-- The input of the decomposition of a step. -/
noncomputable def lddInS (v : Fin n) (y : NegIn (Fin n) × (Fin P.J → Fin (P.L + 1) → Fin (P.R + 1) → ρL))
    (m : Mem) (s : ℕ) : LddIn (Fin n) × ρL :=
  (mkLdd y.1.nbrs v (lamS (keptS (adjLoc v y.1) n (wLoc v y.1) (P.phV v m (dig P.Z s).1) (Bseq P.B₀ (dig P.Z s).1))
      (ysc n (wLoc v y.1) (P.phV v m (dig P.Z s).1) (Bseq P.B₀ (dig P.Z s).1))) (2 ^ ((dig P.Z s).2.2.2.1 + 1)),
    P.strAt y.2 (dig P.Z s).1 (dig P.Z s).2.2.2.1 (dig P.Z s).2.2.2.2.1)

/-- The potential of phase `j` from the memory. -/
def phiVal (m : Mem) (j : ℕ) : ℤ :=
  if j = 0 then 0
  else ownV m (P.sPhi (j - 1)) + (rhoB (Bseq P.B₀ (j - 1)) : ℤ) * ownV m (P.sLev (j - 1) P.L 0)

/-- The potential of level `ℓ` and repetition `r` of phase `j` from the memory. -/
def levVal (n : ℕ) (m : Mem) (j ℓ r : ℕ) : ℤ :=
  minR (fun q => max (-(n : ℤ))
    (ownV m (P.sAlt j ℓ r q P.t) + if ℓ = 0 then 0 else ownV m (P.sLev j (ℓ - 1) q))) P.R -
    if ℓ < P.L then (n : ℤ) * ownV m (P.sIdx j ℓ r) else 0

/-- The value of a step from the memory. -/
noncomputable def compV (n : ℕ) (m : Mem) (s : ℕ) : ℤ :=
  if (dig P.Z s).2.1 = 0 then
    (if (dig P.Z s).2.2.1 = 0 then P.phiVal m (dig P.Z s).1
      else if (dig P.Z s).2.2.1 = 1 then (m (3 * s) 0 : ℤ) else 0)
  else if (dig P.Z s).2.2.1 = 0 then ((decE (m (3 * s + 1) 0)).toNat : ℤ) - P.cs
  else if (dig P.Z s).2.2.1 = 1 then P.levVal n m (dig P.Z s).1 ((dig P.Z s).2.1 - 1) (dig P.Z s).2.2.2.1
  else 0

/-- **The program of a node.** -/
noncomputable def progN (k : ℕ) (v : Fin n)
    (y : NegIn (Fin n) × (Fin P.J → Fin (P.L + 1) → Fin (P.R + 1) → ρL)) (m : Mem) :
    OracleIn (Fin n) ⊕ RelaxIn (Fin n) ⊕ (LddIn (Fin n) × ρL) :=
  if k % 3 = 0 then .inr (.inr (P.lddInS v y m (k / 3)))
  else if k % 3 = 1 then .inl (P.oraIn v y.1 m (k / 3))
  else .inr (.inl (passIn (encZ (P.compV n m (k / 3))) (fun z _ => z) (fun _ => encZ (P.compV n m (k / 3)))))

variable (v : Fin n) (y : NegIn (Fin n) × (Fin P.J → Fin (P.L + 1) → Fin (P.R + 1) → ρL)) (m : Mem)

theorem progN_ldd (s : ℕ) : P.progN (3 * s) v y m = .inr (.inr (P.lddInS v y m s)) := by
  unfold progN
  rw [ite_eq_left (by omega), show 3 * s / 3 = s by omega]

theorem progN_ora (s : ℕ) : P.progN (3 * s + 1) v y m = .inl (P.oraIn v y.1 m s) := by
  unfold progN
  rw [ite_eq_right (by omega), ite_eq_left (by omega), show (3 * s + 1) / 3 = s by omega]

theorem progN_ex (s : ℕ) : P.progN (3 * s + 2) v y m =
    .inr (.inl (passIn (encZ (P.compV n m s)) (fun z _ => z) (fun _ => encZ (P.compV n m s)))) := by
  unfold progN
  rw [ite_eq_right (by omega), ite_eq_right (by omega), show (3 * s + 2) / 3 = s by omega]

theorem compV_phi (j : ℕ) : P.compV n m (P.sPhi j) = P.phiVal m j := by
  unfold compV
  rw [P.dig_sPhi]
  simp

theorem compV_idx {j ℓ r : ℕ} (hℓ : ℓ ≤ P.L) (hr : r ≤ P.R) :
    P.compV n m (P.sIdx j ℓ r) = (m (3 * P.sIdx j ℓ r) 0 : ℤ) := by
  unfold compV
  rw [P.dig_sIdx hℓ hr]
  simp

theorem compV_alt {j ℓ r q i : ℕ} (hℓ : ℓ ≤ P.L) (hr : r ≤ P.R) (hq : q ≤ P.R) (hi : i ≤ P.t) :
    P.compV n m (P.sAlt j ℓ r q i) = ((decE (m (3 * P.sAlt j ℓ r q i + 1) 0)).toNat : ℤ) - P.cs := by
  unfold compV
  rw [P.dig_sAlt hℓ hr hq hi]
  simp

theorem compV_lev {j ℓ r : ℕ} (hℓ : ℓ ≤ P.L) (hr : r ≤ P.R) :
    P.compV n m (P.sLev j ℓ r) = P.levVal n m j ℓ r := by
  unfold compV
  rw [P.dig_sLev hℓ hr]
  simp

theorem compV_chk : P.compV n m P.sChk = 0 := by
  unfold compV
  rw [P.dig_sChk]
  simp

theorem compV_fin : P.compV n m P.sFin = 0 := by
  unfold compV
  rw [P.dig_sFin]
  simp

theorem oraIn_alt (x : NegIn (Fin n)) {j ℓ r q i : ℕ} (hℓ : ℓ ≤ P.L) (hr : r ≤ P.R) (hq : q ≤ P.R)
    (hi : i ≤ P.t) : P.oraIn v x m (P.sAlt j ℓ r q i) = P.oraAlt v x m j ℓ r q i := by
  unfold oraIn
  rw [P.dig_sAlt hℓ hr hq hi]
  simp

theorem oraIn_chk (x : NegIn (Fin n)) : P.oraIn v x m P.sChk = P.oraChk v x m := by
  unfold oraIn
  rw [P.dig_sChk]
  simp

theorem oraIn_fin (x : NegIn (Fin n)) : P.oraIn v x m P.sFin = P.oraFin v x m := by
  unfold oraIn
  rw [P.dig_sFin]
  simp

theorem lddInS_idx {j ℓ r : ℕ} (hℓ : ℓ ≤ P.L) (hr : r ≤ P.R) : P.lddInS v y m (P.sIdx j ℓ r) =
    (mkLdd y.1.nbrs v (lamS (keptS (adjLoc v y.1) n (wLoc v y.1) (P.phV v m j) (Bseq P.B₀ j))
      (ysc n (wLoc v y.1) (P.phV v m j) (Bseq P.B₀ j))) (2 ^ (ℓ + 1)), P.strAt y.2 j ℓ r) := by
  unfold lddInS
  rw [P.dig_sIdx hℓ hr]

end Node

end NPar

end SsspFlow.Congest
