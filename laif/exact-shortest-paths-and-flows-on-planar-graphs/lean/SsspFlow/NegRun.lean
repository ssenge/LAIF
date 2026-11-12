import SsspFlow.NegNet

/-!
# The run of the program of negative weights

The values of the steps of `progN` (`phiG`, `idxG`, `altG`, `levG`) and their bounds. `NRun` is what
a run of the machine gives: older entries stay, oracle calls answer `dsrcTop`, decompositions answer
their indices and exchanges pass values to the neighbours. From it, after the step of a value,
every node holds its value and those of its neighbours (`Holds`). If no phase is bad, the outputs
of the nodes are correct (`negSpec_run`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped ENNReal
open Cslib.Congest Cslib.Congest.Algorithm

namespace SsspFlow.Congest

theorem negRelax_ge {V : Type} [Fintype V] {E : V → V → Prop} {y : V → V → ℤ} {φ : V → ℤ} {M : ℤ}
    (hM : ∀ a, -M ≤ φ a ∧ φ a ≤ 0) (hy : ∀ a b, E a b → -1 ≤ y a b) (i : ℕ) (a : V) :
    -(((i + 1 : ℕ) : ℤ) * (M + 1)) ≤ negRelax E y φ (altSeq E y φ i) a := by
  rcases negRelax_cases (E := E) (y := y) (φ := φ) (altSeq E y φ i) a with h | ⟨u, hu, h⟩
  · rw [h]
    have := altSeq_ge hM hy i a
    have hM0 : 0 ≤ M + 1 := by have := hM a; linarith
    push_cast
    nlinarith
  · rw [h, yr]
    have := altSeq_ge hM hy i u
    have := hy u a hu.1
    have := hM u
    have := hM a
    push_cast
    linarith

theorem encZ_lt {z : ℤ} {Vm Bm : ℕ} (hz : -(Vm : ℤ) ≤ z ∧ z ≤ Vm) (hB : 2 * Vm < 2 ^ Bm) :
    encZ z < 2 ^ Bm := by
  have h1 := encZ_le z
  have h2 : z.natAbs ≤ Vm := by omega
  omega

namespace NPar

theorem strAt_eq (P : NPar) {ρL : Type} (y : Fin P.J → Fin (P.L + 1) → Fin (P.R + 1) → ρL) {j ℓ r : ℕ}
    (hj : j < P.J) (hℓ : ℓ ≤ P.L) (hr : r ≤ P.R) :
    P.strAt y j ℓ r = y ⟨j, hj⟩ ⟨ℓ, Nat.lt_succ_of_le hℓ⟩ ⟨r, Nat.lt_succ_of_le hr⟩ := by
  unfold strAt
  have e1 : (⟨j % P.J, Nat.mod_lt _ P.J_pos⟩ : Fin P.J) = ⟨j, hj⟩ := Fin.ext (Nat.mod_eq_of_lt hj)
  have e2 : (⟨ℓ % (P.L + 1), Nat.mod_lt _ (Nat.succ_pos _)⟩ : Fin (P.L + 1)) =
      ⟨ℓ, Nat.lt_succ_of_le hℓ⟩ := Fin.ext (Nat.mod_eq_of_lt (Nat.lt_succ_of_le hℓ))
  have e3 : (⟨r % (P.R + 1), Nat.mod_lt _ (Nat.succ_pos _)⟩ : Fin (P.R + 1)) =
      ⟨r, Nat.lt_succ_of_le hr⟩ := Fin.ext (Nat.mod_eq_of_lt (Nat.lt_succ_of_le hr))
  rw [e1, e2, e3]

/-! ### The values -/

section Values

variable (P : NPar) {n : ℕ} {X : Type} [Fintype X] (adj : Fin n → Fin n → Prop)
  (w : Fin n → Fin n → Option ℤ) (ixF : (Fin n → ℤ) → ℕ → ℕ → X → Fin n → ℕ)
  (ω : Fin P.J → Fin (P.L + 1) → Fin (P.R + 1) → X)

/-- The potential of phase `j`. -/
noncomputable def phiG (j : ℕ) : Fin n → ℤ := phiS adj n P.L P.R P.t w P.B₀ (decOf P.B₀ ixF ω) j

/-- The indices of the decompositions of phase `j`. -/
noncomputable def idxG (j : ℕ) : ℕ → ℕ → Fin n → ℕ := decOf P.B₀ ixF ω j (P.phiG adj w ixF ω j)

/-- The potentials that level `ℓ` of phase `j` starts from. -/
noncomputable def prevG (j ℓ q : ℕ) : Fin n → ℤ :=
  prevPhi n P.L P.R P.t (keptS adj n w (P.phiG adj w ixF ω j) (Bseq P.B₀ j))
    (ysc n w (P.phiG adj w ixF ω j) (Bseq P.B₀ j)) (P.idxG adj w ixF ω j) ℓ q

/-- Step `i` of Lemma 1 at level `ℓ`, repetition `r` and start `q` of phase `j`. -/
noncomputable def altG (j ℓ r q i : ℕ) : Fin n → ℤ :=
  altSeq (clArc P.L (keptS adj n w (P.phiG adj w ixF ω j) (Bseq P.B₀ j)) (P.idxG adj w ixF ω j) ℓ r)
    (ysc n w (P.phiG adj w ixF ω j) (Bseq P.B₀ j)) (P.prevG adj w ixF ω j ℓ q) i

/-- The potential of level `ℓ` and repetition `r` of phase `j`. -/
noncomputable def levG (j ℓ r : ℕ) : Fin n → ℤ :=
  levPhi n P.L P.R P.t (keptS adj n w (P.phiG adj w ixF ω j) (Bseq P.B₀ j))
    (ysc n w (P.phiG adj w ixF ω j) (Bseq P.B₀ j)) (P.idxG adj w ixF ω j) ℓ r

/-- The offsets of step `i` of Lemma 1, before the shift by `cs`. -/
noncomputable def offG (j ℓ r q i : ℕ) (a : Fin n) : ℤ :=
  if i = 0 then -P.prevG adj w ixF ω j ℓ q a
  else negRelax (clArc P.L (keptS adj n w (P.phiG adj w ixF ω j) (Bseq P.B₀ j)) (P.idxG adj w ixF ω j) ℓ r)
    (ysc n w (P.phiG adj w ixF ω j) (Bseq P.B₀ j)) (P.prevG adj w ixF ω j ℓ q)
    (P.altG adj w ixF ω j ℓ r q (i - 1)) a

/-- The lengths of the oracle in Lemma 1. -/
noncomputable def lenG (j ℓ r q : ℕ) : Fin n → Fin n → ℕ∞ :=
  altLen adj n P.L w (P.phiG adj w ixF ω j) (Bseq P.B₀ j) (P.idxG adj w ixF ω j) ℓ r
    (P.prevG adj w ixF ω j ℓ q)

/-- The offsets of the oracle in step `i` of Lemma 1. -/
noncomputable def offN (j ℓ r q i : ℕ) : Fin n → ℕ∞ :=
  altOff adj n P.L w (P.phiG adj w ixF ω j) (Bseq P.B₀ j) (P.idxG adj w ixF ω j) ℓ r
    (P.prevG adj w ixF ω j ℓ q) (P.altG adj w ixF ω j ℓ r q (i - 1)) i P.cs

theorem levG_eq (j ℓ r : ℕ) (v : Fin n) : P.levG adj w ixF ω j ℓ r v =
    minR (fun q => max (-(n : ℤ)) (P.altG adj w ixF ω j ℓ r q P.t v + P.prevG adj w ixF ω j ℓ q v)) P.R -
      if ℓ < P.L then (n : ℤ) * P.idxG adj w ixF ω j ℓ r v else 0 := by
  unfold levG
  rw [levPhi_eq]
  rfl

theorem altG_eq (j ℓ r q i : ℕ) : P.altG adj w ixF ω j ℓ r q i =
    zdist (posArc (clArc P.L (keptS adj n w (P.phiG adj w ixF ω j) (Bseq P.B₀ j)) (P.idxG adj w ixF ω j) ℓ r)
        (ysc n w (P.phiG adj w ixF ω j) (Bseq P.B₀ j)) (P.prevG adj w ixF ω j ℓ q))
      (posLen (ysc n w (P.phiG adj w ixF ω j) (Bseq P.B₀ j)) (P.prevG adj w ixF ω j ℓ q))
      (P.offG adj w ixF ω j ℓ r q i) := by
  cases i <;> (show zdist _ _ _ = zdist _ _ _; congr 1)

variable {P adj w ixF ω}

theorem phiG_bounds (j : ℕ) (v : Fin n) :
    -((j * (P.B₀ + 1) * n : ℕ) : ℤ) ≤ P.phiG adj w ixF ω j v ∧ P.phiG adj w ixF ω j v ≤ 0 :=
  phiS_bounds P.B₀ _ j v

theorem idxG_lt {IDX : ℕ} (h0 : 0 < IDX) (hix : ∀ φ B ℓ x v, ℓ ≤ P.L → ixF φ B ℓ x v < IDX)
    (j ℓ r : ℕ) (v : Fin n) : P.idxG adj w ixF ω j ℓ r v < IDX := by
  unfold idxG decOf
  split_ifs with h
  · unfold idxOf
    split_ifs with h'
    · exact hix _ _ _ _ _ h'.1
    · exact h0
  · exact h0

variable {IDX : ℕ} {j : ℕ} (hidx : ∀ ℓ r v, P.idxG adj w ixF ω j ℓ r v < IDX)
include hidx

theorem levG_bounds (ℓ r : ℕ) (v : Fin n) :
    -((n + n * IDX : ℕ) : ℤ) ≤ P.levG adj w ixF ω j ℓ r v ∧ P.levG adj w ixF ω j ℓ r v ≤ 0 := by
  have hb := levPhi_bounds (n := n) (L := P.L) (R := P.R) (t := P.t)
    (kept := keptS adj n w (P.phiG adj w ixF ω j) (Bseq P.B₀ j))
    (ys := ysc n w (P.phiG adj w ixF ω j) (Bseq P.B₀ j)) (idx := P.idxG adj w ixF ω j) ℓ r v
  have hs : (0 : ℤ) ≤ shiftI n P.L (P.idxG adj w ixF ω j) ℓ r v ∧
      shiftI n P.L (P.idxG adj w ixF ω j) ℓ r v ≤ (n : ℤ) * IDX := by
    unfold shiftI
    split_ifs
    · have h1 : (P.idxG adj w ixF ω j ℓ r v : ℤ) ≤ IDX := by exact_mod_cast (hidx ℓ r v).le
      exact ⟨by positivity, mul_le_mul_of_nonneg_left h1 (by positivity)⟩
    · exact ⟨le_rfl, by positivity⟩
  unfold levG
  push_cast
  constructor <;> linarith [hb.1, hb.2, hs.1, hs.2]

theorem prevG_bounds (ℓ q : ℕ) (v : Fin n) :
    -((n + n * IDX : ℕ) : ℤ) ≤ P.prevG adj w ixF ω j ℓ q v ∧ P.prevG adj w ixF ω j ℓ q v ≤ 0 := by
  cases ℓ with
  | zero =>
    show _ ≤ (0 : ℤ) ∧ (0 : ℤ) ≤ 0
    exact ⟨by have : (0 : ℤ) ≤ ((n + n * IDX : ℕ) : ℤ) := Int.natCast_nonneg _; linarith, le_rfl⟩
  | succ ℓ => exact levG_bounds hidx ℓ q v

theorem altG_bounds (ℓ r q i : ℕ) (v : Fin n) :
    -((i : ℤ) * (((n + n * IDX : ℕ) : ℤ) + 1)) ≤ P.altG adj w ixF ω j ℓ r q i v ∧
      P.altG adj w ixF ω j ℓ r q i v ≤ ((n + n * IDX : ℕ) : ℤ) := by
  have hM := prevG_bounds hidx ℓ q
  have h0 := altSeq_ge (E := clArc P.L (keptS adj n w (P.phiG adj w ixF ω j) (Bseq P.B₀ j))
    (P.idxG adj w ixF ω j) ℓ r) (y := ysc n w (P.phiG adj w ixF ω j) (Bseq P.B₀ j)) hM
    (fun _ _ _ => le_max_left _ _) i v
  have h1 := altSeq_le_off (E := clArc P.L (keptS adj n w (P.phiG adj w ixF ω j) (Bseq P.B₀ j))
    (P.idxG adj w ixF ω j) ℓ r) (y := ysc n w (P.phiG adj w ixF ω j) (Bseq P.B₀ j))
    (φ := P.prevG adj w ixF ω j ℓ q) i v
  have := hM v
  unfold altG
  constructor <;> linarith

theorem offG_bounds (ℓ r q i : ℕ) (a : Fin n) :
    -((i : ℤ) * (((n + n * IDX : ℕ) : ℤ) + 1)) ≤ P.offG adj w ixF ω j ℓ r q i a ∧
      P.offG adj w ixF ω j ℓ r q i a ≤ ((n + n * IDX : ℕ) : ℤ) := by
  have hM := prevG_bounds hidx ℓ q
  cases i with
  | zero =>
    have := hM a
    unfold offG
    rw [ite_eq_left rfl]
    push_cast at this ⊢
    constructor <;> linarith
  | succ i =>
    have hlo := negRelax_ge (E := clArc P.L (keptS adj n w (P.phiG adj w ixF ω j) (Bseq P.B₀ j))
      (P.idxG adj w ixF ω j) ℓ r) (y := ysc n w (P.phiG adj w ixF ω j) (Bseq P.B₀ j)) hM
      (fun _ _ _ => le_max_left _ _) i a
    have hle := negRelax_le_self (E := clArc P.L (keptS adj n w (P.phiG adj w ixF ω j) (Bseq P.B₀ j))
      (P.idxG adj w ixF ω j) ℓ r) (y := ysc n w (P.phiG adj w ixF ω j) (Bseq P.B₀ j))
      (φ := P.prevG adj w ixF ω j ℓ q) (P.altG adj w ixF ω j ℓ r q i) a
    have hup := (altG_bounds hidx ℓ r q i a).2
    unfold offG
    rw [ite_eq_right (Nat.succ_ne_zero i), Nat.add_sub_cancel]
    exact ⟨hlo, by linarith⟩

/-- The finite lengths of the oracle in Lemma 1 are at most `W`. -/
theorem lenG_le {W : ℕ} (hW : n + (n + n * IDX) ≤ W) (ℓ r q : ℕ) (a b : Fin n) :
    P.lenG adj w ixF ω j ℓ r q a b = ⊤ ∨ P.lenG adj w ixF ω j ℓ r q a b ≤ W := by
  unfold lenG altLen restrictLen
  split_ifs with hp
  · right
    have hk : ysc n w (P.phiG adj w ixF ω j) (Bseq P.B₀ j) a b ≤ n := hp.1.1.2
    have h1 := (prevG_bounds hidx ℓ q a).2
    have h2 := (prevG_bounds hidx ℓ q b).1
    have h3 : posLen (ysc n w (P.phiG adj w ixF ω j) (Bseq P.B₀ j)) (P.prevG adj w ixF ω j ℓ q) a b ≤ W := by
      unfold posLen yr
      rw [Int.toNat_le]
      push_cast at h2 ⊢
      have : ((n : ℤ) + ((n : ℤ) + (n : ℤ) * (IDX : ℤ))) ≤ (W : ℤ) := by exact_mod_cast hW
      linarith
    exact_mod_cast h3
  · left
    rfl

end Values

/-! ### The run -/

section Run

variable (P : NPar) {n : ℕ} {ρL X : Type} [Fintype X]

/-- What a run of the machine gives. Older entries of the memory stay. An oracle call with valid
lengths and offsets answers `dsrcTop`. A decomposition with the lengths of a phase answers `ixF` on
the string of its phase, level and repetition. An exchange passes the value of its step. -/
structure NRun (Bm W : ℕ) (N : Net (Fin n)) (w : Fin n → Fin n → Option ℤ) (src : Fin n)
    (str : Fin n → Fin P.J → Fin (P.L + 1) → Fin (P.R + 1) → ρL)
    (ixF : (Fin n → ℤ) → ℕ → ℕ → X → Fin n → ℕ) (ω : Fin P.J → Fin (P.L + 1) → Fin (P.R + 1) → X)
    (mem : ℕ → Fin n → Mem) : Prop where
  stable : ∀ {j k : ℕ}, j < k → ∀ v, mem k v j = mem (j + 1) v j
  ora : ∀ (s : ℕ) (ℓ : Fin n → Fin n → ℕ∞) (φ : Fin n → ℕ∞), OracleValid N 0 W ℓ φ →
    (∀ u, P.oraIn u (N.negIn w src u) (mem (3 * s + 1) u) s = N.oracleIn ℓ φ u) →
    ∀ v, (decE (mem (3 * s + 2) v (3 * s + 1) 0) : ℝ≥0∞) = N.dsrcTop ℓ φ v
  ldd : ∀ (s : ℕ) (φ : Fin n → ℤ) (B : ℕ) (j : Fin P.J) (ℓ : Fin (P.L + 1)) (r : Fin (P.R + 1)),
    (∀ u, P.lddInS u (N.negIn w src u, str u) (mem (3 * s) u) s =
      (N.lddIn (lamS (keptS N.G.Adj n w φ B) (ysc n w φ B)) (2 ^ ((ℓ : ℕ) + 1)) u, str u j ℓ r)) →
    ∀ v, mem (3 * s + 1) v (3 * s) 0 = ixF φ B ℓ (ω j ℓ r) v
  exch : ∀ (s : ℕ) (v : Fin n), mem (3 * s + 2 + 1) v (3 * s + 2) = relaxSt Bm N.G
    (fun u => passIn (encZ (P.compV n (mem (3 * s + 2) u) s)) (fun z _ => z)
      (fun _ => encZ (P.compV n (mem (3 * s + 2) u) s))) 1 v

/-- The numbers of a run: indices below `IDX`, values of absolute value at most `Vm`, which fit into
`Bm` bits, and lengths and offsets of the oracle calls in Lemma 1 at most `W`. -/
structure NNum (n IDX Vm Bm W : ℕ) : Prop where
  idx0 : 0 < IDX
  t1 : 1 ≤ P.t
  cs : P.t * (n + n * IDX + 1) ≤ P.cs
  vm : P.J * (P.B₀ + 1) * n + IDX + P.cs ≤ Vm
  bm : 2 * Vm < 2 ^ Bm
  w : n + (n + n * IDX) + P.cs ≤ W

/-- The output of a node from its memory: the bit of the check, the value of the last call and the
last potential. -/
noncomputable def outN (n : ℕ) (m : Mem) : Option (Option ℤ) :=
  outS n (decide (decE (m (3 * P.sChk + 1) 0) ≠ ⊤)) (decE (m (3 * P.sFin + 1) 0)) (ownV m (P.sPhi P.J))

variable {P} {Bm W : ℕ} {N : Net (Fin n)} {w : Fin n → Fin n → Option ℤ} {src : Fin n}
  {str : Fin n → Fin P.J → Fin (P.L + 1) → Fin (P.R + 1) → ρL}
  {ixF : (Fin n → ℤ) → ℕ → ℕ → X → Fin n → ℕ} {ω : Fin P.J → Fin (P.L + 1) → Fin (P.R + 1) → X}
  {mem : ℕ → Fin n → Mem}

/-- **A value from the memory.** If the value of step `s` from the memory is `f`, then from
phase `3 s + 3` on every node holds `f` at itself and its neighbours. -/
theorem holds_of_comp (h : P.NRun Bm W N w src str ixF ω mem) {s : ℕ} {f : Fin n → ℤ}
    (hf : ∀ v, P.compV n (mem (3 * s + 2) v) s = f v) (hB : ∀ v, encZ (f v) < 2 ^ Bm) :
    Holds N.G mem s f := by
  intro k hk v
  have e : ∀ u, mem k u (3 * s + 2) =
      relaxSt Bm N.G (fun u => passIn (encZ (f u)) (fun z _ => z) (fun _ => encZ (f u))) 1 u := by
    intro u
    rw [h.stable (j := 3 * s + 2) (k := k) (by omega) u, h.exch s u]
    simp only [hf]
  rw [e v]
  exact exch_one N.G (fun u => encZ (f u)) hB v

theorem holds_phi (h : P.NRun Bm W N w src str ixF ω mem) {j : ℕ}
    (hB : ∀ v, encZ (P.phiG N.G.Adj w ixF ω j v) < 2 ^ Bm)
    (hprev : ∀ j', j = j' + 1 → Holds N.G mem (P.sPhi j') (P.phiG N.G.Adj w ixF ω j') ∧
      Holds N.G mem (P.sLev j' P.L 0) (P.levG N.G.Adj w ixF ω j' P.L 0)) :
    Holds N.G mem (P.sPhi j) (P.phiG N.G.Adj w ixF ω j) := by
  refine holds_of_comp h (fun v => ?_) hB
  rw [P.compV_phi]
  unfold phiVal
  cases j with
  | zero =>
    rw [ite_eq_left rfl]
    rfl
  | succ j' =>
    obtain ⟨h1, h2⟩ := hprev j' rfl
    rw [ite_eq_right (Nat.succ_ne_zero j'), Nat.add_sub_cancel,
      h1.own (k := 3 * P.sPhi (j' + 1) + 2) (by have := P.sPhi_lt_sPhi j'; omega) v,
      h2.own (k := 3 * P.sPhi (j' + 1) + 2)
        (by have := P.sLev_lt_sPhi (j := j') (le_refl P.L) (Nat.zero_le P.R); omega) v]
    rfl

theorem holds_idx (h : P.NRun Bm W N w src str ixF ω mem) {j ℓ r : ℕ} (hj : j < P.J) (hℓ : ℓ ≤ P.L)
    (hr : r ≤ P.R) (hB : ∀ v, encZ (P.idxG N.G.Adj w ixF ω j ℓ r v : ℤ) < 2 ^ Bm)
    (hφ : Holds N.G mem (P.sPhi j) (P.phiG N.G.Adj w ixF ω j)) :
    Holds N.G mem (P.sIdx j ℓ r) (fun v => (P.idxG N.G.Adj w ixF ω j ℓ r v : ℤ)) := by
  have hk : 3 * P.sPhi j + 3 ≤ 3 * P.sIdx j ℓ r := by have := P.sPhi_lt_sIdx j ℓ r; omega
  have hin : ∀ u, P.lddInS u (N.negIn w src u, str u) (mem (3 * P.sIdx j ℓ r) u) (P.sIdx j ℓ r) =
      (N.lddIn (lamS (keptS N.G.Adj n w (P.phiG N.G.Adj w ixF ω j) (Bseq P.B₀ j))
        (ysc n w (P.phiG N.G.Adj w ixF ω j) (Bseq P.B₀ j))) (2 ^ (ℓ + 1)) u,
        str u ⟨j, hj⟩ ⟨ℓ, Nat.lt_succ_of_le hℓ⟩ ⟨r, Nat.lt_succ_of_le hr⟩) := by
    intro u
    rw [P.lddInS_idx u _ _ hℓ hr, P.strAt_eq _ hj hℓ hr]
    refine Prod.ext (mkLdd_eq N fun u' hu' => ⟨?_, ?_⟩) rfl
    · exact lamS_congr (adjLoc_out N w src u u') (wLoc_out N w src hu')
        (hφ.view hk u u (Or.inl rfl)) (hφ.view hk u u' (Or.inr hu'))
    · exact lamS_congr (adjLoc_in N w src u u') (wLoc_in N w src hu')
        (hφ.view hk u u' (Or.inr hu')) (hφ.view hk u u (Or.inl rfl))
  refine holds_of_comp h (fun v => ?_) hB
  rw [P.compV_idx _ hℓ hr, h.stable (j := 3 * P.sIdx j ℓ r) (k := 3 * P.sIdx j ℓ r + 2) (by omega) v,
    h.ldd _ _ _ ⟨j, hj⟩ ⟨ℓ, Nat.lt_succ_of_le hℓ⟩ ⟨r, Nat.lt_succ_of_le hr⟩ hin v]
  unfold idxG decOf
  rw [dite_eq_left hj, idxOf, dite_eq_left ⟨hℓ, hr⟩]

omit [Fintype X] in
/-- The arcs into `u` of the clusters, as `u` computes them, are the global ones. -/
theorem clArc_in {u : Fin n} {φL φG : Fin n → ℤ} {iL iG : ℕ → ℕ → Fin n → ℕ} {L B ℓ r : ℕ}
    (hφ : ∀ u', u' = u ∨ N.G.Adj u u' → φL u' = φG u')
    (hi : ∀ u', u' = u ∨ N.G.Adj u u' → iL ℓ r u' = iG ℓ r u') (u' : Fin n) :
    clArc L (keptS (adjLoc u (N.negIn w src u)) n (wLoc u (N.negIn w src u)) φL B) iL ℓ r u' u ↔
      clArc L (keptS N.G.Adj n w φG B) iG ℓ r u' u := by
  by_cases ha : N.G.Adj u' u
  · exact clArc_congr (keptS_congr (adjLoc_in N w src u u') (wLoc_in N w src ha.symm)
      (hφ u' (Or.inr ha.symm)) (hφ u (Or.inl rfl))) (hi u' (Or.inr ha.symm)) (hi u (Or.inl rfl))
  · constructor
    · rintro ⟨⟨⟨h1, -⟩, -⟩, -⟩
      exact absurd ((adjLoc_in N w src u u').1 h1) ha
    · rintro ⟨⟨⟨h1, -⟩, -⟩, -⟩
      exact absurd h1 ha

omit [Fintype X] in
/-- The relaxation at `u`, as `u` computes it, is the global one. -/
theorem negRelax_loc {u : Fin n} {φL φG pL pG AL AG : Fin n → ℤ} {iL iG : ℕ → ℕ → Fin n → ℕ}
    {L B ℓ r : ℕ} (hφ : ∀ u', u' = u ∨ N.G.Adj u u' → φL u' = φG u')
    (hi : ∀ u', u' = u ∨ N.G.Adj u u' → iL ℓ r u' = iG ℓ r u')
    (hp : ∀ u', u' = u ∨ N.G.Adj u u' → pL u' = pG u')
    (hA : ∀ u', u' = u ∨ N.G.Adj u u' → AL u' = AG u') :
    negRelax (clArc L (keptS (adjLoc u (N.negIn w src u)) n (wLoc u (N.negIn w src u)) φL B) iL ℓ r)
        (ysc n (wLoc u (N.negIn w src u)) φL B) pL AL u =
      negRelax (clArc L (keptS N.G.Adj n w φG B) iG ℓ r) (ysc n w φG B) pG AG u := by
  have hadj : ∀ u', clArc L (keptS (adjLoc u (N.negIn w src u)) n (wLoc u (N.negIn w src u)) φL B)
      iL ℓ r u' u → N.G.Adj u u' := fun u' h => ((adjLoc_in N w src u u').1 h.1.1.1).symm
  exact negRelax_congr (clArc_in hφ hi)
    (fun u' h => ysc_congr (wLoc_in N w src (hadj u' h)) (hφ u' (Or.inr (hadj u' h))) (hφ u (Or.inl rfl)))
    (fun u' h => hp u' (Or.inr (hadj u' h))) (hp u (Or.inl rfl)) (fun u' h => hA u' (Or.inr (hadj u' h)))
    (hA u (Or.inl rfl))

/-- The oracle input of step `i` of Lemma 1 at `u` is the global one, if `u` knows the potential,
the indices, the potentials of the level before and the values of the step before. -/
theorem oraAlt_eq {u : Fin n} {m : Mem} {j ℓ r q i : ℕ}
    (hφ : ∀ u', u' = u ∨ N.G.Adj u u' → P.phV u m j u' = P.phiG N.G.Adj w ixF ω j u')
    (hi : ∀ u', u' = u ∨ N.G.Adj u u' → P.idxV u m j ℓ r u' = P.idxG N.G.Adj w ixF ω j ℓ r u')
    (hp : ∀ u', u' = u ∨ N.G.Adj u u' → P.prevV u m j ℓ q u' = P.prevG N.G.Adj w ixF ω j ℓ q u')
    (ha : ∀ i', i = i' + 1 → ∀ u', u' = u ∨ N.G.Adj u u' →
      viewV u m (P.sAlt j ℓ r q i') u' = P.altG N.G.Adj w ixF ω j ℓ r q i' u') :
    P.oraAlt u (N.negIn w src u) m j ℓ r q i =
      N.oracleIn (P.lenG N.G.Adj w ixF ω j ℓ r q) (P.offN N.G.Adj w ixF ω j ℓ r q i) u := by
  unfold oraAlt
  refine mkOra_eq N (fun u' hu' => ⟨?_, ?_⟩) ?_
  · exact altLen_congr (adjLoc_out N w src u u') (wLoc_out N w src hu') (hφ u (Or.inl rfl))
      (hφ u' (Or.inr hu')) (hi u (Or.inl rfl)) (hi u' (Or.inr hu')) (hp u (Or.inl rfl))
      (hp u' (Or.inr hu'))
  · exact altLen_congr (adjLoc_in N w src u u') (wLoc_in N w src hu') (hφ u' (Or.inr hu'))
      (hφ u (Or.inl rfl)) (hi u' (Or.inr hu')) (hi u (Or.inl rfl)) (hp u' (Or.inr hu'))
      (hp u (Or.inl rfl))
  · unfold offN altOff
    cases i with
    | zero => rw [ite_eq_left rfl, ite_eq_left rfl, hp u (Or.inl rfl)]
    | succ i =>
      rw [ite_eq_right (Nat.succ_ne_zero i), ite_eq_right (Nat.succ_ne_zero i), Nat.add_sub_cancel,
        negRelax_loc hφ hi hp (ha i rfl)]

/-- The answer of the oracle in step `i` of Lemma 1. -/
theorem alt_dsrc {j ℓ r q i : ℕ} (hcs : ∀ a, 0 ≤ P.offG N.G.Adj w ixF ω j ℓ r q i a + P.cs)
    (v : Fin n) : N.dsrcTop (P.lenG N.G.Adj w ixF ω j ℓ r q) (P.offN N.G.Adj w ixF ω j ℓ r q i) v =
      ((((P.altG N.G.Adj w ixF ω j ℓ r q i v + P.cs).toNat : ℕ) : ℕ∞) : ℝ≥0∞) := by
  have hE : ∀ a b, posArc (clArc P.L (keptS N.G.Adj n w (P.phiG N.G.Adj w ixF ω j) (Bseq P.B₀ j))
      (P.idxG N.G.Adj w ixF ω j) ℓ r) (ysc n w (P.phiG N.G.Adj w ixF ω j) (Bseq P.B₀ j))
      (P.prevG N.G.Adj w ixF ω j ℓ q) a b → N.G.Adj a b := fun a b h => h.1.1.1.1
  have h1 := dsrc_restrict hE (posLen (ysc n w (P.phiG N.G.Adj w ixF ω j) (Bseq P.B₀ j))
    (P.prevG N.G.Adj w ixF ω j ℓ q)) (fun a => (P.offG N.G.Adj w ixF ω j ℓ r q i a + P.cs).toNat) v
  have h2 := ndsrc_shift (adj := posArc (clArc P.L (keptS N.G.Adj n w (P.phiG N.G.Adj w ixF ω j)
      (Bseq P.B₀ j)) (P.idxG N.G.Adj w ixF ω j) ℓ r) (ysc n w (P.phiG N.G.Adj w ixF ω j) (Bseq P.B₀ j))
      (P.prevG N.G.Adj w ixF ω j ℓ q))
    (len := posLen (ysc n w (P.phiG N.G.Adj w ixF ω j) (Bseq P.B₀ j)) (P.prevG N.G.Adj w ixF ω j ℓ q))
    (o := P.offG N.G.Adj w ixF ω j ℓ r q i) P.cs hcs v
  rw [← P.altG_eq] at h2
  rw [ENat.toENNReal_coe, ← h2, Int.toNat_natCast]
  exact h1

omit [Fintype X] in
theorem prevV_eq {k j ℓ q : ℕ}
    (hprev : ∀ ℓ', ℓ = ℓ' + 1 → Holds N.G mem (P.sLev j ℓ' q) (P.levG N.G.Adj w ixF ω j ℓ' q))
    (hk : ∀ ℓ', ℓ = ℓ' + 1 → 3 * P.sLev j ℓ' q + 3 ≤ k) (u u' : Fin n) (hu : u' = u ∨ N.G.Adj u u') :
    P.prevV u (mem k u) j ℓ q u' = P.prevG N.G.Adj w ixF ω j ℓ q u' := by
  cases ℓ with
  | zero =>
    unfold prevV
    rw [ite_eq_left rfl]
    rfl
  | succ ℓ' =>
    unfold prevV
    rw [ite_eq_right (Nat.succ_ne_zero ℓ'), Nat.add_sub_cancel]
    exact (hprev ℓ' rfl).view (hk ℓ' rfl) u u' hu

theorem holds_alt (h : P.NRun Bm W N w src str ixF ω mem) {j ℓ r q i : ℕ} (hℓ : ℓ ≤ P.L)
    (hr : r ≤ P.R) (hq : q ≤ P.R) (hi : i ≤ P.t)
    (hval : OracleValid N 0 W (P.lenG N.G.Adj w ixF ω j ℓ r q) (P.offN N.G.Adj w ixF ω j ℓ r q i))
    (hcs : ∀ a, 0 ≤ P.offG N.G.Adj w ixF ω j ℓ r q i a + P.cs)
    (hpos : ∀ v, 0 ≤ P.altG N.G.Adj w ixF ω j ℓ r q i v + P.cs)
    (hB : ∀ v, encZ (P.altG N.G.Adj w ixF ω j ℓ r q i v) < 2 ^ Bm)
    (hφ : Holds N.G mem (P.sPhi j) (P.phiG N.G.Adj w ixF ω j))
    (hI : Holds N.G mem (P.sIdx j ℓ r) (fun v => (P.idxG N.G.Adj w ixF ω j ℓ r v : ℤ)))
    (hprev : ∀ ℓ', ℓ = ℓ' + 1 → Holds N.G mem (P.sLev j ℓ' q) (P.levG N.G.Adj w ixF ω j ℓ' q))
    (hA : ∀ i', i = i' + 1 → Holds N.G mem (P.sAlt j ℓ r q i') (P.altG N.G.Adj w ixF ω j ℓ r q i')) :
    Holds N.G mem (P.sAlt j ℓ r q i) (P.altG N.G.Adj w ixF ω j ℓ r q i) := by
  have hk1 : 3 * P.sPhi j + 3 ≤ 3 * P.sAlt j ℓ r q i + 1 := by
    have := P.sPhi_lt_sAlt j ℓ r q i; omega
  have hk2 : 3 * P.sIdx j ℓ r + 3 ≤ 3 * P.sAlt j ℓ r q i + 1 := by
    have := P.sIdx_lt_sAlt (j := j) hℓ hr ℓ r q i; omega
  have hin : ∀ u, P.oraIn u (N.negIn w src u) (mem (3 * P.sAlt j ℓ r q i + 1) u) (P.sAlt j ℓ r q i) =
      N.oracleIn (P.lenG N.G.Adj w ixF ω j ℓ r q) (P.offN N.G.Adj w ixF ω j ℓ r q i) u := by
    intro u
    rw [P.oraIn_alt u _ _ hℓ hr hq hi]
    refine oraAlt_eq (fun u' hu' => hφ.view hk1 u u' hu') (fun u' hu' => ?_) (fun u' hu' => ?_)
      (fun i' e u' hu' => ?_)
    · show (viewV u _ (P.sIdx j ℓ r) u').toNat = _
      rw [hI.view hk2 u u' hu']
      exact Int.toNat_natCast _
    · exact prevV_eq hprev (fun ℓ' e => by
        subst e
        have := P.sLev_lt_sAlt (j := j) (ℓ := ℓ') hq r q i
        omega) u u' hu'
    · subst e
      exact (hA i' rfl).view (by have := P.sAlt_lt_sAlt j ℓ r q i'; omega) u u' hu'
  refine holds_of_comp h (fun v => ?_) hB
  rw [P.compV_alt _ hℓ hr hq hi]
  have e1 := h.ora (P.sAlt j ℓ r q i) _ _ hval hin v
  rw [alt_dsrc hcs v, ENat.toENNReal_inj] at e1
  rw [e1, ENat.toNat_natCast]
  have := hpos v
  omega

theorem holds_lev (h : P.NRun Bm W N w src str ixF ω mem) {j ℓ r : ℕ} (hℓ : ℓ ≤ P.L) (hr : r ≤ P.R)
    (hB : ∀ v, encZ (P.levG N.G.Adj w ixF ω j ℓ r v) < 2 ^ Bm)
    (hI : ℓ < P.L → Holds N.G mem (P.sIdx j ℓ r) (fun v => (P.idxG N.G.Adj w ixF ω j ℓ r v : ℤ)))
    (hprev : ∀ ℓ', ℓ = ℓ' + 1 → ∀ q ≤ P.R,
      Holds N.G mem (P.sLev j ℓ' q) (P.levG N.G.Adj w ixF ω j ℓ' q))
    (hA : ∀ q ≤ P.R, Holds N.G mem (P.sAlt j ℓ r q P.t) (P.altG N.G.Adj w ixF ω j ℓ r q P.t)) :
    Holds N.G mem (P.sLev j ℓ r) (P.levG N.G.Adj w ixF ω j ℓ r) := by
  refine holds_of_comp h (fun v => ?_) hB
  rw [P.compV_lev _ hℓ hr, P.levG_eq]
  unfold levVal
  congr 1
  · refine minR_congr fun q hq => ?_
    rw [(hA q hq).own (k := 3 * P.sLev j ℓ r + 2)
      (by have := P.sAlt_lt_sLev (j := j) (ℓ := ℓ) hr hq (le_refl P.t); omega) v]
    congr 2
    cases ℓ with
    | zero =>
      rw [ite_eq_left rfl]
      rfl
    | succ ℓ' =>
      rw [ite_eq_right (Nat.succ_ne_zero ℓ'), Nat.add_sub_cancel]
      exact (hprev ℓ' rfl q hq).own (by have := P.sLev_lt_sLev (j := j) (ℓ := ℓ') hq r; omega) v
  · split_ifs with hl
    · rw [(hI hl).own (k := 3 * P.sLev j ℓ r + 2) (by have := P.sIdx_lt_sLev (j := j) hℓ hr ℓ r; omega) v]
    · rfl

/-! ### The numbers -/

variable {IDX Vm : ℕ}

omit [Fintype X] in
theorem NNum.mp_le (hN : P.NNum n IDX Vm Bm W) : n + n * IDX ≤ P.cs :=
  calc n + n * IDX ≤ 1 * (n + n * IDX + 1) := by omega
    _ ≤ P.t * (n + n * IDX + 1) := Nat.mul_le_mul_right _ hN.t1
    _ ≤ P.cs := hN.cs

theorem NNum.phi_fit (hN : P.NNum n IDX Vm Bm W) {j : ℕ} (hj : j ≤ P.J) (v : Fin n) :
    encZ (P.phiG N.G.Adj w ixF ω j v) < 2 ^ Bm := by
  obtain ⟨h1, h2⟩ := phiG_bounds (P := P) (adj := N.G.Adj) (w := w) (ixF := ixF) (ω := ω) j v
  have h3 : j * (P.B₀ + 1) * n ≤ Vm :=
    (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hj)).trans (by have := hN.vm; omega)
  have h4 : ((j * (P.B₀ + 1) * n : ℕ) : ℤ) ≤ Vm := by exact_mod_cast h3
  exact encZ_lt ⟨by linarith, by linarith [Int.natCast_nonneg Vm]⟩ hN.bm

theorem NNum.idx_fit (hN : P.NNum n IDX Vm Bm W) {j : ℕ}
    (hidx : ∀ ℓ r v, P.idxG N.G.Adj w ixF ω j ℓ r v < IDX) (ℓ r : ℕ) (v : Fin n) :
    encZ (P.idxG N.G.Adj w ixF ω j ℓ r v : ℤ) < 2 ^ Bm := by
  have h1 : P.idxG N.G.Adj w ixF ω j ℓ r v ≤ Vm := (hidx ℓ r v).le.trans (by have := hN.vm; omega)
  have h2 : ((P.idxG N.G.Adj w ixF ω j ℓ r v : ℕ) : ℤ) ≤ Vm := by exact_mod_cast h1
  exact encZ_lt ⟨by linarith [Int.natCast_nonneg (P.idxG N.G.Adj w ixF ω j ℓ r v),
    Int.natCast_nonneg Vm], h2⟩ hN.bm

theorem NNum.alt_fit (hN : P.NNum n IDX Vm Bm W) {j : ℕ}
    (hidx : ∀ ℓ r v, P.idxG N.G.Adj w ixF ω j ℓ r v < IDX) {ℓ r q i : ℕ} (hi : i ≤ P.t) :
    (∀ v, encZ (P.altG N.G.Adj w ixF ω j ℓ r q i v) < 2 ^ Bm) ∧
      (∀ v, 0 ≤ P.altG N.G.Adj w ixF ω j ℓ r q i v + P.cs) ∧
      (∀ a, 0 ≤ P.offG N.G.Adj w ixF ω j ℓ r q i a + P.cs) := by
  have hic : (i : ℤ) * (((n + n * IDX : ℕ) : ℤ) + 1) ≤ P.cs := by
    have : i * (n + n * IDX + 1) ≤ P.cs := (Nat.mul_le_mul_right _ hi).trans hN.cs
    exact_mod_cast this
  have hmp : ((n + n * IDX : ℕ) : ℤ) ≤ P.cs := by exact_mod_cast hN.mp_le
  have hcv : (P.cs : ℤ) ≤ Vm := by exact_mod_cast (show P.cs ≤ Vm by have := hN.vm; omega)
  refine ⟨fun v => ?_, fun v => ?_, fun a => ?_⟩
  · obtain ⟨h1, h2⟩ := altG_bounds hidx ℓ r q i v
    exact encZ_lt ⟨by linarith, by linarith⟩ hN.bm
  · linarith [(altG_bounds hidx ℓ r q i v).1]
  · linarith [(offG_bounds hidx ℓ r q i a).1]

theorem NNum.lev_fit (hN : P.NNum n IDX Vm Bm W) {j : ℕ}
    (hidx : ∀ ℓ r v, P.idxG N.G.Adj w ixF ω j ℓ r v < IDX) (ℓ r : ℕ) (v : Fin n) :
    encZ (P.levG N.G.Adj w ixF ω j ℓ r v) < 2 ^ Bm := by
  obtain ⟨h1, h2⟩ := levG_bounds hidx ℓ r v
  have hmp : ((n + n * IDX : ℕ) : ℤ) ≤ Vm := by
    exact_mod_cast (show n + n * IDX ≤ Vm by have := hN.mp_le; have := hN.vm; omega)
  exact encZ_lt ⟨by linarith, by linarith [Int.natCast_nonneg Vm]⟩ hN.bm

theorem NNum.alt_valid (hN : P.NNum n IDX Vm Bm W) {j : ℕ}
    (hidx : ∀ ℓ r v, P.idxG N.G.Adj w ixF ω j ℓ r v < IDX) (ℓ r q i : ℕ) :
    OracleValid N 0 W (P.lenG N.G.Adj w ixF ω j ℓ r q) (P.offN N.G.Adj w ixF ω j ℓ r q i) := by
  refine ⟨fun a b _ => ?_, fun a => Or.inr ?_⟩
  · rcases lenG_le hidx (by have := hN.w; omega : n + (n + n * IDX) ≤ W) ℓ r q a b with h | h
    · exact Or.inl h
    · exact Or.inr ⟨zero_le, h⟩
  · show (((P.offG N.G.Adj w ixF ω j ℓ r q i a + P.cs).toNat : ℕ) : ℕ∞) ≤ W
    have h1 := (offG_bounds hidx ℓ r q i a).2
    have h2 : ((n + (n + n * IDX) + P.cs : ℕ) : ℤ) ≤ W := by exact_mod_cast hN.w
    have h3 : (P.offG N.G.Adj w ixF ω j ℓ r q i a + P.cs).toNat ≤ W := by
      rw [Int.toNat_le]
      push_cast at h1 h2 ⊢
      linarith [Int.natCast_nonneg n]
    exact_mod_cast h3

/-! ### All steps -/

theorem holds_alts (h : P.NRun Bm W N w src str ixF ω mem) (hN : P.NNum n IDX Vm Bm W) {j : ℕ}
    (hidx : ∀ ℓ r v, P.idxG N.G.Adj w ixF ω j ℓ r v < IDX) {ℓ r q : ℕ} (hℓ : ℓ ≤ P.L) (hr : r ≤ P.R)
    (hq : q ≤ P.R) (hφ : Holds N.G mem (P.sPhi j) (P.phiG N.G.Adj w ixF ω j))
    (hI : Holds N.G mem (P.sIdx j ℓ r) (fun v => (P.idxG N.G.Adj w ixF ω j ℓ r v : ℤ)))
    (hprev : ∀ ℓ', ℓ = ℓ' + 1 → Holds N.G mem (P.sLev j ℓ' q) (P.levG N.G.Adj w ixF ω j ℓ' q)) :
    ∀ i ≤ P.t, Holds N.G mem (P.sAlt j ℓ r q i) (P.altG N.G.Adj w ixF ω j ℓ r q i) := by
  intro i
  induction i with
  | zero =>
    intro hi
    obtain ⟨hB, hpos, hcs⟩ := hN.alt_fit hidx (ℓ := ℓ) (r := r) (q := q) hi
    exact holds_alt h hℓ hr hq hi (hN.alt_valid hidx ℓ r q 0) hcs hpos hB hφ hI hprev
      (fun i' e => absurd e (by omega))
  | succ i ih =>
    intro hi
    obtain ⟨hB, hpos, hcs⟩ := hN.alt_fit hidx (ℓ := ℓ) (r := r) (q := q) hi
    exact holds_alt h hℓ hr hq hi (hN.alt_valid hidx ℓ r q _) hcs hpos hB hφ hI hprev
      (fun i' e => by
        obtain rfl : i = i' := by omega
        exact ih (by omega))

theorem holds_levs (h : P.NRun Bm W N w src str ixF ω mem) (hN : P.NNum n IDX Vm Bm W) {j : ℕ}
    (hidx : ∀ ℓ r v, P.idxG N.G.Adj w ixF ω j ℓ r v < IDX) (hj : j < P.J)
    (hφ : Holds N.G mem (P.sPhi j) (P.phiG N.G.Adj w ixF ω j)) :
    ∀ ℓ ≤ P.L, ∀ r ≤ P.R, Holds N.G mem (P.sLev j ℓ r) (P.levG N.G.Adj w ixF ω j ℓ r) := by
  have hI : ∀ ℓ ≤ P.L, ∀ r ≤ P.R,
      Holds N.G mem (P.sIdx j ℓ r) (fun v => (P.idxG N.G.Adj w ixF ω j ℓ r v : ℤ)) :=
    fun ℓ hℓ r hr => holds_idx h hj hℓ hr (hN.idx_fit hidx ℓ r) hφ
  intro ℓ
  induction ℓ with
  | zero =>
    intro hℓ r hr
    have hpv : ∀ ℓ', 0 = ℓ' + 1 → ∀ q ≤ P.R,
        Holds N.G mem (P.sLev j ℓ' q) (P.levG N.G.Adj w ixF ω j ℓ' q) :=
      fun ℓ' e => absurd e (by omega)
    exact holds_lev h hℓ hr (hN.lev_fit hidx 0 r) (fun _ => hI 0 hℓ r hr) hpv fun q hq =>
      holds_alts h hN hidx hℓ hr hq hφ (hI 0 hℓ r hr) (fun ℓ' e => hpv ℓ' e q hq) P.t le_rfl
  | succ ℓ ih =>
    intro hℓ r hr
    have hpv : ∀ ℓ', ℓ + 1 = ℓ' + 1 → ∀ q ≤ P.R,
        Holds N.G mem (P.sLev j ℓ' q) (P.levG N.G.Adj w ixF ω j ℓ' q) := fun ℓ' e => by
      obtain rfl : ℓ = ℓ' := by omega
      exact ih (by omega)
    exact holds_lev h hℓ hr (hN.lev_fit hidx _ r) (fun _ => hI _ hℓ r hr) hpv fun q hq =>
      holds_alts h hN hidx hℓ hr hq hφ (hI _ hℓ r hr) (fun ℓ' e => hpv ℓ' e q hq) P.t le_rfl

/-- **All phases.** Every node holds the potentials of all phases. -/
theorem holds_phis (h : P.NRun Bm W N w src str ixF ω mem) (hN : P.NNum n IDX Vm Bm W)
    (hix : ∀ φ B ℓ x v, ℓ ≤ P.L → ixF φ B ℓ x v < IDX) :
    ∀ j ≤ P.J, Holds N.G mem (P.sPhi j) (P.phiG N.G.Adj w ixF ω j) := by
  intro j
  induction j with
  | zero =>
    intro hj
    exact holds_phi h (hN.phi_fit hj) (fun j' e => absurd e (by omega))
  | succ j ih =>
    intro hj
    refine holds_phi h (hN.phi_fit hj) fun j' e => ?_
    obtain rfl : j = j' := by omega
    have hφ := ih (by omega)
    exact ⟨hφ, holds_levs h hN (idxG_lt hN.idx0 hix j) (by omega) hφ P.L le_rfl 0 (Nat.zero_le _)⟩

/-! ### The check and the last call -/

omit [Fintype X] in
/-- **The check.** The entry of the check is finite at a node exactly if some arc of finite weight
has a negative reduced weight after the last phase. -/
theorem chk_iff (h : P.NRun Bm W N w src str ixF ω mem)
    (hφ : Holds N.G mem (P.sPhi P.J) (P.phiG N.G.Adj w ixF ω P.J))
    (conn : ∀ u v, Nonempty (Walk N.G.Adj u v)) (v : Fin n) :
    decE (mem (3 * P.sChk + 2) v (3 * P.sChk + 1) 0) ≠ ⊤ ↔
      ∃ a b, zArc N.G.Adj w a b ∧ yr (xw n w) (P.phiG N.G.Adj w ixF ω P.J) a b < 0 := by
  classical
  have hk : 3 * P.sPhi P.J + 3 ≤ 3 * P.sChk + 1 := by have := P.sPhi_lt_sChk; omega
  have hin : ∀ u, P.oraIn u (N.negIn w src u) (mem (3 * P.sChk + 1) u) P.sChk =
      N.oracleIn (fun _ _ => 0)
        (fun a => if badAt N.G.Adj n w (P.phiG N.G.Adj w ixF ω P.J) a then 0 else ⊤) u := by
    intro u
    rw [P.oraIn_chk u _ _]
    unfold oraChk
    refine mkOra_eq N (fun _ _ => ⟨rfl, rfl⟩) ?_
    have hb : badAt (adjLoc u (N.negIn w src u)) n (wLoc u (N.negIn w src u))
        (P.phV u (mem (3 * P.sChk + 1) u) P.J) u ↔ badAt N.G.Adj n w (P.phiG N.G.Adj w ixF ω P.J) u :=
      badAt_congr (adjLoc_out N w src u) (fun b hb => wLoc_out N w src ((adjLoc_out N w src u b).1 hb))
        (hφ.view hk u u (Or.inl rfl))
        (fun b hb => hφ.view hk u b (Or.inr ((adjLoc_out N w src u b).1 hb)))
    by_cases hc : badAt N.G.Adj n w (P.phiG N.G.Adj w ixF ω P.J) u
    · simp [hc, hb.2 hc]
    · simp [hc, mt hb.1 hc]
  have hval : OracleValid N 0 W (fun _ _ => 0)
      (fun a => if badAt N.G.Adj n w (P.phiG N.G.Adj w ixF ω P.J) a then 0 else ⊤) := by
    refine ⟨fun _ _ _ => Or.inr ⟨le_rfl, zero_le⟩, fun a => ?_⟩
    dsimp only
    split_ifs
    · exact Or.inr (zero_le)
    · exact Or.inl rfl
  have e := h.ora P.sChk _ _ hval hin v
  have h2 := dsrc_or conn (badAt N.G.Adj n w (P.phiG N.G.Adj w ixF ω P.J)) v
  rw [← ENat.toENNReal_ne_top, e]
  exact h2

/-- **The last call.** Its entry is the distance from the source in the reduced weights of the last
potential. -/
theorem fin_eq (h : P.NRun Bm W N w src str ixF ω mem) {Ww : ℕ} (hw : N.NegValid Ww w)
    (hWw : 2 * ((n + 1) * Ww + 1) + P.J * (P.B₀ + 1) * n ≤ W)
    (hφ : Holds N.G mem (P.sPhi P.J) (P.phiG N.G.Adj w ixF ω P.J)) (v : Fin n) :
    (decE (mem (3 * P.sFin + 2) v (3 * P.sFin + 1) 0) : ℝ≥0∞) =
      dsrc N.G.Adj (lenTop (restrictLen (zArc N.G.Adj w) (lenX n w (P.phiG N.G.Adj w ixF ω P.J))))
        (offTop (single src (-(P.phiG N.G.Adj w ixF ω P.J src)).toNat)) v := by
  have hk : 3 * P.sPhi P.J + 3 ≤ 3 * P.sFin + 1 := by
    have := P.sPhi_lt_sChk; have := P.sChk_lt_sFin; omega
  have hin : ∀ u, P.oraIn u (N.negIn w src u) (mem (3 * P.sFin + 1) u) P.sFin =
      N.oracleIn (finLen N.G.Adj n w (P.phiG N.G.Adj w ixF ω P.J))
        (single src (-(P.phiG N.G.Adj w ixF ω P.J src)).toNat) u := by
    intro u
    rw [P.oraIn_fin u _ _]
    unfold oraFin
    refine mkOra_eq N (fun u' hu' => ⟨?_, ?_⟩) ?_
    · exact finLen_congr (adjLoc_out N w src u u') (wLoc_out N w src hu') (hφ.view hk u u (Or.inl rfl))
        (hφ.view hk u u' (Or.inr hu'))
    · exact finLen_congr (adjLoc_in N w src u u') (wLoc_in N w src hu') (hφ.view hk u u' (Or.inr hu'))
        (hφ.view hk u u (Or.inl rfl))
    · have hφu : P.phV u (mem (3 * P.sFin + 1) u) P.J u = P.phiG N.G.Adj w ixF ω P.J u :=
        hφ.view hk u u (Or.inl rfl)
      unfold single
      by_cases hus : u = src
      · subst hus
        simp [Net.negIn, hφu]
      · simp [Net.negIn, hus]
  have hval : OracleValid N 0 W (finLen N.G.Adj n w (P.phiG N.G.Adj w ixF ω P.J))
      (single src (-(P.phiG N.G.Adj w ixF ω P.J src)).toNat) := by
    have hJ : ((P.J * (P.B₀ + 1) * n : ℕ) : ℤ) ≤ W := by
      exact_mod_cast (le_trans (Nat.le_add_left _ _) hWw)
    refine ⟨fun a b hab => ?_, fun a => ?_⟩
    · unfold finLen restrictLen
      split_ifs with hz
      · right
        refine ⟨zero_le, ?_⟩
        obtain ⟨x, hx⟩ := Option.isSome_iff_exists.1 hz.2
        have hx1 : x ≤ Ww := (abs_le.1 (hw a b hab x hx)).2
        have h1 := (phiG_bounds (P := P) (adj := N.G.Adj) (w := w) (ixF := ixF) (ω := ω) P.J a).2
        have h2 := (phiG_bounds (P := P) (adj := N.G.Adj) (w := w) (ixF := ixF) (ω := ω) P.J b).1
        have h3 : lenX n w (P.phiG N.G.Adj w ixF ω P.J) a b ≤ W := by
          unfold lenX yr xw
          rw [Int.toNat_le, zWt_of_eq hx]
          have hW' : ((2 * ((n + 1) * Ww + 1) + P.J * (P.B₀ + 1) * n : ℕ) : ℤ) ≤ W := by
            exact_mod_cast hWw
          push_cast at hW' h2 ⊢
          nlinarith [mul_le_mul_of_nonneg_left hx1 (by positivity : (0 : ℤ) ≤ (n : ℤ) + 1)]
        exact_mod_cast h3
      · left
        rfl
    · unfold single
      split_ifs
      · right
        have h1 := (phiG_bounds (P := P) (adj := N.G.Adj) (w := w) (ixF := ixF) (ω := ω) P.J src).1
        have h3 : (-(P.phiG N.G.Adj w ixF ω P.J src)).toNat ≤ W := by
          rw [Int.toNat_le]
          linarith
        exact_mod_cast h3
      · left
        rfl
  exact h.ora P.sFin _ _ hval hin v

/-- **The output.** On a run with good strings, the outputs of the nodes are correct. -/
theorem negSpec_run (h : P.NRun Bm W N w src str ixF ω mem) (hN : P.NNum n IDX Vm Bm W)
    (hix : ∀ φ B ℓ x v, ℓ ≤ P.L → ixF φ B ℓ x v < IDX) {Ww D : ℕ} (hw : N.NegValid Ww w)
    (hWw : 2 * ((n + 1) * Ww + 1) + P.J * (P.B₀ + 1) * n ≤ W) (hB₀ : 2 * (n + 1) * Ww ≤ P.B₀)
    (ht : 2 ≤ P.t) (hL : 1 ≤ P.L) (hD : N.DiamLE D)
    (hgood : ∀ j : Fin P.J, ¬ PhaseBad N.G.Adj P.L P.R P.t
      (keptS N.G.Adj n w (P.phiG N.G.Adj w ixF ω j) (Bseq P.B₀ j))
      (ysc n w (P.phiG N.G.Adj w ixF ω j) (Bseq P.B₀ j))
      (ixF (P.phiG N.G.Adj w ixF ω j) (Bseq P.B₀ j)) (ω j))
    {K : ℕ} (hK : 3 * P.sFin + 2 ≤ K) :
    N.NegSpec w src (fun v => P.outN n (mem K v)) := by
  have hφ := holds_phis h hN hix P.J le_rfl
  have conn : ∀ u v, Nonempty (Walk N.G.Adj u v) := fun u v => Walk.nonempty_of_sg (hD u v).choose
  have hcard : Fintype.card (Fin n) ≤ n := (Fintype.card_fin n).le
  have hfun : (fun v => P.outN n (mem K v)) = fun v => outS n
      (decide (decE (mem (3 * P.sChk + 2) v (3 * P.sChk + 1) 0) ≠ ⊤))
      (decE (mem (3 * P.sFin + 2) v (3 * P.sFin + 1) 0)) (P.phiG N.G.Adj w ixF ω P.J v) := by
    funext v
    have e1 : mem K v (3 * P.sChk + 1) = mem (3 * P.sChk + 2) v (3 * P.sChk + 1) :=
      h.stable (by have := P.sChk_lt_sFin; omega) v
    have e2 : mem K v (3 * P.sFin + 1) = mem (3 * P.sFin + 2) v (3 * P.sFin + 1) :=
      h.stable (by omega) v
    unfold outN
    rw [e1, e2, hφ.own (k := K) (by have := P.sPhi_lt_sChk; have := P.sChk_lt_sFin; omega) v]
  rw [hfun]
  refine negSpec_of hcard (phiG_bounds P.J src).2 _ _ (fun v => ?_) (fun v => fin_eq h hw hWw hφ v)
    (fun hc a b hab => ?_)
  · rw [decide_eq_true_iff]
    exact chk_iff h hφ conn v
  · have hneg : ∀ a (C : Walk (zArc N.G.Adj w) a a), 0 ≤ C.zw (zWt w) := by
      intro a C
      by_contra h'
      push Not at h'
      exact hc ⟨a, _, walkZ_iff.2 ⟨C, rfl⟩, h'⟩
    have hB₀' : ∀ a b, zArc N.G.Adj w a b → -(P.B₀ : ℤ) ≤ xw n w a b := by
      intro a b hz
      obtain ⟨x, hx⟩ := Option.isSome_iff_exists.1 hz.2
      have hx1 : -(Ww : ℤ) ≤ x := (abs_le.1 (hw a b hz.1 x hx)).1
      unfold xw
      rw [zWt_of_eq hx]
      have : ((2 * (n + 1) * Ww : ℕ) : ℤ) ≤ P.B₀ := by exact_mod_cast hB₀
      push_cast at this
      nlinarith [mul_le_mul_of_nonneg_left hx1 (by positivity : (0 : ℤ) ≤ (n : ℤ) + 1)]
    exact pos_of_noBad hcard hneg ht hL hB₀' ixF ω hgood a b hab

end Run

end NPar

end SsspFlow.Congest
