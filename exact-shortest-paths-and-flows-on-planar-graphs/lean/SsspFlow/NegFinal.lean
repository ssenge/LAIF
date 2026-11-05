import SsspFlow.NegRun
import SsspFlow.LabelFinal

/-!
# Negative weights from the decomposition

`negReduction_of_ldd`: the decomposition of `LDDBox` gives the reduction `NegReduction` with the
factor `logᶜ n`. The machine runs `progN`, with an exact oracle for the calls and the decomposition
for the indices (`nrun_mach`, `run_negAlg`). With `L = log n` levels, `O(log n)` repetitions and
`t = O(log² n)` steps of Lemma 1, all numbers are polynomial in `n` (`negP_nums`), the number of
steps is `O(log¹¹ n)` (`negP_kp`), and the strings with a bad phase are rare (`anyBad_count`).
`negFlow_of_ldd` adds the decomposition to the results of `LabelFinal`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped ENNReal
open Cslib.Congest Cslib.Congest.Algorithm

namespace SsspFlow.Congest

/-! ### The machine -/

section Mach

variable {n : ℕ} {ρL σa σf : Type} {B : ℕ}

/-- The entry of an oracle call: the encoded distance. -/
def resO (outA : Fin n → σa → ℕ∞) (v : Fin n) (s : σa) : ℕ → ℕ := fun _ => encE (outA v s)

/-- The entry of a decomposition: the index. -/
def resI (idxQ : Fin n → σf → ℕ) (v : Fin n) (s : σf) : ℕ → ℕ := fun _ => idxQ v s

/-- The index from a decomposition in `Tf` rounds, with the lengths of a phase with potential `φ` and
bound `B` and the bound `2 ^ (ℓ + 1)`, on the strings `y`. -/
noncomputable def ixQ (Af : Algorithm (Fin n) (LddIn (Fin n) × ρL) σf B) (idxQ : Fin n → σf → ℕ)
    (Tf : ℕ) (N : Net (Fin n)) (w : Fin n → Fin n → Option ℤ) (φ : Fin n → ℤ) (Bp ℓ : ℕ)
    (y : Fin n → ρL) (v : Fin n) : ℕ :=
  idxQ v (Af.run N.G
    (fun u => (N.lddIn (lamS (keptS N.G.Adj n w φ Bp) (ysc n w φ Bp)) (2 ^ (ℓ + 1)) u, y u)) Tf v)

namespace NPar

variable (P : NPar) (Aa : Algorithm (Fin n) (OracleIn (Fin n)) σa B) (outA : Fin n → σa → ℕ∞)
  (Af : Algorithm (Fin n) (LddIn (Fin n) × ρL) σf B) (idxQ : Fin n → σf → ℕ) (Ta Tf T : ℕ)

/-- The strings of the decompositions, by phase, level and repetition. -/
def omg (str : Fin n → Fin P.J → Fin (P.L + 1) → Fin (P.R + 1) → ρL) :
    Fin P.J → Fin (P.L + 1) → Fin (P.R + 1) → Fin n → ρL :=
  fun j ℓ r u => str u j ℓ r

/-- The memory of the machine. -/
noncomputable abbrev memN (N : Net (Fin n)) (w : Fin n → Fin n → Option ℤ) (src : Fin n)
    (str : Fin n → Fin P.J → Fin (P.L + 1) → Fin (P.R + 1) → ρL) : ℕ → Fin n → Mem :=
  memAt Aa Af Ta 1 Tf T P.progN (resO outA) (resI idxQ) N.G fun u => (N.negIn w src u, str u)

/-- **The run of the machine.** -/
theorem nrun_mach {W D : ℕ} (hora : ExactOracleOK n W D Ta Aa outA) {N : Net (Fin n)}
    (hP : N.toRot.Planar) (hD : N.DiamLE D) (w : Fin n → Fin n → Option ℤ) (src : Fin n)
    (str : Fin n → Fin P.J → Fin (P.L + 1) → Fin (P.R + 1) → ρL)
    (hTa : Ta ≤ T) (hTf : Tf ≤ T) (hT : 1 ≤ T) :
    P.NRun B W N w src str (ixQ Af idxQ Tf N w) (P.omg str)
      (P.memN Aa outA Af idxQ Ta Tf T N w src str) where
  stable hjk v := mem_stable Aa Af Ta 1 Tf T P.progN (resO outA) (resI idxQ) N.G _ hjk v
  ora s ℓ φ hV hin v := by
    have e := mem_agg Aa Af Ta 1 Tf T P.progN (resO outA) (resI idxQ) N.G
      (fun u => (N.negIn w src u, str u)) (k := 3 * s + 1) (fun u => N.oracleIn ℓ φ u)
      (fun u => (P.progN_ora u _ _ s).trans (congrArg Sum.inl (hin u))) hTa v
    have e0 : P.memN Aa outA Af idxQ Ta Tf T N w src str (3 * s + 2) v (3 * s + 1) 0 =
        encE (outA v (Aa.run N.G (N.oracleIn ℓ φ) Ta v)) := congrFun e 0
    rw [e0, decE_encE]
    exact hora N ℓ φ hP hD hV v
  ldd s φ Bp j ℓ r hin v := congrFun (mem_face Aa Af Ta 1 Tf T P.progN (resO outA) (resI idxQ) N.G
    (fun u => (N.negIn w src u, str u)) (k := 3 * s)
    (fun u => (N.lddIn (lamS (keptS N.G.Adj n w φ Bp) (ysc n w φ Bp)) (2 ^ ((ℓ : ℕ) + 1)) u, str u j ℓ r))
    (fun u => (P.progN_ldd u _ _ s).trans (congrArg (fun x => Sum.inr (Sum.inr x)) (hin u))) hTf v) 0
  exch s v := mem_relax Aa Af Ta 1 Tf T P.progN (resO outA) (resI idxQ) N.G _ (k := 3 * s + 2) _
    (fun u => P.progN_ex u _ _ s) hT v

/-- **The algorithm of the nodes.** -/
noncomputable def negAlg (KP : ℕ) {B' : ℕ} (hB : B ≤ B') :=
  (((mach Aa Af Ta 1 Tf T P.progN (resO outA) (resI idxQ)).stopAt (KP * T)).premap
    fun _ (i : NegIn (Fin n) × (Fin P.J → Fin (P.L + 1) → Fin (P.R + 1) → ρL)) =>
      ((i, 0, fun _ _ => 0) :
        (NegIn (Fin n) × (Fin P.J → Fin (P.L + 1) → Fin (P.R + 1) → ρL)) × ℕ × Mem)).widen hB

theorem run_negAlg (KP : ℕ) {B' : ℕ} (hB : B ≤ B') (hT : 0 < T) (N : Net (Fin n))
    (w : Fin n → Fin n → Option ℤ) (src : Fin n)
    (str : Fin n → Fin P.J → Fin (P.L + 1) → Fin (P.R + 1) → ρL) {t : ℕ} (ht : KP * T ≤ t) (v : Fin n) :
    ((P.negAlg Aa outA Af idxQ Ta Tf T KP hB).run N.G (fun u => (N.negIn w src u, str u)) t v).2.1.2.2 =
      P.memN Aa outA Af idxQ Ta Tf T N w src str KP v := by
  unfold negAlg
  rw [run_widen, run_premap, run_stopAt, min_eq_right ht]
  exact run_mach Aa Af Ta 1 Tf T P.progN (resO outA) (resI idxQ) N.G _ hT KP v

/-- The strings by node, and by phase, level and repetition. -/
def omgEquiv (P : NPar) (n : ℕ) (ρL : Type) :
    (Fin n → Fin P.J → Fin (P.L + 1) → Fin (P.R + 1) → ρL) ≃
      (Fin P.J → Fin (P.L + 1) → Fin (P.R + 1) → Fin n → ρL) where
  toFun := P.omg
  invFun ω u j ℓ r := ω j ℓ r u
  left_inv _ := rfl
  right_inv _ := rfl

/-- Some phase is bad for the strings `ω`. -/
abbrev anyBad (P : NPar) {n : ℕ} {X : Type} [Fintype X] (adj : Fin n → Fin n → Prop)
    (w : Fin n → Fin n → Option ℤ) (ixF : (Fin n → ℤ) → ℕ → ℕ → X → Fin n → ℕ)
    (ω : Fin P.J → Fin (P.L + 1) → Fin (P.R + 1) → X) : Prop :=
  ∃ j : Fin P.J, PhaseBad adj P.L P.R P.t
    (keptS adj n w (phiS adj n P.L P.R P.t w P.B₀ (decOf P.B₀ ixF ω) j) (Bseq P.B₀ j))
    (ysc n w (phiS adj n P.L P.R P.t w P.B₀ (decOf P.B₀ ixF ω) j) (Bseq P.B₀ j))
    (ixF (phiS adj n P.L P.R P.t w P.B₀ (decOf P.B₀ ixF ω) j) (Bseq P.B₀ j)) (ω j)

end NPar

theorem ixQ_widen (Af : Algorithm (Fin n) (LddIn (Fin n) × ρL) σf B) {B' : ℕ} (h : B ≤ B')
    (idxQ : Fin n → σf → ℕ) (Tf : ℕ) (N : Net (Fin n)) (w : Fin n → Fin n → Option ℤ) :
    ixQ (Af.widen h) idxQ Tf N w = ixQ Af idxQ Tf N w := by
  funext φ Bp ℓ y v
  unfold ixQ
  rw [run_widen]

end Mach

/-! ### Oracles and counts -/

section Count

theorem ExactOracleOK.mono {n W W' D T : ℕ} {σ : Type} {B : ℕ}
    {A : Algorithm (Fin n) (OracleIn (Fin n)) σ B} {out : Fin n → σ → ℕ∞}
    (h : ExactOracleOK n W' D T A out) (hW : W ≤ W') : ExactOracleOK n W D T A out := by
  intro N ℓ φ hP hD hV v
  have hW' : (W : ℕ∞) ≤ W' := by exact_mod_cast hW
  exact h N ℓ φ hP hD (And.intro (fun a b hab => (hV.1 a b hab).imp_right fun h' => ⟨h'.1, h'.2.trans hW'⟩)
    (fun v => (hV.2 v).imp_right fun h' => h'.trans hW')) v

theorem ExactOracleOK.widen {n W D T : ℕ} {σ : Type} {B B' : ℕ}
    {A : Algorithm (Fin n) (OracleIn (Fin n)) σ B} {out : Fin n → σ → ℕ∞}
    (h : ExactOracleOK n W D T A out) (hB : B ≤ B') : ExactOracleOK n W D T (A.widen hB) out := by
  intro N ℓ φ hP hD hV v
  rw [run_widen]
  exact h N ℓ φ hP hD hV v

theorem pcount_equiv {X Y : Type} [Fintype X] [Fintype Y] (e : X ≃ Y) (q : Y → Prop) :
    pcount (fun x => q (e x)) = pcount q := by
  classical
  rw [pcount_eq, pcount_eq, ← Fintype.card_subtype, ← Fintype.card_subtype]
  exact Fintype.card_congr (e.subtypeEquiv fun _ => Iff.rfl)

theorem strCount_le_of {V ρ : Type} [Fintype V] [DecidableEq V] [Fintype ρ] {p q : (V → ρ) → Prop}
    (h : ∀ r, p r → q r) : strCount p ≤ pcount q :=
  pcount_mono h

theorem key_le {u J L R n M P2 : ℕ} (ha : 2 * u * (J * (L + 1) * (R + 1)) ≤ M)
    (hb : 2 * u * (J * (L + 1) * (R + 1)) * n ≤ P2) :
    u * (J * ((L + 1) * (R + 1) * (P2 + n * M))) ≤ M * P2 := by
  have h1 := Nat.mul_le_mul_right P2 ha
  have h2 := Nat.mul_le_mul_right M hb
  nlinarith

theorem final_count {S M P2 A c u : ℕ} (hS : S * (M * P2) ≤ A * c) (hA : u * A ≤ M * P2)
    (hpos : 0 < M * P2) : S * u ≤ c := by
  refine Nat.le_of_mul_le_mul_right (c := M * P2) ?_ hpos
  calc S * u * (M * P2) = u * (S * (M * P2)) := by ring
    _ ≤ u * (A * c) := Nat.mul_le_mul_left _ hS
    _ = u * A * c := by ring
    _ ≤ M * P2 * c := Nat.mul_le_mul_right _ hA
    _ = c * (M * P2) := by ring

end Count

/-! ### The numbers -/

section Numbers

theorem two_pow_logN_le (n : ℕ) : 2 ^ logN n ≤ 2 * (n + 2) := by
  have := Nat.pow_log_le_self 2 (show n + 2 ≠ 0 by omega)
  unfold logN
  rw [pow_succ]
  omega

theorem logN_le (n : ℕ) : logN n ≤ n + 2 := by
  have h1 := Nat.pow_log_le_self 2 (show n + 2 ≠ 0 by omega)
  have h2 : Nat.log 2 (n + 2) < 2 ^ Nat.log 2 (n + 2) := Nat.lt_two_pow_self
  unfold logN
  omega

theorem logN_le_succ {n : ℕ} (hn : 1 ≤ n) : logN n ≤ n + 1 := by
  have h1 := Nat.pow_log_le_self 2 (show n + 2 ≠ 0 by omega)
  have h3 : n < 2 ^ n := Nat.lt_two_pow_self
  unfold logN
  by_contra h
  have h2 : 2 ^ (n + 1) ≤ 2 ^ Nat.log 2 (n + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
  rw [pow_succ] at h2
  omega

theorem two_pow_ge (c b : ℕ) : c + b * (2 * (c + 2 * b + 1)) ≤ 2 ^ (2 * (c + 2 * b + 1)) := by
  have h1 : c + 2 * b + 1 < 2 ^ (c + 2 * b + 1) := Nat.lt_two_pow_self
  have h2 : 2 ^ (2 * (c + 2 * b + 1)) = 2 ^ (c + 2 * b + 1) * 2 ^ (c + 2 * b + 1) := by
    rw [two_mul, pow_add]
  rw [h2]
  nlinarith [Nat.mul_le_mul h1.le h1.le, Nat.zero_le (c * c), Nat.zero_le (b * c)]

/-- The number of repetitions per level, over `logN n`. -/
def repX (K k : ℕ) : ℕ := k + 4 + 2 * (4 * (2 * K + 8) * (k + 4) + 2 * (4 * (2 * K + 8)) + 1)

theorem repX_spec (K k : ℕ) :
    4 * (2 * K + 8) * repX K k ≤ 2 ^ (2 * (4 * (2 * K + 8) * (k + 4) + 2 * (4 * (2 * K + 8)) + 1)) := by
  have h := two_pow_ge (4 * (2 * K + 8) * (k + 4)) (4 * (2 * K + 8))
  calc 4 * (2 * K + 8) * repX K k = 4 * (2 * K + 8) * (k + 4) +
        4 * (2 * K + 8) * (2 * (4 * (2 * K + 8) * (k + 4) + 2 * (4 * (2 * K + 8)) + 1)) := by
          unfold repX; ring
    _ ≤ _ := h

/-- The numbers of the program for the exponent `K` of the weights, the factor `X` of the
repetitions and the constant `Cl` of the decomposition. -/
def negP (K X Cl n : ℕ) : NPar where
  L := logN n
  R := X * logN n
  t := 4 * ((Cl + 1) * logN n ^ 2) + 1
  B₀ := 2 * (n + 1) * (n + 2) ^ K
  cs := (4 * ((Cl + 1) * logN n ^ 2) + 1) * (n + n * (n + 2) ^ Cl + 1)

/-- The number of phases is `O(log n)`. -/
theorem negP_J (K X Cl n : ℕ) : (negP K X Cl n).J ≤ (2 * K + 8) * logN n := by
  have hΛ := one_le_logN n
  have hP := lt_two_pow_logN n
  have hpos : 0 < (n + 2) ^ K := by positivity
  have hB : 2 * (n + 1) * (n + 2) ^ K < 2 ^ (logN n * (K + 2)) :=
    calc 2 * (n + 1) * (n + 2) ^ K < (n + 2) ^ 2 * (n + 2) ^ K :=
          mul_lt_mul_of_pos_right (by nlinarith) hpos
      _ = (n + 2) ^ (K + 2) := by ring
      _ < (2 ^ logN n) ^ (K + 2) := Nat.pow_lt_pow_left hP (by omega)
      _ = 2 ^ (logN n * (K + 2)) := by rw [← pow_mul]
  have hlog := Nat.log_lt_of_lt_pow (b := 2) (by positivity) hB
  show 2 * (Nat.log 2 (2 * (n + 1) * (n + 2) ^ K) + 1) + 4 ≤ _
  nlinarith

theorem sFin_le (P : NPar) : P.sFin ≤ (P.J + 3) * P.Z ^ 5 := by
  have hZ : 1 ≤ P.Z := by unfold NPar.Z; omega
  have e : P.sFin = P.J * P.Z ^ 5 + 3 * P.Z ^ 3 := by
    unfold NPar.sFin addr6 mixZ
    ring
  have : P.Z ^ 3 ≤ P.Z ^ 5 := Nat.pow_le_pow_right hZ (by norm_num)
  rw [e]
  nlinarith

/-- The constant of the number of steps. -/
def repG (K X Cl : ℕ) : ℕ := 3 * (2 * K + 11) * (X + 4 * Cl + 11) ^ 5 + 2

/-- The number of steps is `O(log¹¹ n)`. -/
theorem negP_kp (K X Cl n : ℕ) : 3 * (negP K X Cl n).sFin + 2 ≤ repG K X Cl * logN n ^ 11 := by
  have hΛ := one_le_logN n
  have hJ := negP_J K X Cl n
  have hZ : (negP K X Cl n).Z ≤ (X + 4 * Cl + 11) * logN n ^ 2 := by
    show logN n + X * logN n + (4 * ((Cl + 1) * logN n ^ 2) + 1) + 5 ≤ _
    have h1 : logN n ≤ logN n ^ 2 := by nlinarith
    have h2 : X * logN n ≤ X * logN n ^ 2 := Nat.mul_le_mul_left _ h1
    have h3 : 1 ≤ logN n ^ 2 := Nat.one_le_pow _ _ hΛ
    nlinarith
  have h4 : (negP K X Cl n).J + 3 ≤ (2 * K + 11) * logN n := by nlinarith
  have h5 := Nat.mul_le_mul h4 (Nat.pow_le_pow_left hZ 5)
  have h6 := sFin_le (negP K X Cl n)
  have h7 : 1 ≤ logN n ^ 11 := Nat.one_le_pow _ _ hΛ
  calc 3 * (negP K X Cl n).sFin + 2
      ≤ 3 * ((2 * K + 11) * logN n * ((X + 4 * Cl + 11) * logN n ^ 2) ^ 5) + 2 * logN n ^ 11 := by
        omega
    _ = repG K X Cl * logN n ^ 11 := by unfold repG; ring

/-- **All numbers are polynomial in `n`.** The values fit into `O(log n)` bits, and the lengths and
offsets of the oracle calls are at most `(n + 2) ^ (3 K + 5 Cl + 15)`. -/
theorem negP_nums (K X Cl n : ℕ) :
    2 * ((negP K X Cl n).J * ((negP K X Cl n).B₀ + 1) * n + (n + 2) ^ Cl + (negP K X Cl n).cs) <
        2 ^ ((3 * K + 5 * Cl + 15) * logN n) ∧
      n + (n + n * (n + 2) ^ Cl) + (negP K X Cl n).cs ≤ (n + 2) ^ (3 * K + 5 * Cl + 15) ∧
      2 * ((n + 1) * (n + 2) ^ K + 1) + (negP K X Cl n).J * ((negP K X Cl n).B₀ + 1) * n ≤
        (n + 2) ^ (3 * K + 5 * Cl + 15) := by
  have hX : 2 ≤ n + 2 := by omega
  have hn : n ≤ (n + 2) ^ 1 := by rw [pow_one]; omega
  have hΛ : logN n ≤ (n + 2) ^ 1 := by rw [pow_one]; exact logN_le n
  have hJ : (negP K X Cl n).J ≤ (n + 2) ^ (2 * K + 8 + 1) :=
    (negP_J K X Cl n).trans (pb_mul (pb_const hX _) hΛ)
  have hB : (negP K X Cl n).B₀ + 1 ≤ (n + 2) ^ (K + 2) := by
    show 2 * (n + 1) * (n + 2) ^ K + 1 ≤ _
    have h1 : 1 ≤ (n + 2) ^ K := Nat.one_le_pow _ _ (by omega)
    have h2 : 2 * n + 3 ≤ (n + 2) ^ 2 := by nlinarith
    calc 2 * (n + 1) * (n + 2) ^ K + 1 ≤ (2 * n + 3) * (n + 2) ^ K := by nlinarith
      _ ≤ (n + 2) ^ 2 * (n + 2) ^ K := Nat.mul_le_mul_right _ h2
      _ = (n + 2) ^ (K + 2) := by ring
  have ht : (negP K X Cl n).t ≤ (n + 2) ^ (4 * Cl + 5 + 2) := by
    show 4 * ((Cl + 1) * logN n ^ 2) + 1 ≤ _
    have h1 : logN n ^ 2 ≤ (n + 2) ^ 2 := Nat.pow_le_pow_left (logN_le n) 2
    have h2 : 1 ≤ (n + 2) ^ 2 := Nat.one_le_pow _ _ (by omega)
    have h3 := Nat.mul_le_mul_left Cl h1
    calc 4 * ((Cl + 1) * logN n ^ 2) + 1 ≤ (4 * Cl + 5) * (n + 2) ^ 2 := by nlinarith
      _ ≤ (n + 2) ^ (4 * Cl + 5) * (n + 2) ^ 2 := Nat.mul_le_mul_right _ (pb_const hX _)
      _ = (n + 2) ^ (4 * Cl + 5 + 2) := by rw [← pow_add]
  have hm : n + n * (n + 2) ^ Cl + 1 ≤ (n + 2) ^ (Cl + 2) := by
    have h1 : 1 ≤ (n + 2) ^ Cl := Nat.one_le_pow _ _ (by omega)
    have h2 := Nat.mul_le_mul_left n h1
    calc n + n * (n + 2) ^ Cl + 1 ≤ (2 * n + 1) * (n + 2) ^ Cl := by nlinarith
      _ ≤ (n + 2) ^ 2 * (n + 2) ^ Cl := Nat.mul_le_mul_right _ (by nlinarith)
      _ = (n + 2) ^ (Cl + 2) := by ring
  have hcs : (negP K X Cl n).t * (n + n * (n + 2) ^ Cl + 1) ≤
      (n + 2) ^ (4 * Cl + 5 + 2 + (Cl + 2)) := pb_mul ht hm
  have e1 : (negP K X Cl n).J * ((negP K X Cl n).B₀ + 1) * n ≤ (n + 2) ^ (3 * K + 5 * Cl + 12) :=
    pb_le hX (pb_mul (pb_mul hJ hB) hn) (by omega)
  have e2 : (n + 2) ^ Cl ≤ (n + 2) ^ (3 * K + 5 * Cl + 12) := pb_le hX le_rfl (by omega)
  have e3 : (negP K X Cl n).cs ≤ (n + 2) ^ (3 * K + 5 * Cl + 12) := pb_le hX hcs (by omega)
  have e4 : n + n * (n + 2) ^ Cl ≤ (n + 2) ^ (3 * K + 5 * Cl + 12) :=
    pb_le hX (by omega : n + n * (n + 2) ^ Cl ≤ (n + 2) ^ (Cl + 2)) (by omega)
  have e5 : 2 * ((n + 1) * (n + 2) ^ K + 1) ≤ (n + 2) ^ (3 * K + 5 * Cl + 12) := by
    have h1 : 1 ≤ (n + 2) ^ K := Nat.one_le_pow _ _ (by omega)
    have h2 : 2 * ((n + 1) * (n + 2) ^ K + 1) ≤ (n + 2) ^ 2 * (n + 2) ^ K := by
      nlinarith [Nat.zero_le (n * n * (n + 2) ^ K), Nat.zero_le (n * (n + 2) ^ K)]
    exact pb_le hX (h2.trans_eq (by ring : (n + 2) ^ 2 * (n + 2) ^ K = (n + 2) ^ (K + 2))) (by omega)
  have e6 : 8 * (n + 2) ^ (3 * K + 5 * Cl + 12) ≤ (n + 2) ^ (3 * K + 5 * Cl + 15) := by
    have : 8 ≤ (n + 2) ^ 3 :=
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ (n + 2) ^ 3 := Nat.pow_le_pow_left hX 3
    calc 8 * (n + 2) ^ (3 * K + 5 * Cl + 12) ≤ (n + 2) ^ 3 * (n + 2) ^ (3 * K + 5 * Cl + 12) :=
          Nat.mul_le_mul_right _ this
      _ = (n + 2) ^ (3 * K + 5 * Cl + 15) := by ring
  have e7 : (n + 2) ^ (3 * K + 5 * Cl + 15) < 2 ^ ((3 * K + 5 * Cl + 15) * logN n) := by
    rw [mul_comm (3 * K + 5 * Cl + 15) (logN n), pow_mul]
    exact Nat.pow_lt_pow_left (lt_two_pow_logN n) (by omega)
  refine ⟨by omega, by omega, by omega⟩

/-- The strings with a bad phase, against the first bound. -/
theorem count_a {n k a X J L R : ℕ} (hn : 1 ≤ n) (hJ : J ≤ a * logN n) (hL : L + 1 ≤ 2 * logN n)
    (hR : R + 1 ≤ 2 * X * logN n) :
    2 * (n + 1) ^ k * (J * (L + 1) * (R + 1)) ≤ (n + 1) ^ (k + 3 + 8 * a * X) := by
  have hΛ := logN_le_succ hn
  have h1 : J * (L + 1) * (R + 1) ≤ 4 * a * X * (n + 1) ^ 3 :=
    calc J * (L + 1) * (R + 1) ≤ a * logN n * (2 * logN n) * (2 * X * logN n) :=
          Nat.mul_le_mul (Nat.mul_le_mul hJ hL) hR
      _ = 4 * a * X * logN n ^ 3 := by ring
      _ ≤ 4 * a * X * (n + 1) ^ 3 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hΛ 3)
  have h2 : 8 * a * X ≤ (n + 1) ^ (8 * a * X) := pb_const (by omega) _
  calc 2 * (n + 1) ^ k * (J * (L + 1) * (R + 1)) ≤ 2 * (n + 1) ^ k * (4 * a * X * (n + 1) ^ 3) :=
        Nat.mul_le_mul_left _ h1
    _ = 8 * a * X * ((n + 1) ^ k * (n + 1) ^ 3) := by ring
    _ ≤ (n + 1) ^ (8 * a * X) * ((n + 1) ^ k * (n + 1) ^ 3) := Nat.mul_le_mul_right _ h2
    _ = (n + 1) ^ (k + 3 + 8 * a * X) := by ring

/-- The strings with a bad phase, against the second bound. -/
theorem count_b {n k a X Y J L R : ℕ} (hX : X = k + 4 + Y) (hY : 4 * a * X ≤ 2 ^ Y)
    (hJ : J ≤ a * logN n) (hL : L + 1 ≤ 2 * logN n) (hR : R = X * logN n) :
    2 * (n + 1) ^ k * (J * (L + 1) * (R + 1)) * n ≤ 2 ^ (R + 1) := by
  have hP := lt_two_pow_logN n
  have hΛ : logN n ≤ 2 ^ logN n := Nat.lt_two_pow_self.le
  have hΛ1 := one_le_logN n
  have hXΛ : 1 ≤ X * logN n := Nat.mul_pos (by omega) hΛ1
  have hR1 : R + 1 ≤ 2 * X * logN n := by rw [hR]; nlinarith
  have h1 : J * (L + 1) * (R + 1) ≤ 4 * a * X * (2 ^ logN n) ^ 3 :=
    calc J * (L + 1) * (R + 1) ≤ a * logN n * (2 * logN n) * (2 * X * logN n) :=
          Nat.mul_le_mul (Nat.mul_le_mul hJ hL) hR1
      _ = 4 * a * X * logN n ^ 3 := by ring
      _ ≤ 4 * a * X * (2 ^ logN n) ^ 3 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hΛ 3)
  have h2 : (n + 1) ^ k ≤ (2 ^ logN n) ^ k := Nat.pow_le_pow_left (by omega) k
  have h3 : n ≤ 2 ^ logN n := by omega
  have h4 : 4 * a * X ≤ 2 ^ (Y * logN n) :=
    hY.trans (Nat.pow_le_pow_right (by norm_num) (Nat.le_mul_of_pos_right Y hΛ1))
  calc 2 * (n + 1) ^ k * (J * (L + 1) * (R + 1)) * n
      ≤ 2 * (2 ^ logN n) ^ k * (4 * a * X * (2 ^ logN n) ^ 3) * 2 ^ logN n :=
        Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul_left 2 h2) h1) h3
    _ = 2 * (4 * a * X) * 2 ^ ((k + 4) * logN n) := by ring
    _ ≤ 2 * 2 ^ (Y * logN n) * 2 ^ ((k + 4) * logN n) :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 2 h4)
    _ = 2 ^ (R + 1) := by rw [hR, hX]; ring

/-- **The rounds.** -/
theorem negRounds_le {G Cl cl c₀ Λ T D KP C : ℕ} (hΛ : 1 ≤ Λ) (hD : 1 ≤ D) (hKP : KP ≤ G * Λ ^ 11)
    (hC : G * (Cl + 1) ^ 2 ≤ C) (hC1 : 1 ≤ C) :
    KP * (T + Cl * Λ ^ c₀ * (T + Cl * Λ ^ cl * D) + 1) ≤
      C * Λ ^ (11 + c₀) * (T + C * Λ ^ (cl + 1) * D) := by
  have hu : 1 ≤ Λ ^ c₀ := Nat.one_le_pow _ _ hΛ
  have hv : 1 ≤ Λ ^ cl := Nat.one_le_pow _ _ hΛ
  have hv' : Λ ^ cl ≤ Λ ^ (cl + 1) := Nat.pow_le_pow_right hΛ (by omega)
  have huvD : 1 ≤ Λ ^ c₀ * Λ ^ cl * D := Nat.mul_pos (Nat.mul_pos hu hv) hD
  have huT : T ≤ Λ ^ c₀ * T := Nat.le_mul_of_pos_left T hu
  have h1 : T + Cl * Λ ^ c₀ * (T + Cl * Λ ^ cl * D) + 1 ≤
      (Cl + 1) ^ 2 * Λ ^ c₀ * (T + Λ ^ cl * D) := by
    nlinarith [Nat.zero_le (Cl * Cl * (Λ ^ c₀ * T)), Nat.zero_le (Cl * (Λ ^ c₀ * T)),
      Nat.zero_le (Cl * (Λ ^ c₀ * Λ ^ cl * D))]
  have h2 : Λ ^ cl ≤ C * Λ ^ (cl + 1) := hv'.trans (Nat.le_mul_of_pos_left _ hC1)
  calc KP * (T + Cl * Λ ^ c₀ * (T + Cl * Λ ^ cl * D) + 1)
      ≤ G * Λ ^ 11 * ((Cl + 1) ^ 2 * Λ ^ c₀ * (T + Λ ^ cl * D)) := Nat.mul_le_mul hKP h1
    _ = G * (Cl + 1) ^ 2 * Λ ^ (11 + c₀) * (T + Λ ^ cl * D) := by ring
    _ ≤ C * Λ ^ (11 + c₀) * (T + C * Λ ^ (cl + 1) * D) :=
        Nat.mul_le_mul (Nat.mul_le_mul_right _ hC) (Nat.add_le_add_left (Nat.mul_le_mul_right _ h2) _)

end Numbers

/-! ### The reduction -/

/-- **Negative weights from the decomposition.** The decomposition of `LDDBox` gives the reduction
`NegReduction` with the factor `logᶜ n`. -/
theorem negReduction_of_ldd (hL : LDDBox) : ∃ c', NegReduction (tauPolylog c') := by
  obtain ⟨c₀, hL⟩ := hL
  refine ⟨11 + c₀, fun K k => ?_⟩
  obtain ⟨Cl, cl, hLDD⟩ := hL 3 (k + 3 + 8 * (2 * K + 8) * repX K k)
  refine ⟨Cl + (3 * K + 5 * Cl + 15) + repG K (repX K k) Cl * (Cl + 1) ^ 2, cl + 1,
    fun n D T B hD σ A out hA => ?_⟩
  set C := Cl + (3 * K + 5 * Cl + 15) + repG K (repX K k) Cl * (Cl + 1) ^ 2 with hC
  have hΛ := one_le_logN n
  have hAl : ExactOracleOK n ((n + 2) ^ Cl) D T A out :=
    hA.mono (Nat.pow_le_pow_right (by omega) (by omega))
  obtain ⟨ρL, _, _, σf, Q, idx, hQ⟩ := hLDD n D T B hD σ A out hAl
  obtain ⟨hn1, hn2, hn3⟩ := negP_nums K (repX K k) Cl n
  have hJ := negP_J K (repX K k) Cl n
  have hkp := negP_kp K (repX K k) Cl n
  set P := negP K (repX K k) Cl n with hP
  have hPL : P.L = logN n := rfl
  have hPR : P.R = repX K k * logN n := rfl
  have hPt : P.t = 4 * ((Cl + 1) * logN n ^ 2) + 1 := rfl
  set Tf := Cl * logN n ^ c₀ * (T + Cl * logN n ^ cl * D) with hTf
  set Bm := B + Cl * logN n ^ cl + (3 * K + 5 * Cl + 15) * logN n with hBm
  have h1 : B ≤ Bm := by omega
  have h2 : B + Cl * logN n ^ cl ≤ Bm := by omega
  have hBm' : Bm ≤ B + C * logN n ^ (cl + 1) := by
    have e1 : logN n ^ cl ≤ logN n ^ (cl + 1) := Nat.pow_le_pow_right hΛ (by omega)
    have e2 : logN n ≤ logN n ^ (cl + 1) :=
      (pow_one (logN n)).symm.le.trans (Nat.pow_le_pow_right hΛ (by omega))
    have e3 := Nat.mul_le_mul_left Cl e1
    have e4 := Nat.mul_le_mul_left (3 * K + 5 * Cl + 15) e2
    have e5 : C * logN n ^ (cl + 1) = Cl * logN n ^ (cl + 1) +
        (3 * K + 5 * Cl + 15) * logN n ^ (cl + 1) +
          repG K (repX K k) Cl * (Cl + 1) ^ 2 * logN n ^ (cl + 1) := by
      rw [hC]; ring
    omega
  refine ⟨Fin P.J → Fin (P.L + 1) → Fin (P.R + 1) → ρL, inferInstance, inferInstance, _,
    P.negAlg (A.widen h1) out (Q.widen h2) idx T Tf (T + Tf + 1) (3 * P.sFin + 2) hBm',
    fun v st => P.outN n st.2.1.2.2, ?_⟩
  intro N w s hPl hDm hV
  rcases Nat.eq_zero_or_pos n with hn0 | hn
  · exact absurd s.2 (by omega)
  -- the oracle and the numbers of the run
  have hora : ExactOracleOK n ((n + 2) ^ (3 * K + 5 * Cl + 15)) D T (A.widen h1) out :=
    (hA.mono (Nat.pow_le_pow_right (by omega) (by omega))).widen h1
  have hCq : 1 ≤ (Cl + 1) * logN n ^ 2 := Nat.mul_pos (Nat.succ_pos Cl) (pow_pos hΛ 2)
  have hN : P.NNum n ((n + 2) ^ Cl) (P.J * (P.B₀ + 1) * n + (n + 2) ^ Cl + P.cs) Bm
      ((n + 2) ^ (3 * K + 5 * Cl + 15)) :=
    { idx0 := by positivity
      t1 := by omega
      cs := le_rfl
      vm := le_rfl
      bm := hn1.trans_le (Nat.pow_le_pow_right (by norm_num) (by omega))
      w := hn2 }
  -- the decompositions
  have hd : ∀ ℓ ≤ P.L, 2 ^ (ℓ + 1) ≤ (n + 2) ^ 3 := by
    intro ℓ hℓ
    have e1 : 2 ^ (ℓ + 1) ≤ 2 ^ (logN n + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have e2 := two_pow_logN_le n
    have e3 : 4 * (n + 2) ≤ (n + 2) ^ 3 := by
      have h4 : 2 ^ 2 ≤ (n + 2) ^ 2 := Nat.pow_le_pow_left (by omega) 2
      calc 4 * (n + 2) = 2 ^ 2 * (n + 2) := by norm_num
        _ ≤ (n + 2) ^ 2 * (n + 2) := Nat.mul_le_mul_right _ h4
        _ = (n + 2) ^ 3 := by ring
    have e4 : 2 ^ (logN n + 1) = 2 * 2 ^ logN n := by ring
    omega
  have hlen : ∀ (φ : Fin n → ℤ) (Bp : ℕ) (a b : Fin n), N.G.Adj a b →
      lamS (keptS N.G.Adj n w φ Bp) (ysc n w φ Bp) a b = ⊤ ∨
        lamS (keptS N.G.Adj n w φ Bp) (ysc n w φ Bp) a b ≤ ((n + 2) ^ 3 : ℕ) := by
    intro φ Bp a b _
    unfold lamS restrictLen
    split_ifs with hk
    · right
      have e1 : posPart (ysc n w φ Bp) a b ≤ n := Int.toNat_le.mpr (max_le hk.2 (by positivity))
      have e2 : n ≤ (n + 2) ^ 3 := (Nat.le_add_right n 2).trans (Nat.le_self_pow (by norm_num) _)
      exact_mod_cast e1.trans e2
    · exact Or.inl rfl
  have hP1 : ∀ (φ : Fin n → ℤ) (Bp : ℕ), ∀ ℓ < P.L, pcount (fun x : Fin n → ρL =>
      ¬ CloseX N.G.Adj (lamS (keptS N.G.Adj n w φ Bp) (ysc n w φ Bp)) (ixQ Q idx Tf N w φ Bp) ℓ x) *
        (n + 1) ^ (k + 3 + 8 * (2 * K + 8) * repX K k) ≤ Fintype.card (Fin n → ρL) := by
    intro φ Bp ℓ hℓ
    obtain ⟨hq1, -, -⟩ := hQ N _ (2 ^ (ℓ + 1)) hPl hDm (hlen φ Bp) Nat.one_le_two_pow (hd ℓ hℓ.le)
    exact hq1
  have hP2 : ∀ (φ : Fin n → ℤ) (Bp : ℕ), ∀ ℓ < P.L, ∀ a b, keptS N.G.Adj n w φ Bp a b →
      pcount (fun x : Fin n → ρL => ixQ Q idx Tf N w φ Bp ℓ x b < ixQ Q idx Tf N w φ Bp ℓ x a) *
        (2 ^ (ℓ + 1) * (n + 1) ^ (k + 3 + 8 * (2 * K + 8) * repX K k)) ≤
      ((Cl + 1) * logN n ^ 2 * posPart (ysc n w φ Bp) a b *
          (n + 1) ^ (k + 3 + 8 * (2 * K + 8) * repX K k) + 2 ^ (ℓ + 1)) *
        Fintype.card (Fin n → ρL) := by
    intro φ Bp ℓ hℓ a b hk
    obtain ⟨-, hq2, -⟩ := hQ N _ (2 ^ (ℓ + 1)) hPl hDm (hlen φ Bp) Nat.one_le_two_pow (hd ℓ hℓ.le)
    have hne : lamS (keptS N.G.Adj n w φ Bp) (ysc n w φ Bp) a b ≠ ⊤ := by
      unfold lamS restrictLen
      rw [ite_eq_left hk]
      exact ENat.natCast_ne_top _
    have e : (lamS (keptS N.G.Adj n w φ Bp) (ysc n w φ Bp) a b).toNat = posPart (ysc n w φ Bp) a b := by
      unfold lamS restrictLen
      rw [ite_eq_left hk]
      rfl
    have h := hq2 a b hk.1.1 hne
    rw [e] at h
    refine h.trans (Nat.mul_le_mul_right _ (Nat.add_le_add_right ?_ _))
    exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _
      (Nat.mul_le_mul_right _ (Nat.le_add_right Cl 1)))
  have hix : ∀ (φ : Fin n → ℤ) (Bp ℓ : ℕ) (x : Fin n → ρL) (v : Fin n), ℓ ≤ P.L →
      ixQ Q idx Tf N w φ Bp ℓ x v < (n + 2) ^ Cl := by
    intro φ Bp ℓ x v hℓ
    obtain ⟨-, -, hq3⟩ := hQ N _ (2 ^ (ℓ + 1)) hPl hDm (hlen φ Bp) Nat.one_le_two_pow (hd ℓ hℓ)
    exact hq3 x v
  -- the rounds
  have htau : tauPolylog (11 + c₀) (n + 2) = logN n ^ (11 + c₀) := rfl
  have hrounds : (3 * P.sFin + 2) * (T + Tf + 1) ≤
      C * tauPolylog (11 + c₀) (n + 2) * (T + C * logN n ^ (cl + 1) * D) := by
    rw [htau]
    exact negRounds_le (Cl := Cl) (cl := cl) (c₀ := c₀) (T := T) hΛ hD hkp (by omega) (by omega)
  -- good strings give a correct answer
  have hS1 : ∀ r : Fin n → Fin P.J → Fin (P.L + 1) → Fin (P.R + 1) → ρL,
      ¬ P.anyBad N.G.Adj w (ixQ Q idx Tf N w) (P.omg r) →
      N.NegSpec w s (fun v => P.outN n ((P.negAlg (A.widen h1) out (Q.widen h2) idx T Tf (T + Tf + 1)
        (3 * P.sFin + 2) hBm').run N.G (fun u => (N.negIn w s u, r u))
          (C * tauPolylog (11 + c₀) (n + 2) * (T + C * logN n ^ (cl + 1) * D)) v).2.1.2.2) := by
    intro r hr
    have hrun := P.nrun_mach (A.widen h1) out (Q.widen h2) idx T Tf (T + Tf + 1) hora hPl hDm w s r
      (by omega) (by omega) (by omega)
    rw [ixQ_widen] at hrun
    have hfun : (fun v => P.outN n ((P.negAlg (A.widen h1) out (Q.widen h2) idx T Tf (T + Tf + 1)
        (3 * P.sFin + 2) hBm').run N.G (fun u => (N.negIn w s u, r u))
          (C * tauPolylog (11 + c₀) (n + 2) * (T + C * logN n ^ (cl + 1) * D)) v).2.1.2.2) =
        fun v => P.outN n (P.memN (A.widen h1) out (Q.widen h2) idx T Tf (T + Tf + 1) N w s r
          (3 * P.sFin + 2) v) := by
      funext v
      rw [P.run_negAlg (A.widen h1) out (Q.widen h2) idx T Tf (T + Tf + 1) (3 * P.sFin + 2) hBm'
        (by omega) N w s r hrounds v]
    rw [hfun]
    exact NPar.negSpec_run hrun hN hix hV hn3 le_rfl (by omega) (by omega) hDm (fun j hj => hr ⟨j, hj⟩) le_rfl
  -- the count
  have hL2 : P.L + 1 ≤ 2 * logN n := by omega
  have hR2 : P.R + 1 ≤ 2 * repX K k * logN n := by
    have e1 : 0 < repX K k * logN n := Nat.mul_pos (by unfold repX; omega) hΛ
    have e2 : 2 * repX K k * logN n = 2 * (repX K k * logN n) := by ring
    omega
  have hM : Fintype.card (Fin n) ≤ (n + 1) ^ (k + 3 + 8 * (2 * K + 8) * repX K k) := by
    rw [Fintype.card_fin]
    exact (Nat.le_succ n).trans (Nat.le_self_pow (by positivity) _)
  have hLV : Fintype.card (Fin n) ≤ 2 ^ (P.L + 1) := by
    rw [Fintype.card_fin, hPL]
    have e1 := lt_two_pow_logN n
    have e2 : 2 ^ logN n ≤ 2 ^ (logN n + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have ht : P.t + 1 = 2 * (2 * ((Cl + 1) * logN n ^ 2) + 1) := by rw [hPt]; ring
  have hcount := anyBad_count (J := P.J) (B₀ := P.B₀) (R := P.R) (ixQ Q idx Tf N w) hM hLV ht hP1 hP2
  rw [Fintype.card_fin] at hcount
  have hkey := key_le (count_a (k := k) hn hJ hL2 hR2)
    (count_b (k := k) (a := 2 * K + 8) (X := repX K k)
      (Y := 2 * (4 * (2 * K + 8) * (k + 4) + 2 * (4 * (2 * K + 8)) + 1)) (R := P.R) rfl
      (repX_spec K k) hJ hL2 hPR)
  refine (Nat.mul_le_mul_right _ (strCount_le_of
    (q := fun r => P.anyBad N.G.Adj w (ixQ Q idx Tf N w) (P.omg r)) fun r hr => ?_)).trans ?_
  · by_contra h'
    exact hr (hS1 r h')
  have he : pcount (fun r => P.anyBad N.G.Adj w (ixQ Q idx Tf N w) (P.omg r)) =
      pcount (P.anyBad N.G.Adj w (ixQ Q idx Tf N w)) := pcount_equiv (P.omgEquiv n ρL) _
  rw [he, Fintype.card_congr (P.omgEquiv n ρL)]
  exact final_count hcount hkey (by positivity)

/-- **Negative weights and maximum flow** with the factor `logᶜ n`, from the realization of
metrics, distance labels, the names of the faces, the aggregation primitive, the smoothing and the
decomposition. -/
theorem negFlow_of_ldd {Cr Cl cl : ℕ} (hC : RealizationBox Cr) (hL : DistanceLabelBox Cl cl)
    (hF : FaceIdBox) (hA : AggBox) (hS : SmoothingBox) (hD : LDDBox) :
    ∃ c, NegSsspBound (tauPolylog c) ∧ MaxFlowBound (tauPolylog c) := by
  obtain ⟨c, hR⟩ := negReduction_of_ldd hD
  exact ⟨c, negFlow_polylog_of_boxes c hC hL hF hA hS hR⟩

end SsspFlow.Congest
