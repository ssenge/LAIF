import SsspFlow.LabelProof
import SsspFlow.MaxFlow

/-!
# The Label Hypothesis from the classics

`labelHypothesis_of_boxes`: the realization of metrics in a disk, distance labels of planar graphs, the names of the
faces and the aggregation primitive give `LabelHypothesis`.

The first part holds the arithmetic of the parameters. All numbers are polynomial in the size of the network
(`exp_bounds`), so they have logarithmically many bits, and the number of rounds is polylogarithmic in the size times
the diameter and the accuracy (`labelRounds_le`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped ENNReal

namespace SsspFlow.Congest

open Cslib.Congest Cslib.Congest.Algorithm FourColor RotSystem RotSystem.RootedTree

section Arith

theorem pb_const {X : ℕ} (hX : 2 ≤ X) (c : ℕ) : c ≤ X ^ c :=
  (Nat.lt_two_pow_self).le.trans (Nat.pow_le_pow_left hX c)

theorem pb_one (X : ℕ) : 1 ≤ X ^ 0 := by simp

theorem pb_add {X : ℕ} (hX : 2 ≤ X) {a b p q : ℕ} (h1 : a ≤ X ^ p) (h2 : b ≤ X ^ q) :
    a + b ≤ X ^ (p + q + 1) := by
  have hX1 : 1 ≤ X := by omega
  have e1 : X ^ p ≤ X ^ (p + q) := Nat.pow_le_pow_right hX1 (by omega)
  have e2 : X ^ q ≤ X ^ (p + q) := Nat.pow_le_pow_right hX1 (by omega)
  rw [pow_succ]
  have e3 : 2 * X ^ (p + q) ≤ X ^ (p + q) * X := by
    rw [mul_comm]
    exact Nat.mul_le_mul_left _ hX
  omega

theorem pb_mul {X a b p q : ℕ} (h1 : a ≤ X ^ p) (h2 : b ≤ X ^ q) : a * b ≤ X ^ (p + q) := by
  rw [pow_add]
  exact Nat.mul_le_mul h1 h2

theorem pb_pow {X a p : ℕ} (h1 : a ≤ X ^ p) (k : ℕ) : a ^ k ≤ X ^ (p * k) := by
  rw [pow_mul]
  exact Nat.pow_le_pow_left h1 k

theorem pb_le {X a p q : ℕ} (hX : 2 ≤ X) (h : a ≤ X ^ p) (hpq : p ≤ q) : a ≤ X ^ q :=
  h.trans (Nat.pow_le_pow_right (by omega) hpq)

/-- All numbers are polynomial in the size of the network. -/
theorem exp_bounds {X n e h L H U s Wt B₀ K Cr : ℕ} (hX : 2 ≤ X) (hn : n ≤ X) (hL : L ≤ X) (he : e ≤ X ^ K)
    (hh : h ≤ X) (hWt : Wt ≤ X ^ K) (hH : H = 3 * (L + 1)) (hU : U = 8 * (2 * H + 3) * e)
    (hs : s = Cr * (2 + H * (2 + 4 * h) + 1) ^ 6 + 1) (hB : B₀ = 2 * (U * (2 * n * n) * Wt) + 1) :
    U ≤ X ^ (19 + K) ∧ s + 2 * s * B₀ + 2 ≤ X ^ (2 * Cr + 238 + 2 * K) ∧ 2 * n * n + 3 * n + 14 ≤ X ^ 24 ∧
      (2 * H + 2) * (2 * (h + (1 + H * (2 + 4 * h))) + 1) ≤ X ^ 29 := by
  have hn' : n ≤ X ^ 1 := by rwa [pow_one]
  have hL' : L ≤ X ^ 1 := by rwa [pow_one]
  have hh' : h ≤ X ^ 1 := by rwa [pow_one]
  have hc := pb_const hX
  have h1 := pb_one X
  have hH' : H ≤ X ^ 5 := by
    rw [hH]
    exact pb_le hX (pb_mul (hc 3) (pb_add hX hL' h1)) (by omega)
  have hA : 2 + 4 * h ≤ X ^ 8 := pb_le hX (pb_add hX (hc 2) (pb_mul (hc 4) hh')) (by omega)
  have hHA : H * (2 + 4 * h) ≤ X ^ 13 := pb_le hX (pb_mul hH' hA) (by omega)
  have hJ : 2 + H * (2 + 4 * h) + 1 ≤ X ^ 17 :=
    pb_le hX (pb_add hX (pb_add hX (hc 2) hHA) h1) (by omega)
  have hS : s ≤ X ^ (Cr + 103) := by
    rw [hs]
    exact pb_le hX (pb_add hX (pb_mul (hc Cr) (pb_pow hJ 6)) h1) (by omega)
  have hU' : U ≤ X ^ (19 + K) := by
    rw [hU]
    exact pb_le hX (pb_mul (pb_mul (hc 8) (pb_add hX (pb_mul (hc 2) hH') (hc 3))) he) (by omega)
  have hB' : B₀ ≤ X ^ (26 + 2 * K) := by
    rw [hB]
    exact pb_le hX (pb_add hX (pb_mul (hc 2) (pb_mul (pb_mul hU' (pb_mul (pb_mul (hc 2) hn') hn')) hWt)) h1)
      (by omega)
  refine ⟨hU', ?_, ?_, ?_⟩
  · exact pb_le hX (pb_add hX (pb_add hX hS (pb_mul (pb_mul (hc 2) hS) hB')) (hc 2)) (by omega)
  · exact pb_le hX (pb_add hX (pb_add hX (pb_mul (pb_mul (hc 2) hn') hn') (pb_mul (hc 3) hn')) (hc 14)) (by omega)
  · exact pb_le hX (pb_mul (pb_add hX (pb_mul (hc 2) hH') (hc 2))
      (pb_add hX (pb_mul (hc 2) (pb_add hX hh' (pb_add hX h1 hHA))) h1)) (by omega)

/-- The sizes of the bags and of the calls. -/
theorem nums_le {L D h H : ℕ} (hL : 1 ≤ L) (hD : 1 ≤ D) (hh : h ≤ D) (hH : H = 3 * (L + 1)) :
    (2 * H + 2) * (2 * (h + (1 + H * (2 + 4 * h))) + 1) ≤ 1078 * (L * (L * D)) ∧
    (2 * H + 2) * (2 * (2 * h + 1 + 2 * (1 + H * (2 + 4 * h))) + 1) ≤ 2170 * (L * (L * D)) ∧
    16 * (1 + (H + 1) * (2 + 4 * h)) + (1 + H * (2 + 4 * h)) ≤ 725 * (L * D) ∧
    5 * (1 + H * (2 + 4 * h)) + 4 ≤ 189 * (L * D) ∧
    1 + (H + 1) * (2 + 4 * h) ≤ 43 * (L * D) := by
  have hm : 1 ≤ L * D := Nat.mul_pos hL hD
  have hDm : D ≤ L * D := Nat.le_mul_of_pos_left _ hL
  have h1 : H ≤ 6 * L := by omega
  have h2 : 2 + 4 * h ≤ 6 * D := by omega
  have h3 : H * (2 + 4 * h) ≤ 36 * (L * D) := by
    calc H * (2 + 4 * h) ≤ (6 * L) * (6 * D) := Nat.mul_le_mul h1 h2
      _ = 36 * (L * D) := by ring
  have h4 : (H + 1) * (2 + 4 * h) ≤ 42 * (L * D) := by
    calc (H + 1) * (2 + 4 * h) ≤ (7 * L) * (6 * D) := Nat.mul_le_mul (by omega) h2
      _ = 42 * (L * D) := by ring
  have h5 : 2 * H + 2 ≤ 14 * L := by omega
  refine ⟨?_, ?_, by omega, by omega, by omega⟩
  · calc (2 * H + 2) * (2 * (h + (1 + H * (2 + 4 * h))) + 1) ≤ (14 * L) * (77 * (L * D)) :=
        Nat.mul_le_mul h5 (by omega)
      _ = 1078 * (L * (L * D)) := by ring
  · calc (2 * H + 2) * (2 * (2 * h + 1 + 2 * (1 + H * (2 + 4 * h))) + 1) ≤ (14 * L) * (155 * (L * D)) :=
        Nat.mul_le_mul h5 (by omega)
      _ = 2170 * (L * (L * D)) := by ring

/-- **The number of rounds.** -/
theorem labelRounds_le {Ca Cf cf cl A₀ L D e h H Lb : ℕ} (hL : 1 ≤ L) (hD : 1 ≤ D) (he : 1 ≤ e) (hh : h ≤ D)
    (hH : H = 3 * (L + 1)) (hLb : Lb ≤ 120 * A₀ * (L ^ (cl + 1) * e)) :
    (10 + 6 * (H + 1) + H + 1) *
      (Ca * 2 * ((2 * H + 2) * (2 * (h + (1 + H * (2 + 4 * h))) + 1) +
          ((5 * (1 + H * (2 + 4 * h)) + 4) +
            (16 * (1 + (H + 1) * (2 + 4 * h)) + (1 + H * (2 + 4 * h))) * (5 + (Lb + 1))) + 1) +
        ((2 * H + 2) * (2 * (2 * h + 1 + 2 * (1 + H * (2 + 4 * h))) + 1) + 1) + Cf * L ^ cf * D + 1) ≤
      59 * (2 * Ca * (1268 + 725 * (120 * A₀ + 6)) + 2171 + Cf + 1) * (L ^ (cl + 4 + cf) * D * e) := by
  obtain ⟨s1, s2, s3, s4, -⟩ := nums_le hL hD hh hH
  have hLp : 1 ≤ L ^ (cl + 1) := Nat.one_le_pow _ _ hL
  obtain ⟨Z, hZ⟩ : ∃ Z, Z = L ^ (cl + 1) * e := ⟨_, rfl⟩
  have hZ1 : 1 ≤ Z := by rw [hZ]; exact Nat.mul_pos hLp he
  obtain ⟨m, hm⟩ : ∃ m, m = L * D := ⟨_, rfl⟩
  have hm1 : 1 ≤ m := by rw [hm]; exact Nat.mul_pos hL hD
  rw [← hm] at s3 s4
  have s1' : (2 * H + 2) * (2 * (h + (1 + H * (2 + 4 * h))) + 1) ≤ 1078 * (L * m) := by rw [hm]; exact s1
  have s2' : (2 * H + 2) * (2 * (2 * h + 1 + 2 * (1 + H * (2 + 4 * h))) + 1) ≤ 2170 * (L * m) := by rw [hm]; exact s2
  obtain ⟨R0, hR0⟩ : ∃ R0, R0 = 120 * A₀ + 6 := ⟨_, rfl⟩
  have hLb' : Lb ≤ 120 * A₀ * Z := by rw [hZ]; exact hLb
  have b1 : 5 + (Lb + 1) ≤ R0 * Z := by
    have : R0 * Z = 120 * A₀ * Z + 6 * Z := by rw [hR0]; ring
    omega
  obtain ⟨Q, hQ⟩ : ∃ Q, Q = L * (m * Z) := ⟨_, rfl⟩
  have hmZ : m ≤ m * Z := Nat.le_mul_of_pos_right _ hZ1
  have hmZ1 : 1 ≤ m * Z := Nat.mul_pos hm1 hZ1
  have hLQ : L * m ≤ Q := by rw [hQ]; exact Nat.mul_le_mul_left _ hmZ
  have hmQ : m * Z ≤ Q := by rw [hQ]; exact Nat.le_mul_of_pos_left _ hL
  have hQ1 : 1 ≤ Q := by omega
  have b2 : (16 * (1 + (H + 1) * (2 + 4 * h)) + (1 + H * (2 + 4 * h))) * (5 + (Lb + 1)) ≤ 725 * R0 * Q := by
    calc _ ≤ (725 * m) * (R0 * Z) := Nat.mul_le_mul s3 b1
      _ = 725 * R0 * (m * Z) := by ring
      _ ≤ 725 * R0 * Q := Nat.mul_le_mul_left _ hmQ
  have b3 : (2 * H + 2) * (2 * (h + (1 + H * (2 + 4 * h))) + 1) +
      ((5 * (1 + H * (2 + 4 * h)) + 4) +
        (16 * (1 + (H + 1) * (2 + 4 * h)) + (1 + H * (2 + 4 * h))) * (5 + (Lb + 1))) + 1 ≤
      (1268 + 725 * R0) * Q := by
    have e1 : (1268 + 725 * R0) * Q = 1268 * Q + 725 * R0 * Q := by ring
    have e2 : m ≤ m * Z := hmZ
    omega
  have hLc : 1 ≤ L ^ cf := Nat.one_le_pow _ _ hL
  obtain ⟨Q₁, hQ₁⟩ : ∃ Q₁, Q₁ = L ^ cf * Q := ⟨_, rfl⟩
  have hQQ : Q ≤ Q₁ := by rw [hQ₁]; exact Nat.le_mul_of_pos_left _ hLc
  have hDQ : D ≤ Q := by
    have h1 : D ≤ m := by rw [hm]; exact Nat.le_mul_of_pos_left _ hL
    have h2 : m ≤ L * m := Nat.le_mul_of_pos_left _ hL
    omega
  have b4 : Cf * L ^ cf * D ≤ Cf * Q₁ := by
    rw [hQ₁, mul_assoc]
    exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hDQ)
  have b5 : Ca * 2 * ((2 * H + 2) * (2 * (h + (1 + H * (2 + 4 * h))) + 1) +
      ((5 * (1 + H * (2 + 4 * h)) + 4) +
        (16 * (1 + (H + 1) * (2 + 4 * h)) + (1 + H * (2 + 4 * h))) * (5 + (Lb + 1))) + 1) ≤
      2 * Ca * (1268 + 725 * R0) * Q₁ := by
    calc _ ≤ Ca * 2 * ((1268 + 725 * R0) * Q) := Nat.mul_le_mul_left _ b3
      _ = 2 * Ca * (1268 + 725 * R0) * Q := by ring
      _ ≤ _ := Nat.mul_le_mul_left _ hQQ
  have b6 : (2 * H + 2) * (2 * (2 * h + 1 + 2 * (1 + H * (2 + 4 * h))) + 1) + 1 ≤ 2171 * Q₁ := by omega
  have b7 : Ca * 2 * ((2 * H + 2) * (2 * (h + (1 + H * (2 + 4 * h))) + 1) +
      ((5 * (1 + H * (2 + 4 * h)) + 4) +
        (16 * (1 + (H + 1) * (2 + 4 * h)) + (1 + H * (2 + 4 * h))) * (5 + (Lb + 1))) + 1) +
      ((2 * H + 2) * (2 * (2 * h + 1 + 2 * (1 + H * (2 + 4 * h))) + 1) + 1) + Cf * L ^ cf * D + 1 ≤
      (2 * Ca * (1268 + 725 * R0) + 2171 + Cf + 1) * Q₁ := by
    have e1 : (2 * Ca * (1268 + 725 * R0) + 2171 + Cf + 1) * Q₁ =
        2 * Ca * (1268 + 725 * R0) * Q₁ + 2171 * Q₁ + Cf * Q₁ + Q₁ := by ring
    omega
  have hKP : 10 + 6 * (H + 1) + H + 1 ≤ 59 * L := by omega
  calc _ ≤ (59 * L) * ((2 * Ca * (1268 + 725 * R0) + 2171 + Cf + 1) * Q₁) := Nat.mul_le_mul hKP b7
    _ = 59 * (2 * Ca * (1268 + 725 * R0) + 2171 + Cf + 1) * (L * Q₁) := by ring
    _ = _ := by
      rw [hR0, hQ₁, hQ, hm, hZ]
      ring

/-- The exponent of all numbers of a run. -/
def expE (Cr Cl cl K : ℕ) : ℕ :=
  ((Cl + (2 * Cr + 238 + 2 * K) * cl + (19 + K)) + 32) + ((2 * Cr + 238 + 2 * K) * cl + K + 2) + (31 + K)

theorem bits_le {X W U s B₀ Wt sA Cr Cl cl K : ℕ} (hX : 2 ≤ X) (hU : U ≤ X ^ (19 + K))
    (hY : s + 2 * s * B₀ + 2 ≤ X ^ (2 * Cr + 238 + 2 * K)) (hW : W ≤ X ^ 24) (hs : sA ≤ X ^ 29) (hWt : Wt ≤ X ^ K) :
    W + 6 + bagLen Cl cl U s B₀ ≤ X ^ expE Cr Cl cl K ∧
      bagWord cl s B₀ + Wt + 1 ≤ X ^ expE Cr Cl cl K ∧
      2 * (sA * Wt) ≤ X ^ expE Cr Cl cl K := by
  have hc := pb_const hX
  have hlog : Nat.log 2 (s + 2 * s * B₀ + 2) ≤ X ^ (2 * Cr + 238 + 2 * K) := (Nat.log_le_self _ _).trans hY
  have hLb : bagLen Cl cl U s B₀ ≤ X ^ (Cl + (2 * Cr + 238 + 2 * K) * cl + (19 + K)) :=
    pb_mul (pb_mul (hc Cl) (pb_pow hlog cl)) hU
  have hWb : bagWord cl s B₀ ≤ X ^ ((2 * Cr + 238 + 2 * K) * cl) := pb_pow hY cl
  refine ⟨pb_le hX (pb_add hX (pb_add hX hW (hc 6)) hLb) ?_,
    pb_le hX (pb_add hX (pb_add hX hWb hWt) (pb_one X)) ?_, pb_le hX (pb_mul (hc 2) (pb_mul hs hWt)) ?_⟩
  all_goals unfold expE; omega

theorem sq_le_two_pow {a m b : ℕ} (h : a ≤ 2 ^ m) (hb : m * 2 ≤ b) : a ^ 2 ≤ 2 ^ b :=
  calc a ^ 2 ≤ (2 ^ m) ^ 2 := Nat.pow_le_pow_left h 2
    _ = 2 ^ (m * 2) := (pow_mul _ _ _).symm
    _ ≤ 2 ^ b := Nat.pow_le_pow_right (by norm_num) hb

/-- The length of the labels of a bag. -/
theorem bagLen_le {L H e U s B₀ Cl cl pY : ℕ} (hL : 1 ≤ L) (hH : H = 3 * (L + 1)) (hU : U = 8 * (2 * H + 3) * e)
    (hY : s + 2 * s * B₀ + 2 ≤ (2 ^ L) ^ pY) :
    bagLen Cl cl U s B₀ ≤ 120 * (Cl * pY ^ cl) * (L ^ (cl + 1) * e) := by
  have h1 : Nat.log 2 (s + 2 * s * B₀ + 2) ≤ L * pY :=
    calc _ ≤ Nat.log 2 ((2 ^ L) ^ pY) := Nat.log_mono_right hY
      _ = L * pY := by rw [← pow_mul, Nat.log_pow (by norm_num)]
  have h2 : U ≤ 120 * L * e := by
    rw [hU]
    exact Nat.mul_le_mul_right e (by omega)
  calc Cl * Nat.log 2 (s + 2 * s * B₀ + 2) ^ cl * U ≤ Cl * (L * pY) ^ cl * (120 * L * e) :=
        Nat.mul_le_mul (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h1 cl)) h2
    _ = _ := by
      rw [mul_pow, pow_succ]
      ring

/-- The accuracy of one level, multiplied over all levels. -/
theorem cU_acc {H U e : ℕ} (he : 1 ≤ e) (hU : U = 8 * (2 * H + 3) * e) :
    cU U ^ (2 * H + 1) ≤ 2 ∧ cU U ^ (2 * H + 1) ≤ 1 + (e : ℝ≥0∞)⁻¹ := by
  have hle : 8 * (2 * H + 1) * e ≤ U := by
    rw [hU]
    exact Nat.mul_le_mul_right e (by omega)
  have h8 : 8 * (2 * H + 1) ≤ U := (Nat.le_mul_of_pos_right _ he).trans hle
  have hU1 : 1 ≤ U := by omega
  refine ⟨pow_cU_le_two hU1 _ h8, (pow_cU_le hU1 _ h8).trans (add_le_add_right ?_ 1)⟩
  have he0 : (e : ℝ≥0∞) ≠ 0 := by exact_mod_cast (by omega : e ≠ 0)
  rw [ENNReal.le_inv_iff_mul_le]
  calc 8 * (((2 * H + 1 : ℕ) : ℝ≥0∞)) * (U : ℝ≥0∞)⁻¹ * e = ((8 * (2 * H + 1) * e : ℕ) : ℝ≥0∞) * (U : ℝ≥0∞)⁻¹ := by
        push_cast
        ring
    _ ≤ (U : ℝ≥0∞) * (U : ℝ≥0∞)⁻¹ := by gcongr
    _ ≤ 1 := ENNReal.mul_inv_le_one _

end Arith

section Tiny

variable {n : ℕ}

/-- The label of a network with at most one node. -/
def tinyOut (v : Fin n) : LabelOut (Fin n) :=
  { chain := [⟨0, [⟨v, 0, 0⟩]⟩]
    treeBags := fun _ => [] }

/-- A network with at most one node has one bag with its node as the hub. -/
theorem labelsOK_tiny (hn : n ≤ 1) (N : Net (Fin n)) (ℓ : Fin n → Fin n → ℕ) (e hh ss ww : ℕ) (hss : 1 ≤ ss) :
    LabelsOK N ℓ e hh ss ww (fun v => tinyOut v) := by
  classical
  have hsub : ∀ a b : Fin n, a = b := fun a b => Fin.ext (by omega)
  have hE : ∀ v, ∀ E ∈ (tinyOut v : LabelOut (Fin n)).chain, E.bag = 0 ∧ E.hubs = [⟨v, 0, 0⟩] := by
    intro v E hE
    obtain rfl := List.mem_singleton.1 hE
    exact ⟨rfl, rfl⟩
  have hF : ∀ v, ∀ E ∈ (tinyOut v : LabelOut (Fin n)).chain, ∀ F ∈ E.hubs, F.hub = v ∧ F.toHub = 0 ∧ F.fromHub = 0 := by
    intro v E hEm F hF
    rw [(hE v E hEm).2] at hF
    obtain rfl := List.mem_singleton.1 hF
    exact ⟨rfl, rfl, rfl⟩
  have hd : ∀ v, dist N.G.Adj (lenOf ℓ) Set.univ v v ≤ 0 := fun v =>
    (iInf₂_le (Walk.nil v) (by simp)).trans (by simp [Walk.wt])
  exact ⟨{
    H := oneBag N
    tree := fun x a b => x = 0 ∧ N.G.Adj a b
    depth := fun _ => 0
    depth_kid := fun _ _ h => h.elim
    height := fun _ => Nat.zero_le _
    tree_adj := fun _ _ _ h => h.2
    tree_symm := fun _ _ _ h => ⟨h.1, h.2.symm⟩
    tree_span := fun x a b _ _ => by
      obtain rfl := hsub a b
      exact ⟨.nil a, by simp⟩
    congestion := fun _ _ _ => ⟨{0}, by simp, fun x _ h => by simp [h.1]⟩
    hub_card := fun x => by
      refine le_trans ?_ hss
      refine (Set.ncard_le_card _).trans ?_
      rw [Nat.card_eq_fintype_card, Fintype.card_fin]
      exact hn
    chain_iff := fun v x => by
      rw [oneBag_chain]
      constructor
      · rintro rfl
        exact ⟨_, List.mem_singleton.2 rfl, rfl⟩
      · rintro ⟨E, hEm, rfl⟩
        exact (hE v E hEm).1
    hubs_iff := fun v E hEm y => by
      constructor
      · intro _
        rw [(hE v E hEm).2]
        exact ⟨_, List.mem_singleton.2 rfl, hsub _ _⟩
      · intro _
        exact (hE v E hEm).1
    tree_know := fun v u hvu => absurd (hsub v u) hvu.ne
    to_lo := fun v E hEm F hFm => by
      obtain ⟨h1, h2, -⟩ := hF v E hEm F hFm
      rw [h1, h2]
      simpa using hd v
    to_hi := fun v E hEm F hFm => by
      obtain ⟨-, h2, -⟩ := hF v E hEm F hFm
      rw [h2]
      simp
    from_lo := fun v E hEm F hFm => by
      obtain ⟨h1, -, h2⟩ := hF v E hEm F hFm
      rw [h1, h2]
      simpa using hd v
    from_hi := fun v E hEm F hFm => by
      obtain ⟨-, -, h2⟩ := hF v E hEm F hFm
      rw [h2]
      simp
    name_lt := fun v E hEm => by
      rw [(hE v E hEm).1]
      positivity
    treeBags_lt := fun _ _ _ h => by
      simp [tinyOut] at h
    value_lt := fun v E hEm F hFm => by
      obtain ⟨-, h2, h3⟩ := hF v E hEm F hFm
      rw [h2, h3]
      have : (0 : ℕ∞) < ((2 ^ ww : ℕ) : ℕ∞) := by exact_mod_cast Nat.two_pow_pos ww
      exact ⟨Or.inr this, Or.inr this⟩ }⟩

/-- The algorithm that does nothing. -/
def idleAlg (V I : Type) (B : ℕ) : Algorithm V I Unit B where
  init _ _ := ()
  send _ _ _ _ := false
  step _ _ _ := ()
  out _ _ := false

end Tiny

section Big

/-- The numbers of a run fit. -/
theorem numOK_big {n e D K H h U s Wt B₀ Lb Wb W sA kA f b Bm Tr₀ Cr Cl cl Ca E CC cc : ℕ}
    (q : List ℕ → List ℕ → ℕ∞) (heK : e ≤ (n + 2) ^ K) (hD : 1 ≤ D)
    (hH : H = 3 * (logN n + 1)) (hh : h = min D n) (hU : U = 8 * (2 * H + 3) * e)
    (hs : s = Cr * (2 + H * (2 + 4 * h) + 1) ^ 6 + 1) (hWt : Wt = (n + 2) ^ K)
    (hB : B₀ = 2 * (U * (2 * n * n) * Wt) + 1) (hLb : Lb = bagLen Cl cl U s B₀) (hWb : Wb = bagWord cl s B₀)
    (hW : W = 2 * n * n + 3 * n + 14) (hsA : sA = (2 * H + 2) * (2 * (h + (1 + H * (2 + 4 * h))) + 1))
    (hkA : kA = (5 * (1 + H * (2 + 4 * h)) + 4) +
      (16 * (1 + (H + 1) * (2 + 4 * h)) + (1 + H * (2 + 4 * h))) * (5 + (Lb + 1)))
    (hb : b = 2 * f + 2 * (logN n * E)) (hBm : Bm = Ca * (b + logN n) + f + b)
    (hTr : Tr₀ = (2 * H + 2) * (2 * (2 * h + 1 + 2 * (1 + H * (2 + 4 * h))) + 1))
    (hE : E = expE Cr Cl cl K) (hCC : 1078 + 2 * E + 1 ≤ CC) (hcc : 2 ≤ cc) :
    NumOK n ⟨H, U, s, Lb, Wb, q⟩ W h sA kA b Bm Tr₀ Wt (CC * logN n) (CC * logN n ^ cc * D) (CC * logN n ^ cc) := by
  have hL1 : 1 ≤ logN n := by unfold logN; omega
  obtain ⟨L, hL⟩ : ∃ L, L = logN n := ⟨_, rfl⟩
  rw [← hL] at hH hb hBm hL1 ⊢
  obtain ⟨X, hXe⟩ : ∃ X, X = 2 ^ L := ⟨_, rfl⟩
  have hnX : n + 2 < X := by
    rw [hXe, hL]
    exact Nat.lt_pow_succ_log_self (by norm_num) _
  have hX : 2 ≤ X := by omega
  have hLX : L ≤ X := by
    rw [hXe]
    exact Nat.lt_two_pow_self.le
  have hhX : h ≤ X := by
    rw [hh]
    exact (min_le_right _ _).trans (by omega)
  have heX : e ≤ X ^ K := heK.trans (Nat.pow_le_pow_left (by omega) K)
  have hWtX : Wt ≤ X ^ K := by
    rw [hWt]
    exact Nat.pow_le_pow_left (by omega) K
  obtain ⟨-, hYX, hWX, hsX⟩ := exp_bounds hX (show n ≤ X by omega) hLX heX hhX hWtX hH hU hs hB
  obtain ⟨hUX, -⟩ := exp_bounds hX (show n ≤ X by omega) hLX heX hhX hWtX hH hU hs hB
  rw [← hW] at hWX
  rw [← hsA] at hsX
  obtain ⟨hb1, hb2, hb3⟩ := bits_le (Cl := Cl) (cl := cl) hX hUX hYX hWX hsX hWtX
  have hXE : X ^ expE Cr Cl cl K = 2 ^ (L * E) := by rw [hXe, hE, pow_mul]
  rw [hXE, ← hLb] at hb1
  rw [hXE, ← hWb] at hb2
  rw [hXE] at hb3
  have hbb : L * E * 2 ≤ b := by
    rw [hb]
    omega
  have hLc : L ≤ L ^ cc := Nat.le_self_pow (by omega) _
  have hww : 2 * (L * E) + 1 ≤ CC * L ^ cc := by
    calc 2 * (L * E) + 1 ≤ (2 * E + 1) * L := by
          have : (2 * E + 1) * L = 2 * (L * E) + L := by ring
          omega
      _ ≤ CC * L ^ cc := Nat.mul_le_mul (by omega) hLc
  have hWsq : ∀ c, c ≤ 6 → (W + c) ^ 2 ≤ (W + 6 + Lb) ^ 2 := fun c hc => Nat.pow_le_pow_left (by omega) 2
  have hsq : (W + 6 + Lb) ^ 2 ≤ 2 ^ b := sq_le_two_pow hb1 hbb
  have hLLD : L * (L * D) ≤ L ^ cc * D := by
    rw [← mul_assoc, ← pow_two]
    exact Nat.mul_le_mul_right D (Nat.pow_le_pow_right (by omega) hcc)
  have hss : 1078 * (L * (L * D)) ≤ CC * L ^ cc * D := by
    rw [mul_assoc CC]
    exact Nat.mul_le_mul (by omega) hLLD
  obtain ⟨n1, -, -, -, n5⟩ := nums_le hL1 hD ((hh ▸ min_le_left _ _ : h ≤ D)) hH
  have hLD : L * D ≤ L * (L * D) := Nat.le_mul_of_pos_left _ hL1
  have hlog : L ≤ n + 2 := by
    have : Nat.log 2 (n + 2) < n + 2 := Nat.log_lt_self 2 (by omega)
    rw [hL]
    unfold logN
    omega
  have a1 : (2 * H + 2) * (2 * (2 * h + 1 + 2 * (1 + H * (2 + 4 * h))) + 1) ≤ Tr₀ + 1 := by omega
  have a2 : h + 1 ≤ Tr₀ := by
    have : 2 * (2 * h + 1 + 2 * (1 + H * (2 + 4 * h))) + 1 ≤
        (2 * H + 2) * (2 * (2 * h + 1 + 2 * (1 + H * (2 + 4 * h))) + 1) := Nat.le_mul_of_pos_left _ (by omega)
    omega
  have a3 : (2 * H + 2) * (2 * (h + (1 + H * (2 + 4 * h))) + 1) ≤ sA := hsA.ge
  have a4 : 5 * (1 + H * (2 + 4 * h)) + 4 ≤ kA := by omega
  have a5 : (16 * (1 + (H + 1) * (2 + 4 * h)) + (1 + H * (2 + 4 * h))) * (5 + (Lb + 1)) ≤ kA := by omega
  have a6 : 5 ≤ W := by omega
  have a7 : 2 * n * n + 2 ≤ W := by omega
  have a8 : H ≤ W := by omega
  have a9 : (W + 1) ^ 2 ≤ 2 ^ Bm :=
    (hWsq 1 (by omega)).trans (hsq.trans (Nat.pow_le_pow_right (by norm_num) (by omega)))
  have a10 : (W + 2) * (W + 2) ≤ 2 ^ b := by
    rw [← pow_two]
    exact (hWsq 2 (by omega)).trans hsq
  have a11 : (W + 6 + Lb) ^ 2 ≤ 2 ^ b := hsq
  have a12 : Wb + Wt + 1 ≤ 2 ^ b := hb2.trans (Nat.pow_le_pow_right (by norm_num) (by omega))
  have a13 : H ≤ CC * L := (show H ≤ 6 * L by omega).trans (Nat.mul_le_mul_right L (by omega))
  have a14 : (2 * H + 2) * (2 * (h + (1 + H * (2 + 4 * h))) + 1) ≤ CC * L ^ cc * D := n1.trans hss
  have a15 : 1 + (H + 1) * (2 + 4 * h) ≤ CC * L ^ cc * D := by omega
  have a16 : (W + 1) ^ 2 ≤ 2 ^ (CC * L ^ cc) :=
    (hWsq 1 (by omega)).trans (sq_le_two_pow hb1 (by omega))
  have a17 : 2 * (((2 * H + 2) * (2 * (h + (1 + H * (2 + 4 * h))) + 1)) * Wt) < 2 ^ (CC * L ^ cc) := by
    rw [← hsA]
    exact hb3.trans_lt (Nat.pow_lt_pow_right (by norm_num) (by omega))
  exact ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17⟩

/-- The bandwidth of a run. -/
theorem band_big {L E f b Bm Ca Cf cf CC cc : ℕ} (hL1 : 1 ≤ L) (hf : f = Cf * L ^ cf) (hb : b = 2 * f + 2 * (L * E))
    (hBm : Bm = Ca * (b + L) + f + b) (hcf : cf ≤ cc) (hcc : 1 ≤ cc)
    (hCC : Ca * (2 * Cf + 2 * E + 1) + 3 * Cf + 2 * E ≤ CC) : Bm ≤ CC * L ^ cc := by
  have h1 : L ^ cf ≤ L ^ cc := Nat.pow_le_pow_right hL1 hcf
  have h2 : L ≤ L ^ cc := Nat.le_self_pow (by omega) _
  obtain ⟨Z, hZ⟩ : ∃ Z, Z = L ^ cc := ⟨_, rfl⟩
  rw [← hZ] at h1 h2 ⊢
  have h3 : f ≤ Cf * Z := by
    rw [hf]
    exact Nat.mul_le_mul_left _ h1
  have h4 : L * E ≤ E * Z := by
    rw [mul_comm]
    exact Nat.mul_le_mul_left _ h2
  have h5 : b + L ≤ (2 * Cf + 2 * E + 1) * Z := by
    have : (2 * Cf + 2 * E + 1) * Z = 2 * (Cf * Z) + 2 * (E * Z) + Z := by ring
    omega
  have h6 : Ca * (b + L) ≤ Ca * ((2 * Cf + 2 * E + 1) * Z) := Nat.mul_le_mul_left _ h5
  calc Bm ≤ (Ca * (2 * Cf + 2 * E + 1) + 3 * Cf + 2 * E) * Z := by
        have : (Ca * (2 * Cf + 2 * E + 1) + 3 * Cf + 2 * E) * Z =
            Ca * ((2 * Cf + 2 * E + 1) * Z) + 3 * (Cf * Z) + 2 * (E * Z) := by ring
        omega
    _ ≤ CC * Z := Nat.mul_le_mul_right _ hCC

end Big

section Final

/-- **The Label Hypothesis.** The realization of metrics in a disk, distance labels of planar graphs, the names of the
faces and the aggregation primitive give the labels in the message model. -/
theorem labelHypothesis_of_boxes {Cr Cl cl : ℕ} (hC : RealizationBox Cr) (hL : DistanceLabelBox Cl cl)
    (hF : FaceIdBox) (hA : AggBox) : LabelHypothesis := by
  classical
  obtain ⟨Cf, cf, hF⟩ := hF
  obtain ⟨Ca, hA⟩ := hA
  intro K
  obtain ⟨E, hE⟩ : ∃ E, E = expE Cr Cl cl K := ⟨_, rfl⟩
  obtain ⟨R, hR⟩ : ∃ R, R = 59 * (2 * Ca * (1268 + 725 * (120 * (Cl * (2 * Cr + 238 + 2 * K) ^ cl) + 6)) + 2171 + Cf + 1) :=
    ⟨_, rfl⟩
  obtain ⟨CC, hCC⟩ : ∃ CC, CC = R + (Ca * (2 * Cf + 2 * E + 1) + 3 * Cf + 2 * E) + 1078 + 2 * E + 1 := ⟨_, rfl⟩
  obtain ⟨cc, hcc⟩ : ∃ cc, cc = cl + 4 + cf := ⟨_, rfl⟩
  refine ⟨CC, cc, fun n e D he1 heK hD => ?_⟩
  by_cases hn : n ≤ 1
  · refine ⟨Unit, idleAlg _ _ _, fun v _ => tinyOut v, fun N ℓ _ _ _ => ?_⟩
    have hL1 : 1 ≤ logN n := by unfold logN; omega
    have h1 : 1 ≤ CC * logN n ^ cc * D :=
      Nat.mul_pos (Nat.mul_pos (by omega) (Nat.pow_pos hL1)) hD
    exact labelsOK_tiny hn N ℓ e _ _ _ h1
  have hn2 : 2 ≤ n := by omega
  have hL1 : 1 ≤ logN n := by unfold logN; omega
  obtain ⟨H, hH⟩ : ∃ H, H = 3 * (logN n + 1) := ⟨_, rfl⟩
  obtain ⟨h, hh⟩ : ∃ h, h = min D n := ⟨_, rfl⟩
  obtain ⟨U, hU⟩ : ∃ U, U = 8 * (2 * H + 3) * e := ⟨_, rfl⟩
  obtain ⟨s, hs⟩ : ∃ s, s = Cr * (2 + H * (2 + 4 * h) + 1) ^ 6 + 1 := ⟨_, rfl⟩
  obtain ⟨Wt, hWt⟩ : ∃ Wt, Wt = (n + 2) ^ K := ⟨_, rfl⟩
  obtain ⟨B₀, hB⟩ : ∃ B₀, B₀ = 2 * (U * (2 * n * n) * Wt) + 1 := ⟨_, rfl⟩
  obtain ⟨Lb, hLb⟩ : ∃ Lb, Lb = bagLen Cl cl U s B₀ := ⟨_, rfl⟩
  obtain ⟨Wb, hWb⟩ : ∃ Wb, Wb = bagWord cl s B₀ := ⟨_, rfl⟩
  obtain ⟨W, hW⟩ : ∃ W, W = 2 * n * n + 3 * n + 14 := ⟨_, rfl⟩
  obtain ⟨sA, hsA⟩ : ∃ sA, sA = (2 * H + 2) * (2 * (h + (1 + H * (2 + 4 * h))) + 1) := ⟨_, rfl⟩
  obtain ⟨kA, hkA⟩ : ∃ kA, kA = (5 * (1 + H * (2 + 4 * h)) + 4) +
      (16 * (1 + (H + 1) * (2 + 4 * h)) + (1 + H * (2 + 4 * h))) * (5 + (Lb + 1)) := ⟨_, rfl⟩
  obtain ⟨f, hf⟩ : ∃ f, f = Cf * logN n ^ cf := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b, b = 2 * f + 2 * (logN n * E) := ⟨_, rfl⟩
  obtain ⟨Bm, hBm⟩ : ∃ Bm, Bm = Ca * (b + logN n) + f + b := ⟨_, rfl⟩
  obtain ⟨Tr₀, hTr⟩ : ∃ Tr₀, Tr₀ = (2 * H + 2) * (2 * (2 * h + 1 + 2 * (1 + H * (2 + 4 * h))) + 1) := ⟨_, rfl⟩
  obtain ⟨Ta, hTa⟩ : ∃ Ta, Ta = Ca * 2 * (sA + kA + 1) := ⟨_, rfl⟩
  obtain ⟨Tf, hTf⟩ : ∃ Tf, Tf = Cf * logN n ^ cf * D := ⟨_, rfl⟩
  obtain ⟨T, hT⟩ : ∃ T, T = Ta + (Tr₀ + 1) + Tf + 1 := ⟨_, rfl⟩
  have hU1 : 1 ≤ U := by
    rw [hU]
    exact Nat.mul_pos (by omega) he1
  obtain ⟨q, hq⟩ := hL U hU1
  obtain ⟨P, hP⟩ : ∃ P : ValP, P = ⟨H, U, s, Lb, Wb, q⟩ := ⟨_, rfl⟩
  have hNum : NumOK n P W h sA kA b Bm Tr₀ Wt (CC * logN n) (CC * logN n ^ cc * D) (CC * logN n ^ cc) := by
    rw [hP]
    exact numOK_big q heK hD hH hh hU hs hWt hB hLb hWb hW hsA hkA hb hBm hTr hE (by omega) (by omega)
  have hBB : Bm ≤ CC * logN n ^ cc :=
    band_big hL1 hf hb hBm (by omega) (by omega) (by omega)
  have hround : (phVal H H + 1) * T ≤ CC * logN n ^ cc * D * e := by
    have hY : s + 2 * s * B₀ + 2 ≤ (2 ^ logN n) ^ (2 * Cr + 238 + 2 * K) := by
      have hnX : n + 2 < 2 ^ logN n := Nat.lt_pow_succ_log_self (by norm_num) _
      exact (exp_bounds (X := 2 ^ logN n) (by omega) (by omega) Nat.lt_two_pow_self.le
        (heK.trans (Nat.pow_le_pow_left (by omega) K))
        (by rw [hh]; exact (min_le_right _ _).trans (by omega))
        (by rw [hWt]; exact Nat.pow_le_pow_left (by omega) K) hH hU hs hB).2.1
    have h1 := bagLen_le (Cl := Cl) (cl := cl) hL1 hH hU hY
    rw [← hLb] at h1
    have h2 := labelRounds_le (Ca := Ca) (Cf := Cf) (cf := cf) hL1 hD he1 (hh ▸ min_le_left _ _ : h ≤ D) hH h1
    rw [← hsA, ← hkA, ← hTr, ← hTa, ← hTf, ← hT] at h2
    unfold phVal
    calc _ ≤ _ := h2
      _ = R * (logN n ^ cc * D * e) := by rw [hR, hcc]
      _ ≤ CC * (logN n ^ cc * D * e) := Nat.mul_le_mul_right _ (by omega)
      _ = _ := by ring
  have hT0 : 0 < T := by omega
  have hw1 : Ca * (b + logN n) ≤ Bm := by omega
  have hw2 : Cf * logN n ^ cf ≤ Bm := by omega
  obtain ⟨σa, Aa, outa, hAa⟩ := hA n sA 2 kA b
  obtain ⟨σf, Af, outf, hFf⟩ := hF n D hD
  obtain ⟨r, hr⟩ : ∃ r : Fin n, r = ⟨0, by omega⟩ := ⟨_, rfl⟩
  refine ⟨_, finalAlg (Aa.widen hw1) (Af.widen hw2) outa outf Ta (Tr₀ + 1) Tf T (phVal P.H P.H + 1) P W r hBB,
    fun v st => outL P W r st.2.1.1.nbrs v st.2.1.2.2, fun N ℓ hR' hDm hℓ => ?_⟩
  have hPH : P.H = H := by rw [hP]
  have hround' : (phVal P.H P.H + 1) * T ≤ CC * logN n ^ cc * D * e := by rw [hPH]; exact hround
  have hne0 : ((⟨0, by omega⟩ : Fin n)) ≠ ⟨1, by omega⟩ := by simp [Fin.ext_iff]
  have hne : ∀ v, ∃ u, N.G.Adj v u := noIso_of_diam hDm hne0
  have hc : N.toRot.Connected := connected_of_diam hDm hne0
  have hG : N.G.Connected := by
    have hn' : Nonempty (Fin n) := ⟨r⟩
    exact { preconnected := fun u v => by
              obtain ⟨p, -⟩ := hDm u v
              exact ⟨p⟩ }
  have hdist : ∀ v, N.G.dist r v ≤ h := fun v => by
    rw [hh]
    obtain ⟨p, hp⟩ := hDm r v
    exact le_min ((SimpleGraph.dist_le p).trans hp) (dist_lt_n N hG r v).le
  have hAgg : AggSpec N (Aa.widen hw1) outa Ta sA kA b := fun inp hv v x hx κ => by
    rw [run_widen, hTa]
    exact hAa N inp hv v x hx κ
  have hid : ∀ d : N.G.Dart, idL (Af.widen hw2) outf Tf N d = outf d.fst (Af.run N.G N.rotList Tf d.fst) d.snd :=
    fun d => by
      unfold idL
      rw [run_widen]
  have hfaces : ∀ d d' : N.G.Dart, idL (Af.widen hw2) outf Tf N d = idL (Af.widen hw2) outf Tf N d' ↔
      N.toRot.faceOf d = N.toRot.faceOf d' := fun d d' => by
    rw [hid, hid, hTf]
    exact (hFf N hR' hDm d d').1
  have hidb : ∀ d, idL (Af.widen hw2) outf Tf N d < 2 ^ f := fun d => by
    rw [hid, hTf, hf]
    exact (hFf N hR' hDm d d).2
  obtain ⟨hcn, hce⟩ := cU_acc (H := H) he1 hU
  have key := labels_memL (Aa.widen hw1) (Af.widen hw2) outa outf Ta Tf T P W r N ℓ
    (e := e) (C := Cr) (Cl := Cl) (cl := cl) (B₀ := B₀) (f := f) (k₀ := logN n + 1) hNum hC
    (by rw [hP]; exact hq) (by rw [hP]; exact hU1) (by rw [hP]; show 1 ≤ s; omega) (by omega)
    (by rw [hP]; show Cr * (2 + H * (2 + 4 * h) + 1) ^ 6 ≤ s; omega)
    (by rw [hP]; show 2 * (U * (2 * n * n) * Wt) ≤ B₀; omega)
    (by rw [hP]; exact hcn) (by rw [hP]; exact hLb) (by rw [hP]; exact hWb) (by rw [hP]; exact hce)
    (by rw [hP]; exact hH) (by
      have hnX : n + 2 < 2 ^ logN n := Nat.lt_pow_succ_log_self (by norm_num) _
      rw [pow_succ]
      omega)
    (by omega) (by omega) (by omega) hAgg hfaces hidb (by omega) hG hne hR' hc hdist (by rw [hWt]; exact hℓ)
  refine (congrArg (LabelsOK N ℓ e _ _ _) (funext fun v => ?_)).mpr key
  obtain ⟨h1, h2⟩ := run_finalAlg (Aa.widen hw1) (Af.widen hw2) outa outf Ta (Tr₀ + 1) Tf T (phVal P.H P.H + 1) P W r hBB
    hT0 N ℓ hround' v
  show outL P W r _ v _ = _
  rw [h1, h2]
  rfl

/-- **Exact shortest paths** in `Õ(D)` rounds, from the realization of metrics, distance labels, the names of the faces,
the aggregation primitive and the smoothing. -/
theorem exactSssp_of_boxes {Cr Cl cl : ℕ} (hC : RealizationBox Cr) (hL : DistanceLabelBox Cl cl) (hF : FaceIdBox)
    (hA : AggBox) (hS : SmoothingBox) : ExactSsspBound :=
  exactSsspBound (labelHypothesis_of_boxes hC hL hF hA) hA hS

/-- **Negative weights and maximum flow** with the factor `(log n)^c`, from the same results and a reduction with this
factor. -/
theorem negFlow_polylog_of_boxes (c : ℕ) {Cr Cl cl : ℕ} (hC : RealizationBox Cr) (hL : DistanceLabelBox Cl cl)
    (hF : FaceIdBox) (hA : AggBox) (hS : SmoothingBox) (hR : NegReduction (tauPolylog c)) :
    NegSsspBound (tauPolylog c) ∧ MaxFlowBound (tauPolylog c) :=
  negFlow_polylog c (labelHypothesis_of_boxes hC hL hF hA) hA hS hR

/-- **Negative weights and maximum flow** with the factor `(log n)^(C √log n)`, from the same results and a reduction
with this factor. -/
theorem negFlow_subpoly_of_boxes (C : ℕ) {Cr Cl cl : ℕ} (hC : RealizationBox Cr) (hL : DistanceLabelBox Cl cl)
    (hF : FaceIdBox) (hA : AggBox) (hS : SmoothingBox) (hR : NegReduction (tauSubpoly C)) :
    NegSsspBound (tauSubpoly C) ∧ MaxFlowBound (tauSubpoly (12 * C)) :=
  negFlow_subpoly C (labelHypothesis_of_boxes hC hL hF hA) hA hS hR

end Final

end SsspFlow.Congest
