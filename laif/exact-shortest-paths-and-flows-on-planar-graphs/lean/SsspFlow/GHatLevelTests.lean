import SsspFlow.GHatPieceAll
import SsspFlow.GHatLevelMasks
import SsspFlow.GHatCornerId
import SsspFlow.GHatStepLocal

/-!
# The tests of the new corners of a level, as one algorithm

Every node holds its tests `stepLoc` of the corners of the darts at it, the two bits of the corners of
the darts into it, and whether the corners of the darts at it lie at a vertex of the cut path. One
exchange of six bits over every edge tells both ends of each dart whether it is a dart of a step, and
gives the tail of a dart the first bit of the corners of the dart. Two runs on the pieces then tell
every corner whether its piece holds a dart of a step at the cut path, and whether it holds the
reverse corner of such a dart.

* `RData.cornerPiece_iff`: the output of a run on the pieces at the copy of a corner is `0` exactly when
  a corner of its piece has the property.
* `RData.levelTests_local`: one algorithm of the message model gives each node the tests of the corners
  of the darts into it, and the bits of the new incised darts from it.
-/

set_option autoImplicit false

namespace SsspFlow

open FourColor SsspFlow.Congest
open scoped ENNReal

namespace RotSystem

namespace RData

variable {n : ℕ} {N : Net (Fin n)} (S : N.toRot.RData) (hN : ∀ u, ∃ w, N.G.Adj u w)

/-- **A run on the pieces, at the copy of a corner.** For values `g` that are `0` exactly at the
corners with a property `p` and `⊤` elsewhere, and a run on the pieces with `1 ≤ M`, the output at
the copy of a corner `c` is `0` exactly when a corner of the piece of `c` has the property. -/
theorem cornerPiece_iff {M : ℕ} (hM : 1 ≤ M) (out : Fin (n * (n * 21)) → ℕ∞)
    (g : N.G.Dart × Bool → ℕ∞) (p : N.G.Dart × Bool → Prop)
    (hg : ∀ z, g z = 0 ↔ p z) (hg' : ∀ z, g z = 0 ∨ g z = ⊤)
    (hpc : ∀ v, min (out ((S.levelPad hN).ι (.inl v)) : ℝ≥0∞) M =
      min (⨅ u, ⨅ (_ : Relation.ReflTransGen S.ER (S.vcopy u) (S.vcopy v)),
        ((S.copyVal g (S.vcopy u) : ℕ∞) : ℝ≥0∞)) M) (c : N.G.Dart × Bool) :
    out ((S.levelPad hN).ι (.inl (S.endV c))) = 0 ↔ ∃ y, S.pieceAt y = S.pieceAt c ∧ p y := by
  have hM' : (0 : ℝ≥0∞) < M := by exact_mod_cast hM
  have h0 : ∀ x : ℕ∞, x = 0 ↔ min (x : ℝ≥0∞) M = 0 := fun x => by
    rw [min_eq_iff]
    constructor
    · intro h; exact .inl ⟨by rw [h]; simp, by rw [h]; simp⟩
    · rintro (⟨h, -⟩ | ⟨h, -⟩)
      · exact_mod_cast h
      · exact absurd h hM'.ne'
  rw [h0, hpc (S.endV c), S.cast_erMin, ← h0, ← S.pieceMin_eq g ⟨S.vcopy (S.endV c), S.endV_end c⟩,
    S.pieceOf_endV c]
  constructor
  · intro h
    by_contra hn
    have : (⨅ z, ⨅ (_ : S.pieceAt z = S.pieceAt c), g z) = ⊤ :=
      iInf_eq_top.2 fun z => iInf_eq_top.2 fun hz =>
        (hg' z).resolve_left fun h0 => hn ⟨z, hz, (hg z).1 h0⟩
    rw [this] at h
    exact ENat.top_ne_zero h
  · rintro ⟨z, hz, hp⟩
    exact le_antisymm (iInf_le_of_le z (iInf_le_of_le hz (le_of_eq ((hg z).2 hp)))) zero_le

end RData

/-- The inputs of the tests at a node: its input of the level, its tests `stepLoc` of corners, the two
bits of the corners of the darts into it, and the cut bits of the corners of the darts from it and into
it. -/
abbrev TestIn (n : ℕ) := LevelIn n × (Fin n × Fin n × Bool → Bool) × (Fin n → Bool → Bool × Bool) ×
  ((Fin n → Bool → Bool) × (Fin n → Bool → Bool))

/-- The six bits from `w` to `u`: its tests of the four corners of the darts between them and the
first bits of the corners of the dart from `u` to `w`. -/
def testMsg {n : ℕ} (w : Fin n) (j : TestIn n) (u : Fin n) : ℕ :=
  bit2 (j.2.1 (w, u, false)) (bit2 (j.2.1 (w, u, true)) (bit2 (j.2.1 (u, w, false))
    (bit2 (j.2.1 (u, w, true)) (bit2 (j.2.2.1 u false).1 (bit2 (j.2.2.1 u true).1 0)))))

theorem testMsg_lt {n : ℕ} (w : Fin n) (j : TestIn n) (u : Fin n) : testMsg w j u < 2 ^ 6 :=
  bit2_lt (k := 5) (bit2_lt (k := 4) (bit2_lt (k := 3) (bit2_lt (k := 2) (bit2_lt (k := 1)
    (bit2_lt (k := 0) (by norm_num))))))

theorem dbit_msg0 {n : ℕ} (w : Fin n) (j : TestIn n) (u : Fin n) (β : Bool) :
    dbit (testMsg w j u) β.toNat = j.2.1 (w, u, β) := by
  cases β <;> simp [testMsg]

theorem dbit_msg2 {n : ℕ} (w : Fin n) (j : TestIn n) (u : Fin n) (β : Bool) :
    dbit (testMsg w j u) (β.toNat + 2) = j.2.1 (u, w, β) := by
  cases β <;> simp [testMsg]

theorem dbit_msg4 {n : ℕ} (w : Fin n) (j : TestIn n) (u : Fin n) (β : Bool) :
    dbit (testMsg w j u) (β.toNat + 4) = (j.2.2.1 u β).1 := by
  cases β <;> simp [testMsg]

/-- The bit `i` received from `u`. -/
def rb {n : ℕ} (m : Fin n → Option ℕ) (u : Fin n) (i : ℕ) : Bool := dbit ((m u).getD 0) i

/-- Whether the corner of the dart from `w` to `u` with bit `β` is a corner of a dart of a step. -/
def sdO {n : ℕ} (w : Fin n) (j : TestIn n) (m : Fin n → Option ℕ) (u : Fin n) (β : Bool) : Bool :=
  j.2.1 (w, u, β) || rb m u (β.toNat + 2)

/-- Whether the corner of the dart from `u` to `w` with bit `β` is a corner of a dart of a step. -/
def sdI {n : ℕ} (w : Fin n) (j : TestIn n) (m : Fin n → Option ℕ) (u : Fin n) (β : Bool) : Bool :=
  j.2.1 (u, w, β) || rb m u β.toNat

/-- The first bit of the corner of the dart from `w` to `u` with bit `β`, received from `u`. -/
def gR {n : ℕ} (m : Fin n → Option ℕ) (u : Fin n) (β : Bool) : Bool := rb m u (β.toNat + 4)

/-- The values of the first run on the pieces at the corners of the darts from and into `w`. -/
noncomputable def voA {n : ℕ} (w : Fin n) (j : TestIn n × (Fin n → Option ℕ)) (u : Fin n) (b : Bool) : ℕ∞ :=
  if (sdO w j.1 j.2 u b && j.1.2.2.2.1 u b) = true then 0 else ⊤

noncomputable def viA {n : ℕ} (w : Fin n) (j : TestIn n × (Fin n → Option ℕ)) (u : Fin n) (b : Bool) : ℕ∞ :=
  if (sdI w j.1 j.2 u b && j.1.2.2.2.2 u b) = true then 0 else ⊤

/-- The values of the second run on the pieces: the reverse corner is a corner of a dart of a step. -/
noncomputable def voB {n : ℕ} (w : Fin n) (j : TestIn n × (Fin n → Option ℕ)) (u : Fin n) (b : Bool) : ℕ∞ :=
  if (sdI w j.1 j.2 u (!b) && j.1.2.2.2.1 u b) = true then 0 else ⊤

noncomputable def viB {n : ℕ} (w : Fin n) (j : TestIn n × (Fin n → Option ℕ)) (u : Fin n) (b : Bool) : ℕ∞ :=
  if (sdO w j.1 j.2 u (!b) && j.1.2.2.2.2 u b) = true then 0 else ⊤

namespace RData

open Cslib.Congest.Algorithm in
/-- **The tests of the new corners of a level, as one algorithm.** For every `K`, `n` and `D`, one
algorithm of the message model, with as many bits per message as a run on the pieces, starts from the
inputs of the tests at every node. Let a predicate `SD` on corners hold exactly when the test of the
tail or of the head of the dart holds, let the two bits of each corner be given at the head of its
dart, and the cut bits at both ends. After `1 + 2 T` rounds, with `T` the rounds of a run on the
pieces, the head of each dart `d` holds for each corner `(d, b)` the first parts of the tests `lvNewA`
and `lvNewB`, whether its piece holds a corner with `SD` at the cut path and whether it holds the
reverse of such a corner, and whether `(d, b)` is a digon corner of a dart with `SD`; the tail of
`d` holds whether `d` is a new incised dart. -/
theorem levelTests_local (hE : ExactSsspBound) (K : ℕ) : ∃ C c : ℕ, ∀ n D : ℕ,
    ∃ (σ : Type) (A : Cslib.Congest.Algorithm (Fin n) (TestIn n) σ
      (4 * (C * logN (n * (n * 21)) ^ c) + (3 * (K * logN (n * (n * 21)) + 1) + 5)))
      (fA fB pA pB dg : Fin n → σ → Fin n → Bool → Bool) (F : Fin n → σ → Fin n → Bool),
    ∀ (N : Net (Fin n)) (S : N.toRot.RData) (hN : ∀ u, ∃ w, N.G.Adj u w) (lam : S.Tok → ℕ) (M : ℕ)
      (u₀ : S.hRot.Vertex) (sdl : Fin n → Fin n × Fin n × Bool → Bool) (gte : Fin n → Fin n → Bool → Bool × Bool)
      (cfo cfi : Fin n → Fin n → Bool → Bool) (SD : N.G.Dart × Bool → Prop) (gA gB : N.G.Dart × Bool → Bool)
      (cutc : N.G.Dart × Bool → Prop),
      N.toRot.Planar → N.toRot.Connected → S.NoConflict → S.cut.card ≤ 3 → N.DiamLE D →
      (∀ x, lam x ≤ (n * (n * 21) + 2) ^ K) → 1 ≤ M → M ≤ (n * (n * 21) + 2) ^ K →
      (∀ z, SD z ↔ ∃ w, (w = z.1.fst ∨ w = z.1.snd) ∧ sdl w (z.1.fst, z.1.snd, z.2) = true) →
      (∀ (d : N.G.Dart) b, gte d.snd d.fst b = (gA (d, b), gB (d, b))) →
      (∀ (d : N.G.Dart) b, (cfo d.fst d.snd b = true ↔ cutc (d, b)) ∧ (cfi d.snd d.fst b = true ↔ cutc (d, b))) →
      let st := A.run N.G (fun w => (S.levelIn hN lam M u₀ w, sdl w, gte w, (cfo w, cfi w)))
        (1 + ((1 + (1 + C * logN (n * (n * 21)) ^ c * (12 * D + 16))) +
          (1 + (1 + C * logN (n * (n * 21)) ^ c * (12 * D + 16)))))
      ∀ (d : N.G.Dart) (b : Bool),
        (fA d.snd (st d.snd) d.fst b = true ↔
          b = false ∧ ∃ β, SD (N.toRot.dual.rev d, β) ∧ gA (N.toRot.dual.rev d, β) = true) ∧
        (fB d.snd (st d.snd) d.fst b = true ↔ b = false ∧ ∃ β, SD (d, β) ∧ gB (d, β) = true) ∧
        (pA d.snd (st d.snd) d.fst b = true ↔ ∃ y, S.pieceAt y = S.pieceAt (d, b) ∧ SD y ∧ cutc y) ∧
        (pB d.snd (st d.snd) d.fst b = true ↔
          ∃ y, S.pieceAt y = S.pieceAt (d, b) ∧ SD (N.toRot.dual.double.rev y) ∧ cutc y) ∧
        (dg d.snd (st d.snd) d.fst b = true ↔ b = false ∧ ∃ β, SD (d, β) ∨ SD (N.toRot.dual.rev d, β)) ∧
        (F d.fst (st d.fst) d.snd = true ↔ ∃ β, SD (d, β) ∨ SD (N.toRot.dual.rev d, β)) := by
  classical
  obtain ⟨C, c, hC⟩ := levelPieceVal_all hE K
  refine ⟨C, c, fun n D => ?_⟩
  set Bw := 4 * (C * logN (n * (n * 21)) ^ c) + (3 * (K * logN (n * (n * 21)) + 1) + 5)
  set Tp := 1 + (1 + C * logN (n * (n * 21)) ^ c * (12 * D + 16))
  obtain ⟨σ, A, out, hA⟩ := hC n D
  let Aex := (exchTo (Fin n) Bw).keep (fun w (j : TestIn n) => testMsg w j)
  let f₁ : Fin n → TestIn n × ((Fin n → ℕ) × (Fin n → Option ℕ)) → TestIn n × (Fin n → Option ℕ) :=
    fun _ s => (s.1, s.2.2)
  let PA := A.keep (fun w (j : TestIn n × (Fin n → Option ℕ)) => (j.1.1, (voA w j, viA w j)))
  let PB := A.keep (fun w (j : (TestIn n × (Fin n → Option ℕ)) × σ) => (j.1.1.1, (voB w j.1, viB w j.1)))
  let fin : Fin n → ((ℕ × (TestIn n × ((Fin n → ℕ) × (Fin n → Option ℕ)))) ⊕
      ((ℕ × ((TestIn n × (Fin n → Option ℕ)) × σ)) ⊕ (((TestIn n × (Fin n → Option ℕ)) × σ) × σ))) →
      Option (((TestIn n × (Fin n → Option ℕ)) × σ) × σ) :=
    fun _ s => match s with
      | .inr (.inr x) => some x
      | _ => none
  refine ⟨_, Aex.seq 1 f₁ (PA.seq Tp (fun _ s => s) PB),
    fun w s u b => match fin w s with
      | some x => !b && ((sdO w x.1.1.1 x.1.1.2 u false && gR x.1.1.2 u false) ||
          (sdO w x.1.1.1 x.1.1.2 u true && gR x.1.1.2 u true))
      | none => false,
    fun w s u b => match fin w s with
      | some x => !b && ((sdI w x.1.1.1 x.1.1.2 u false && (x.1.1.1.2.2.1 u false).2) ||
          (sdI w x.1.1.1 x.1.1.2 u true && (x.1.1.1.2.2.1 u true).2))
      | none => false,
    fun w s u b => match fin w s with
      | some x => decide (out (idEquiv (cornerName x.1.1.1.1.rot x.1.1.1.1.own w u b)) x.1.2 = 0)
      | none => false,
    fun w s u b => match fin w s with
      | some x => decide (out (idEquiv (cornerName x.1.1.1.1.rot x.1.1.1.1.own w u b)) x.2 = 0)
      | none => false,
    fun w s u b => match fin w s with
      | some x => !b && (sdI w x.1.1.1 x.1.1.2 u false || sdI w x.1.1.1 x.1.1.2 u true ||
          sdO w x.1.1.1 x.1.1.2 u false || sdO w x.1.1.1 x.1.1.2 u true)
      | none => false,
    fun w s u => match fin w s with
      | some x => sdO w x.1.1.1 x.1.1.2 u false || sdO w x.1.1.1 x.1.1.2 u true ||
          sdI w x.1.1.1 x.1.1.2 u false || sdI w x.1.1.1 x.1.1.2 u true
      | none => false, ?_⟩
  intro N S hN lam M u₀ sdl gte cfo cfi SD gA gB cutc hP hc hS hcut hD hlam hM1 hM hSD hgte hcf
  intro st d b
  set inp : Fin n → TestIn n := fun w => (S.levelIn hN lam M u₀ w, sdl w, gte w, (cfo w, cfi w))
  set recv : Fin n → Fin n → Option ℕ := fun w u => if N.G.Adj u w then some (testMsg u (inp u) w) else none
  have hmsg : ∀ u w, testMsg u (inp u) w < 2 ^ Bw := fun u w =>
    (testMsg_lt u (inp u) w).trans_le (Nat.pow_le_pow_right (by norm_num) (by omega))
  have hex : (fun w => f₁ w (Aex.run N.G inp 1 w)) = fun w => (inp w, recv w) := by
    funext w
    show f₁ w ((exchTo (Fin n) Bw).keep (fun w (j : TestIn n) => testMsg w j) |>.run N.G inp 1 w) = _
    rw [run_keep]
    show (inp w, ((exchTo (Fin n) Bw).run N.G _ 1 w).2) = _
    rw [run_exchTo N.G _ hmsg]
  set sA : Fin n → σ := fun w => A.run N.G (fun v => ((inp v).1, (voA v (inp v, recv v), viA v (inp v, recv v))))
    Tp w
  set sB : Fin n → σ := fun w => A.run N.G (fun v => ((inp v).1, (voB v (inp v, recv v), viB v (inp v, recv v))))
    Tp w
  have hrun : ∀ w, fin w (st w) = some (((inp w, recv w), sA w), sB w) := by
    intro w
    show fin w ((Aex.seq 1 f₁ (PA.seq Tp (fun _ s => s) PB)).run N.G inp (1 + (Tp + Tp)) w) = _
    rw [run_seq]
    dsimp only
    rw [hex, run_seq]
    dsimp only
    rw [run_keep]
    dsimp only
    rw [run_keep]
  -- the bits at both ends
  have hsdO : ∀ (e : N.G.Dart) β, sdO e.fst (inp e.fst) (recv e.fst) e.snd β = decide (SD (e, β)) := by
    intro e β
    have hadj : N.G.Adj e.snd e.fst := e.adj.symm
    unfold sdO rb
    simp only [recv, hadj, ↓reduceIte, Option.getD_some, dbit_msg2]
    rw [Bool.eq_iff_iff, Bool.or_eq_true, decide_eq_true_iff, hSD]
    constructor
    · rintro (h | h)
      · exact ⟨e.fst, .inl rfl, h⟩
      · exact ⟨e.snd, .inr rfl, h⟩
    · rintro ⟨w, rfl | rfl, h⟩
      · exact .inl h
      · exact .inr h
  have hsdI : ∀ (e : N.G.Dart) β, sdI e.snd (inp e.snd) (recv e.snd) e.fst β = decide (SD (e, β)) := by
    intro e β
    have hadj : N.G.Adj e.fst e.snd := e.adj
    unfold sdI rb
    simp only [recv, hadj, ↓reduceIte, Option.getD_some, dbit_msg0]
    rw [Bool.eq_iff_iff, Bool.or_eq_true, decide_eq_true_iff, hSD]
    constructor
    · rintro (h | h)
      · exact ⟨e.snd, .inr rfl, h⟩
      · exact ⟨e.fst, .inl rfl, h⟩
    · rintro ⟨w, rfl | rfl, h⟩
      · exact .inr h
      · exact .inl h
  have hgR : ∀ (e : N.G.Dart) β, gR (recv e.fst) e.snd β = gA (e, β) := by
    intro e β
    have hadj : N.G.Adj e.snd e.fst := e.adj.symm
    unfold gR rb
    simp only [recv, hadj, ↓reduceIte, Option.getD_some, dbit_msg4]
    show (gte e.snd e.fst β).1 = _
    rw [hgte]
  have hW : 1 ≤ (n * (n * 21) + 2) ^ K := Nat.one_le_pow _ _ (by omega)
  -- the two runs on the pieces
  set gAv : N.G.Dart × Bool → ℕ∞ := fun z => if SD z ∧ cutc z then 0 else ⊤
  set gBv : N.G.Dart × Bool → ℕ∞ := fun z => if SD (N.toRot.dual.double.rev z) ∧ cutc z then 0 else ⊤
  have hpA := hA N S hN lam M u₀ gAv (fun w => voA w (inp w, recv w)) (fun w => viA w (inp w, recv w))
    hP hc hS hcut hD hlam hM1 hM (fun z => by unfold gAv; split_ifs <;> simp)
    (fun e β => by
      show voA e.fst (inp e.fst, recv e.fst) e.snd β = _
      unfold voA gAv
      rw [hsdO e β]
      exact if_congr (by rw [Bool.and_eq_true, decide_eq_true_iff]; exact and_congr Iff.rfl (hcf e β).1) rfl rfl)
    (fun e β => by
      show viA e.snd (inp e.snd, recv e.snd) e.fst β = _
      unfold viA gAv
      rw [hsdI e β]
      exact if_congr (by rw [Bool.and_eq_true, decide_eq_true_iff]; exact and_congr Iff.rfl (hcf e β).2) rfl rfl)
  have hpB := hA N S hN lam M u₀ gBv (fun w => voB w (inp w, recv w)) (fun w => viB w (inp w, recv w))
    hP hc hS hcut hD hlam hM1 hM (fun z => by unfold gBv; split_ifs <;> simp)
    (fun e β => by
      show voB e.fst (inp e.fst, recv e.fst) e.snd β = _
      unfold voB gBv
      rw [show sdI e.fst (inp e.fst) (recv e.fst) e.snd (!β) = decide (SD (e.symm, !β)) from hsdI e.symm (!β)]
      exact if_congr (by rw [Bool.and_eq_true, decide_eq_true_iff]; exact and_congr Iff.rfl (hcf e β).1) rfl rfl)
    (fun e β => by
      show viB e.snd (inp e.snd, recv e.snd) e.fst β = _
      unfold viB gBv
      rw [show sdO e.snd (inp e.snd) (recv e.snd) e.fst (!β) = decide (SD (e.symm, !β)) from hsdO e.symm (!β)]
      exact if_congr (by rw [Bool.and_eq_true, decide_eq_true_iff]; exact and_congr Iff.rfl (hcf e β).2) rfl rfl)
  have hcn : idEquiv (cornerName (inp d.snd).1.rot (inp d.snd).1.own d.snd d.fst b) =
      (S.levelPad hN).ι (.inl (S.endV (d, b))) := S.cornerName_eq hN d b
  have hho : d.snd = hostOf ((S.levelPad hN).ι (.inl (S.endV (d, b)))) := (S.hostOf_endV hN (d, b)).symm
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [hrun]
    rw [Bool.and_eq_true, Bool.not_eq_true', Bool.or_eq_true, Bool.and_eq_true, Bool.and_eq_true]
    show (b = false ∧ ((sdO d.symm.fst (inp d.symm.fst) (recv d.symm.fst) d.symm.snd false = true ∧
        gR (recv d.symm.fst) d.symm.snd false = true) ∨ (sdO d.symm.fst (inp d.symm.fst) (recv d.symm.fst)
        d.symm.snd true = true ∧ gR (recv d.symm.fst) d.symm.snd true = true))) ↔ _
    simp only [hsdO, hgR, decide_eq_true_eq]
    refine and_congr_right fun _ => ⟨?_, ?_⟩
    · rintro (h | h)
      · exact ⟨false, h⟩
      · exact ⟨true, h⟩
    · rintro ⟨β, h⟩
      cases β
      · exact .inl h
      · exact .inr h
  · simp only [hrun]
    rw [Bool.and_eq_true, Bool.not_eq_true', Bool.or_eq_true, Bool.and_eq_true, Bool.and_eq_true]
    simp only [hsdI, decide_eq_true_eq]
    show (b = false ∧ ((SD (d, false) ∧ (gte d.snd d.fst false).2 = true) ∨
      (SD (d, true) ∧ (gte d.snd d.fst true).2 = true))) ↔ _
    simp only [hgte]
    refine and_congr_right fun _ => ⟨?_, ?_⟩
    · rintro (h | h)
      · exact ⟨false, h⟩
      · exact ⟨true, h⟩
    · rintro ⟨β, h⟩
      cases β
      · exact .inl h
      · exact .inr h
  · simp only [hrun, decide_eq_true_eq]
    rw [hcn, hho]
    exact S.cornerPiece_iff hN hM1 (fun a => out a (sA (hostOf a))) gAv (fun z => SD z ∧ cutc z)
      (fun z => by unfold gAv; split_ifs with h <;> simp [h]) (fun z => by unfold gAv; split_ifs <;> simp)
      hpA (d, b)
  · simp only [hrun, decide_eq_true_eq]
    rw [hcn, hho]
    exact S.cornerPiece_iff hN hM1 (fun a => out a (sB (hostOf a))) gBv
      (fun z => SD (N.toRot.dual.double.rev z) ∧ cutc z)
      (fun z => by unfold gBv; split_ifs with h <;> simp [h]) (fun z => by unfold gBv; split_ifs <;> simp)
      hpB (d, b)
  · simp only [hrun]
    rw [Bool.and_eq_true, Bool.not_eq_true', Bool.or_eq_true, Bool.or_eq_true, Bool.or_eq_true]
    show (b = false ∧ (((sdI d.snd (inp d.snd) (recv d.snd) d.fst false = true ∨
        sdI d.snd (inp d.snd) (recv d.snd) d.fst true = true) ∨
        sdO d.symm.fst (inp d.symm.fst) (recv d.symm.fst) d.symm.snd false = true) ∨
        sdO d.symm.fst (inp d.symm.fst) (recv d.symm.fst) d.symm.snd true = true)) ↔ _
    simp only [hsdI, hsdO, decide_eq_true_eq]
    refine and_congr_right fun _ => ⟨?_, ?_⟩
    · rintro (((h | h) | h) | h)
      · exact ⟨false, .inl h⟩
      · exact ⟨true, .inl h⟩
      · exact ⟨false, .inr h⟩
      · exact ⟨true, .inr h⟩
    · rintro ⟨β, h | h⟩ <;> cases β
      · exact .inl (.inl (.inl h))
      · exact .inl (.inl (.inr h))
      · exact .inl (.inr h)
      · exact .inr h
  · simp only [hrun]
    rw [Bool.or_eq_true, Bool.or_eq_true, Bool.or_eq_true]
    show (((sdO d.fst (inp d.fst) (recv d.fst) d.snd false = true ∨
        sdO d.fst (inp d.fst) (recv d.fst) d.snd true = true) ∨
        sdI d.symm.snd (inp d.symm.snd) (recv d.symm.snd) d.symm.fst false = true) ∨
        sdI d.symm.snd (inp d.symm.snd) (recv d.symm.snd) d.symm.fst true = true) ↔ _
    simp only [hsdI, hsdO, decide_eq_true_eq]
    constructor
    · rintro (((h | h) | h) | h)
      · exact ⟨false, .inl h⟩
      · exact ⟨true, .inl h⟩
      · exact ⟨false, .inr h⟩
      · exact ⟨true, .inr h⟩
    · rintro ⟨β, h | h⟩ <;> cases β
      · exact .inl (.inl (.inl h))
      · exact .inl (.inl (.inr h))
      · exact .inl (.inr h)
      · exact .inr h

end RData

end RotSystem

end SsspFlow
