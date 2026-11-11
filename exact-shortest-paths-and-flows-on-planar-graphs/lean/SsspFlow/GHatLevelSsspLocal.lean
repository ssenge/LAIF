import SsspFlow.GHatLevelLen
import SsspFlow.GHatLevelLocal

/-!
# The distances of a level from local inputs

Every node `w` of `N` starts with its own name, its rotation list, the records and the values `λ` of
the darts at `w`, the bound `M` and the identifier of the source copy (`LevelIn`, `RData.levelIn`).
In one round it sends each neighbour the record and the values `λ` of the dart to it
(`Algorithm.exchTo`). From then on it knows the rotation lists and the inputs of all its identifiers
in the network of a level (`RData.levelNet_rotList_raw`, `RData.levelNet_oracleIn_raw`), and the nodes
simulate the shortest paths of the level (`RData.levelSssp_sim`).

* `RData.levelSssp_local`: assuming the Exact SSSP bound, one algorithm of the message model, fixed
  before the network, computes at every copy of a level its distance in `Ĝ_ℓ` from the source copy
  in `C log^c n · (12 D + 16) + 1` rounds, from these local inputs only.
-/

set_option autoImplicit false

namespace SsspFlow

open FourColor SsspFlow.Congest
open scoped ENNReal

namespace RotSystem

/-- The input of a node for a level. -/
structure LevelIn (n : ℕ) where
  /-- The name of the node. -/
  me : Fin n
  /-- Its rotation list. -/
  rot : List (Fin n)
  /-- The records of the darts at the node. -/
  own : Fin n → DInfo
  /-- The values `λ` of the tokens on the darts at the node. -/
  lamO : Fin n → Lab → ℕ
  /-- The bound `M`. -/
  bnd : ℕ
  /-- The identifier of the source copy. -/
  src : Fin (n * (n * 21))

namespace LevelIn

variable {n : ℕ}

/-- The number that a node sends to its neighbour `u`. -/
def msg (b : ℕ) (j : LevelIn n) (u : Fin n) : ℕ :=
  DInfo.pack b (j.own u) (j.lamO u .zero) (j.lamO u .one) (j.lamO u .two)

/-- The record of the dart from `u`, from the received numbers. -/
def inn (b : ℕ) (r : Fin n → Option ℕ) (u : Fin n) : DInfo :=
  match r u with
  | some c => (DInfo.unpack b c).1
  | none => default

/-- The values `λ` on the dart from `u`, from the received numbers. -/
def lamI (b : ℕ) (r : Fin n → Option ℕ) (u : Fin n) (l : Lab) : ℕ :=
  match r u with
  | some c =>
    match l with
    | .zero => (DInfo.unpack b c).2.1
    | .one => (DInfo.unpack b c).2.2.1
    | .two => (DInfo.unpack b c).2.2.2
  | none => 0

/-- The place of an identifier. -/
def qOf (a : Fin (n * (n * 21))) : Fin n × Fin 21 :=
  ((RData.idEquiv.symm a).2.1, (RData.idEquiv.symm a).2.2)

/-- The raw rotation list at an identifier, from the data of a node after the exchange. -/
def lists (b : ℕ) (d : LevelIn n × (Fin n → Option ℕ)) (a : Fin (n * (n * 21))) :
    List (Fin (n * (n * 21))) :=
  rawAt d.1.rot d.1.own (inn b d.2) d.1.me (qOf a)

/-- The view of a node: one end is its own and the other is in the list of that end. -/
def view (b : ℕ) (d : LevelIn n × (Fin n → Option ℕ)) (x y : Fin (n * (n * 21))) : Prop :=
  (RData.hostOf x = d.1.me ∧ y ∈ lists b d x) ∨ (RData.hostOf y = d.1.me ∧ x ∈ lists b d y)

/-- The input of an identifier hosted at `w`. -/
def vin (b : ℕ) (w : Fin n) (d : LevelIn n × (Fin n → Option ℕ)) (a : Fin (n * (n * 21))) :
    OracleIn (Fin (n * (n * 21))) :=
  rawIn d.1.rot d.1.own (inn b d.2) d.1.lamO (lamI b d.2) d.1.bnd d.1.src w (qOf a)

end LevelIn

namespace RData

variable {n : ℕ} {N : Net (Fin n)} (S : N.toRot.RData) (hN : ∀ u, ∃ w, N.G.Adj u w)
  (lam : S.Tok → ℕ) (M : ℕ)

/-- The true input of a node for a level with source copy `u₀`. -/
noncomputable def levelIn (u₀ : S.hRot.Vertex) (w : Fin n) : LevelIn n :=
  ⟨w, N.rotList w, S.dinfoAt w, S.lamAt lam w, M, (S.levelPad hN).ι (.inl u₀)⟩

/-- The numbers a node receives in the exchange. -/
noncomputable def levelRecv (b : ℕ) (u₀ : S.hRot.Vertex) (w : Fin n) : Fin n → Option ℕ :=
  fun u => if N.G.Adj u w then some ((S.levelIn hN lam M u₀ u).msg b w) else none

theorem lamAt_lt {b : ℕ} (hb : ∀ x, lam x < 2 ^ b) (w u : Fin n) (l : Lab) : S.lamAt lam w u l < 2 ^ b := by
  unfold lamAt
  split_ifs
  · exact hb _
  · exact Nat.two_pow_pos b
  · exact Nat.two_pow_pos b

theorem inn_recv {b : ℕ} (hb : ∀ x, lam x < 2 ^ b) (u₀ : S.hRot.Vertex) (w : Fin n) :
    LevelIn.inn b (S.levelRecv hN lam M b u₀ w) = fun u => S.dinfoAt u w := by
  funext u
  unfold LevelIn.inn levelRecv
  by_cases h : N.G.Adj u w
  · rw [ite_eq_left_of_eq_true _ _ (eq_true h)]
    simp only [LevelIn.msg, levelIn]
    rw [DInfo.unpack_pack _ (S.lamAt_lt lam hb _ _ _) (S.lamAt_lt lam hb _ _ _)]
  · rw [ite_eq_right_of_eq_false _ _ (eq_false h)]
    unfold dinfoAt
    rw [dite_eq_right_of_eq_false (eq_false h)]

theorem lamI_recv {b : ℕ} (hb : ∀ x, lam x < 2 ^ b) (u₀ : S.hRot.Vertex) (w : Fin n) :
    LevelIn.lamI b (S.levelRecv hN lam M b u₀ w) = fun u => S.lamAt lam u w := by
  funext u l
  unfold LevelIn.lamI levelRecv
  by_cases h : N.G.Adj u w
  · rw [ite_eq_left_of_eq_true _ _ (eq_true h)]
    simp only [LevelIn.msg, levelIn]
    rw [DInfo.unpack_pack _ (S.lamAt_lt lam hb _ _ _) (S.lamAt_lt lam hb _ _ _)]
    cases l <;> rfl
  · rw [ite_eq_right_of_eq_false _ _ (eq_false h)]
    unfold lamAt
    rw [dite_eq_right_of_eq_false (eq_false h)]

/-- After the exchange the nodes hold the lists of the network of a level at their identifiers. -/
theorem lists_recv {b : ℕ} (hb : ∀ x, lam x < 2 ^ b) (u₀ : S.hRot.Vertex) (w : Fin n)
    (a : Fin (n * (n * 21))) (ha : hostOf a = w) :
    LevelIn.lists b (S.levelIn hN lam M u₀ w, S.levelRecv hN lam M b u₀ w) a = (S.levelNet hN).rotList a := by
  rw [S.levelNet_rotList_raw hN a, ha]
  unfold LevelIn.lists
  rw [S.inn_recv hN lam M hb]
  rfl

/-- After the exchange the nodes hold the inputs of their identifiers. -/
theorem vin_recv {b : ℕ} (hb : ∀ x, lam x < 2 ^ b) (u₀ : S.hRot.Vertex) (a : Fin (n * (n * 21))) :
    (S.levelNet hN).oracleIn (S.levelLen hN lam M) (S.levelOff hN u₀) a =
      LevelIn.vin b (hostOf a) (S.levelIn hN lam M u₀ (hostOf a), S.levelRecv hN lam M b u₀ (hostOf a)) a := by
  rw [S.levelNet_oracleIn_raw lam hN M u₀ a]
  unfold LevelIn.vin
  rw [S.inn_recv hN lam M hb, S.lamI_recv hN lam M hb]
  rfl

theorem view_recv {b : ℕ} (hb : ∀ x, lam x < 2 ^ b) (u₀ : S.hRot.Vertex) (w : Fin n)
    (x y : Fin (n * (n * 21))) (hxy : hostOf x = w ∨ hostOf y = w) :
    LevelIn.view b (S.levelIn hN lam M u₀ w, S.levelRecv hN lam M b u₀ w) x y ↔ (S.levelNet hN).G.Adj x y := by
  unfold LevelIn.view
  exact Congest.view_of_lists (S.levelNet hN) hostOf (fun d : LevelIn n × (Fin n → Option ℕ) => d.1.me)
    (LevelIn.lists b)
    (fun w => (S.levelIn hN lam M u₀ w, S.levelRecv hN lam M b u₀ w)) (fun _ => rfl)
    (fun w a ha => S.lists_recv hN lam M hb u₀ w a ha) w x y hxy

theorem lam_lt_pow {K n' : ℕ} {x : ℕ} (hx : x ≤ (n' + 2) ^ K) : x < 2 ^ (K * logN n' + 1) := by
  have hlt : n' + 2 < 2 ^ logN n' := Nat.lt_pow_succ_log_self (by norm_num) _
  calc x ≤ (n' + 2) ^ K := hx
    _ ≤ (2 ^ logN n') ^ K := Nat.pow_le_pow_left hlt.le K
    _ = 2 ^ (K * logN n') := by rw [← pow_mul, mul_comm]
    _ < 2 ^ (K * logN n' + 1) := Nat.pow_lt_pow_right (by norm_num) (by omega)

open Cslib.Congest.Algorithm in
/-- **The distances of a level from local inputs.** Assuming the Exact SSSP bound, one algorithm of
the message model on `N`, fixed before the network, with messages of
`4 C log^c n' + 3 (K log n' + 1) + 5` bits for `n' = 21 n²`, starts from the inputs `levelIn` and
after `C log^c n' · (12 D + 16) + 1` rounds holds at every copy of a level its distance in `Ĝ_ℓ` from
the source copy, for lengths `λ` and `M` up to `(n' + 2)^K`. -/
theorem levelSssp_local (hE : ExactSsspBound) (K : ℕ) : ∃ C c : ℕ, ∀ n D : ℕ,
    ∃ (σ : Type) (A : Cslib.Congest.Algorithm (Fin n) (LevelIn n) σ
      (4 * (C * logN (n * (n * 21)) ^ c) + (3 * (K * logN (n * (n * 21)) + 1) + 5)))
      (out : Fin (n * (n * 21)) → σ → ℕ∞),
    ∀ (N : Net (Fin n)) (S : N.toRot.RData) (hN : ∀ u, ∃ w, N.G.Adj u w) (lam : S.Tok → ℕ) (M : ℕ)
      (u₀ : S.hRot.Vertex),
      N.toRot.Planar → N.toRot.Connected → S.NoConflict → S.cut.card ≤ 3 → N.DiamLE D →
      (∀ x, lam x ≤ (n * (n * 21) + 2) ^ K) → M ≤ (n * (n * 21) + 2) ^ K →
      ∀ v : S.hRot.Vertex,
        (out ((S.levelPad hN).ι (.inl v))
          (A.run N.G (S.levelIn hN lam M u₀) (1 + C * logN (n * (n * 21)) ^ c * (12 * D + 16))
            (hostOf ((S.levelPad hN).ι (.inl v)))) : ℝ≥0∞) =
          S.arcDist lam M (S.vcopy u₀) (S.vcopy v) := by
  obtain ⟨C, c, hC⟩ := levelSssp_sim hE K
  refine ⟨C, c, fun n D => ?_⟩
  obtain ⟨σ, A, out, hA⟩ := hC n D
  set b := K * logN (n * (n * 21)) + 1
  set Bw := 4 * (C * logN (n * (n * 21)) ^ c) + (3 * b + 5)
  let Aex := (exchTo (Fin n) Bw).keep (fun _ (j : LevelIn n) => j.msg b)
  let f : Fin n → LevelIn n × ((Fin n → ℕ) × (Fin n → Option ℕ)) → LevelIn n × (Fin n → Option ℕ) :=
    fun _ s => (s.1, s.2.2)
  let Asim := (simulateView (k := 4) A hostOf (LevelIn.view b) (LevelIn.vin b)).widen
    (show 4 * (C * logN (n * (n * 21)) ^ c) ≤ Bw by omega)
  refine ⟨_, Aex.seq 1 f Asim, fun a s => match s with
    | .inr s' => (out a (s'.2 a)).1
    | .inl _ => ⊤, ?_⟩
  intro N S hN lam M u₀ hP hc hS hcut hD hlam hM v
  have hb : ∀ x, lam x < 2 ^ b := fun x => lam_lt_pow (hlam x)
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
  exact hA (LevelIn n × (Fin n → Option ℕ)) (LevelIn.view b) (LevelIn.vin b) N S hN lam M u₀
    (fun w => (S.levelIn hN lam M u₀ w, S.levelRecv hN lam M b u₀ w)) hP hc hS hcut hD hlam hM
    (S.vin_recv hN lam M hb u₀) (fun w x y hxy => S.view_recv hN lam M hb u₀ w x y hxy) v

end RData

end RotSystem

end SsspFlow
