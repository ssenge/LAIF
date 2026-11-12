import SsspFlow.OracleChainDown

/-!
# The two runs along the parent chains in the message model

Every node has three flags as input: whether it is a target, and two flags `f0` and `f1`. The
algorithm `chainAlg` runs the exact shortest-path oracle; then one round in which every node tells
each neighbour whether it is its child, together with its two flags; then the counting run up the
chains for `f0` from the targets; then the run down the chains for `f1` from the nodes flagged by
`f0` with count `0`.

* `countIn_eq`, `downIn_eq`: the inputs of the two runs, built at each node from its input, its outputs
  and the numbers received, are those of the oracle for the lengths of `Net.markLenW` and
  `Net.downLenW`.
* `chainAlg_spec`: assuming the Exact SSSP bound, after `3 C log^c n · D + 1` rounds the outputs of the
  three runs meet the specification of the oracle.
-/

set_option autoImplicit false

namespace SsspFlow

namespace Congest

open Cslib.Congest Cslib.Congest.Algorithm
open scoped ENNReal

variable {V : Type} [Fintype V] [DecidableEq V]

/-- The number a node with parent `par` and flags `fl` sends to `b`: bit `0` says whether `b` is its
parent, bits `1` and `2` are its flags `f0` and `f1`. -/
def chainMsg (par : Option V) (fl : Bool × Bool × Bool) (b : V) : ℕ :=
  childMsg par b + 2 * fl.2.1.toNat + 4 * fl.2.2.toNat

/-- The input of the counting run: length `f0` on the arc to the parent, the flag `f0` of a child on
the arc from it, offset `0` at the targets. -/
def countIn (j : OracleIn V × (Bool × Bool × Bool)) (par : Option V) (rc : V → Option ℕ) : OracleIn V where
  nbrs := j.1.nbrs
  lenOut u := if u ∈ j.1.nbrs then (if par = some u then (j.2.2.1.toNat : ℕ∞) else ⊤) else ⊤
  lenIn u := if u ∈ j.1.nbrs then
    (if (rc u).map (· % 2) = some 1 then (((rc u).getD 0 / 2 % 2 : ℕ) : ℕ∞) else ⊤) else ⊤
  offset := if j.2.1 then 0 else ⊤

/-- The input of the run down the chains: length `f1` on the arcs to the children, the flag `f1` of
the parent on the arc from it, offset `0` at the nodes flagged by `f0` with count `d = 0`. -/
def downIn (j : OracleIn V × (Bool × Bool × Bool)) (par : Option V) (rc : V → Option ℕ) (d : ℕ∞) :
    OracleIn V where
  nbrs := j.1.nbrs
  lenOut u := if u ∈ j.1.nbrs then
    (if (rc u).map (· % 2) = some 1 then (j.2.2.2.toNat : ℕ∞) else ⊤) else ⊤
  lenIn u := if u ∈ j.1.nbrs then (if par = some u then (((rc u).getD 0 / 4 % 2 : ℕ) : ℕ∞) else ⊤) else ⊤
  offset := if j.2.2.1 && decide (d = 0) then 0 else ⊤

omit [Fintype V] in
theorem chainMsg_lt (par : Option V) (fl : Bool × Bool × Bool) (b : V) : chainMsg par fl b < 8 := by
  have h1 : childMsg par b ≤ 1 := by unfold childMsg; split_ifs <;> omega
  have h2 := Bool.toNat_le fl.2.1
  have h3 := Bool.toNat_le fl.2.2
  unfold chainMsg
  omega

omit [Fintype V] in
theorem chainMsg_bit0 (par : Option V) (fl : Bool × Bool × Bool) (b : V) :
    chainMsg par fl b % 2 = 1 ↔ par = some b := by
  have h2 := Bool.toNat_le fl.2.1
  have h3 := Bool.toNat_le fl.2.2
  unfold chainMsg childMsg
  split_ifs with h <;> simp only [h, iff_true, iff_false] <;> omega

omit [Fintype V] in
theorem chainMsg_bit1 (par : Option V) (fl : Bool × Bool × Bool) (b : V) :
    chainMsg par fl b / 2 % 2 = fl.2.1.toNat := by
  have h1 : childMsg par b ≤ 1 := by unfold childMsg; split_ifs <;> omega
  have h2 := Bool.toNat_le fl.2.1
  have h3 := Bool.toNat_le fl.2.2
  unfold chainMsg
  omega

omit [Fintype V] in
theorem chainMsg_bit2 (par : Option V) (fl : Bool × Bool × Bool) (b : V) :
    chainMsg par fl b / 4 % 2 = fl.2.2.toNat := by
  have h1 : childMsg par b ≤ 1 := by unfold childMsg; split_ifs <;> omega
  have h2 := Bool.toNat_le fl.2.1
  have h3 := Bool.toNat_le fl.2.2
  unfold chainMsg
  omega

/-- The input of the counting run is that of the oracle for the lengths `f0` on the arcs to the
parents and offset `0` at the targets. -/
theorem countIn_eq (N : Net V) (ℓ : V → V → ℕ∞) (φ : V → ℕ∞) (fl : V → Bool × Bool × Bool)
    (r : V → ℕ∞ × Option V) (v : V) :
    countIn (N.oracleIn ℓ φ v, fl v) (r v).2
        (fun u => if N.G.Adj u v then some (chainMsg (r u).2 (fl u) v) else none) =
      N.oracleIn (Net.markLenW r fun a => ((fl a).2.1.toNat : ℕ∞)) (Net.markOffB fun a => (fl a).1) v := by
  unfold countIn Net.oracleIn Net.markLenW Net.markOffB
  congr 1
  · funext u
    simp only [N.mem_rotList]
  · funext u
    simp only [N.mem_rotList]
    by_cases h : N.G.Adj v u
    · have h' : N.G.Adj u v := h.symm
      simp only [h, h', ite_true, Option.map_some, Option.getD_some, Option.some.injEq,
        chainMsg_bit0, chainMsg_bit1]
    · simp [h]

/-- The input of the run down the chains is that of the oracle for the lengths `f1` on the arcs to
the children and offset `0` at the nodes flagged by `f0` with count `0`. -/
theorem downIn_eq (N : Net V) (ℓ : V → V → ℕ∞) (φ : V → ℕ∞) (fl : V → Bool × Bool × Bool)
    (r : V → ℕ∞ × Option V) (d : V → ℕ∞) (v : V) :
    downIn (N.oracleIn ℓ φ v, fl v) (r v).2
        (fun u => if N.G.Adj u v then some (chainMsg (r u).2 (fl u) v) else none) (d v) =
      N.oracleIn (Net.downLenW r fun a => ((fl a).2.2.toNat : ℕ∞))
        (Net.markOffB fun a => (fl a).2.1 && decide (d a = 0)) v := by
  unfold downIn Net.oracleIn Net.downLenW Net.markOffB
  congr 1
  · funext u
    simp only [N.mem_rotList]
    by_cases h : N.G.Adj v u
    · have h' : N.G.Adj u v := h.symm
      simp only [h, h', ite_true, Option.map_some, Option.some.injEq, chainMsg_bit0]
    · simp [h]
  · funext u
    simp only [N.mem_rotList]
    by_cases h : N.G.Adj v u
    · have h' : N.G.Adj u v := h.symm
      simp only [h, h', ite_true, Option.getD_some, chainMsg_bit2]
    · simp [h]

/-- The input of `chainAlg`: the oracle input and the three flags. -/
abbrev ChainI (V : Type) := OracleIn V × (Bool × Bool × Bool)

/-- The state of `chainAlg` after the exchange round. -/
abbrev ChainQ (V σ : Type) := (ChainI V × σ) × ((V → ℕ) × (V → Option ℕ))

/-- The algorithm of the two runs along the chains: the oracle `A`, one round of messages, the
counting run, and the run down the chains. -/
noncomputable def chainAlg {σ : Type} {B : ℕ} (A : Algorithm V (OracleIn V) σ B)
    (out : V → σ → ℕ∞ × Option V) (T : ℕ) :
    Algorithm V (ChainI V)
      ((ℕ × (ChainI V × σ)) ⊕ ((ℕ × ChainQ V σ) ⊕ ((ℕ × (ChainQ V σ × σ)) ⊕ ((ChainQ V σ × σ) × σ))))
      (B + 3) :=
  ((A.widen (Nat.le_add_right B 3)).keep (fun _ (j : ChainI V) => j.1)).seq T (fun _ s => s)
    (((exchTo V (B + 3)).keep (fun v (p : ChainI V × σ) => chainMsg (out v p.2).2 p.1.2)).seq 1
      (fun _ s => s)
      (((A.widen (Nat.le_add_right B 3)).keep (fun v (q : ChainQ V σ) =>
          countIn q.1.1 (out v q.1.2).2 q.2.2)).seq T (fun _ s => s)
        ((A.widen (Nat.le_add_right B 3)).keep (fun v (s : ChainQ V σ × σ) =>
          downIn s.1.1.1 (out v s.1.1.2).2 s.1.2.2 (out v s.2).1))))

/-- The outputs of the three runs, read from a state of `chainAlg`. -/
def chainOut {σ : Type} (out : V → σ → ℕ∞ × Option V) (v : V) :
    ((ℕ × (ChainI V × σ)) ⊕ ((ℕ × ChainQ V σ) ⊕ ((ℕ × (ChainQ V σ × σ)) ⊕ ((ChainQ V σ × σ) × σ)))) →
      (ℕ∞ × Option V) × (ℕ∞ × Option V) × (ℕ∞ × Option V)
  | .inr (.inr (.inr ((q, s₃), s₄))) => (out v q.1.2, out v s₃, out v s₄)
  | _ => ((⊤, none), (⊤, none), (⊤, none))

/-- **The two runs along the chains.** Assuming the Exact SSSP bound, after `3 C log^c n · D + 1`
rounds the outputs of the first run, of the counting run up the chains for `f0` from the targets, and
of the run down the chains for `f1` from the nodes flagged by `f0` with count `0` meet the
specification of the oracle. -/
theorem chainAlg_spec (hE : ExactSsspBound) (K : ℕ) : ∃ C c : ℕ, ∀ n D : ℕ, 1 ≤ D →
    ∃ (σ : Type) (A : Algorithm (Fin n) (OracleIn (Fin n)) σ (C * logN n ^ c))
      (out : Fin n → σ → ℕ∞ × Option (Fin n)),
      ∀ (N : Net (Fin n)) (ℓ : Fin n → Fin n → ℕ∞) (φ : Fin n → ℕ∞) (fl : Fin n → Bool × Bool × Bool),
        N.toRot.Planar → N.DiamLE D → OracleValid N 0 ((n + 2) ^ K) ℓ φ →
        let st := (chainAlg A out (C * logN n ^ c * D)).run N.G (fun v => (N.oracleIn ℓ φ v, fl v))
          (C * logN n ^ c * D + (1 + (C * logN n ^ c * D + C * logN n ^ c * D)))
        N.ExactSpec ℓ φ (fun v => (chainOut out v (st v)).1) ∧
          N.ExactSpec (Net.markLenW (fun v => (chainOut out v (st v)).1) fun a => ((fl a).2.1.toNat : ℕ∞))
            (Net.markOffB fun a => (fl a).1) (fun v => (chainOut out v (st v)).2.1) ∧
          N.ExactSpec (Net.downLenW (fun v => (chainOut out v (st v)).1) fun a => ((fl a).2.2.toNat : ℕ∞))
            (Net.markOffB fun a => (fl a).2.1 && decide ((chainOut out a (st a)).2.1.1 = 0))
            (fun v => (chainOut out v (st v)).2.2) := by
  obtain ⟨C, c, hC⟩ := hE K
  refine ⟨C, c, fun n D hD => ?_⟩
  obtain ⟨σ, A, out, hA⟩ := hC n D hD
  refine ⟨σ, A, out, fun N ℓ φ fl hP hDi hval => ?_⟩
  set T := C * logN n ^ c * D
  set r : Fin n → ℕ∞ × Option (Fin n) := fun v => out v (A.run N.G (N.oracleIn ℓ φ) T v) with hr
  set ℓ₂ := Net.markLenW r fun a => ((fl a).2.1.toNat : ℕ∞) with hℓ₂
  set φ₂ := Net.markOffB fun a => (fl a).1 with hφ₂
  set r₂ : Fin n → ℕ∞ × Option (Fin n) := fun v => out v (A.run N.G (N.oracleIn ℓ₂ φ₂) T v) with hr₂
  set ℓ₃ := Net.downLenW r fun a => ((fl a).2.2.toNat : ℕ∞) with hℓ₃
  set φ₃ := Net.markOffB fun a => (fl a).2.1 && decide ((r₂ a).1 = 0) with hφ₃
  have hmsg : ∀ u w, chainMsg (r u).2 (fl u) w < 2 ^ (C * logN n ^ c + 3) := fun u w =>
    (chainMsg_lt _ _ _).trans_le (by
      calc (8 : ℕ) = 2 ^ 3 := rfl
        _ ≤ _ := Nat.pow_le_pow_right (by norm_num) (by omega))
  have hex : ∀ w, (exchTo (Fin n) (C * logN n ^ c + 3)).run N.G
      (fun w => chainMsg (out w (A.run N.G (fun v => (N.oracleIn ℓ φ v, fl v).1) T w)).2
        (N.oracleIn ℓ φ w, fl w).2) 1 w =
      (fun b => chainMsg (r w).2 (fl w) b, fun u => if N.G.Adj u w then some (chainMsg (r u).2 (fl u) w) else none) :=
    fun w => run_exchTo N.G (fun w b => chainMsg (r w).2 (fl w) b) hmsg w
  have hrun : ∀ v, chainOut out v ((chainAlg A out T).run N.G (fun v => (N.oracleIn ℓ φ v, fl v))
      (T + (1 + (T + T))) v) = (r v, r₂ v, out v (A.run N.G (N.oracleIn ℓ₃ φ₃) T v)) := by
    intro v
    unfold chainAlg
    rw [run_seq, run_seq, run_seq]
    simp only [run_keep, run_widen]
    simp only [hex]
    have hc : (fun v => countIn (N.oracleIn ℓ φ v, fl v) (out v (A.run N.G (fun v => N.oracleIn ℓ φ v) T v)).2
        fun u => if N.G.Adj u v then some (chainMsg (r u).2 (fl u) v) else none) = N.oracleIn ℓ₂ φ₂ :=
      funext fun v => countIn_eq N ℓ φ fl r v
    rw [hc]
    have hd : (fun v => downIn (N.oracleIn ℓ φ v, fl v) (out v (A.run N.G (fun v => N.oracleIn ℓ φ v) T v)).2
        (fun u => if N.G.Adj u v then some (chainMsg (r u).2 (fl u) v) else none)
        (out v (A.run N.G (N.oracleIn ℓ₂ φ₂) T v)).1) = N.oracleIn ℓ₃ φ₃ :=
      funext fun v => downIn_eq N ℓ φ fl r (fun a => (r₂ a).1) v
    rw [hd]
    rfl
  have hb : ∀ b : Bool, ((b.toNat : ℕ) : ℕ∞) ≤ (((n + 2) ^ K : ℕ) : ℕ∞) := fun b =>
    Nat.cast_le.2 (b.toNat_le.trans (Nat.one_le_pow _ _ (by omega)))
  have hoff : ∀ g : Fin n → Bool, ∀ z, Net.markOffB g z = ⊤ ∨ Net.markOffB g z ≤ (((n + 2) ^ K : ℕ) : ℕ∞) :=
    fun g z => by
      unfold Net.markOffB
      split_ifs
      · exact .inr zero_le
      · exact .inl rfl
  simp only [hrun]
  refine ⟨hA N ℓ φ hP hDi hval, hA N ℓ₂ φ₂ hP hDi ⟨fun u v _ => ?_, hoff _⟩,
    hA N ℓ₃ φ₃ hP hDi ⟨fun u v _ => ?_, hoff _⟩⟩
  · simp only [hℓ₂, Net.markLenW]
    split_ifs
    · exact .inr ⟨zero_le, hb _⟩
    · exact .inl rfl
  · simp only [hℓ₃, Net.downLenW]
    split_ifs
    · exact .inr ⟨zero_le, hb _⟩
    · exact .inl rfl

end Congest

end SsspFlow
