import Cslib.Computability.Distributed.Congest.LowerBound
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Walk.Operations
import SsspFlow.PlanarMap

/-!
# CONGEST algorithms on plane networks

The model is `Cslib.Congest.Algorithm V I σ B`: synchronous rounds, node identifiers `V`, node
inputs `I`, unbounded local states `σ` and local computation, and messages of exactly `B` bits per
edge, direction and round. `Algorithm.run` is the execution on a simple graph. An algorithm is
fixed before the graph, so a statement of the form `∃ A, ∀ G, …` cannot store the graph in the
program.

* `Algorithm.widen`, `Algorithm.seq`: wider messages and sequential composition, with their
  semantics `run_widen`, `run_seq_lt`, `run_seq`.
* `Algorithm.keep`: inputs read from richer data that stays in the state (`run_keep`).
* `Algorithm.stopAt`: a run that ends after `T` rounds (`run_stopAt`).
* `Algorithm.exch`: one round in which every node tells its neighbours a number (`run_exch`).
* `Algorithm.iter`: an algorithm repeated with new inputs every `T` rounds (`run_iter`).
* `Algorithm.run_congr`: the state of a node after `t` rounds depends only on the inputs within `t`
  hops and on the edges at nodes within `t - 1` hops.
* `Net V`: a simple graph on the identifiers whose nodes list their neighbours in rotation order, and
  `Net.toRot`, its rotation system on the darts of the graph. `tail_eq_iff` says that its vertices are
  the nodes, `toRot_connected` that it is connected if the graph is. `triNet` is the triangle, a
  planar example with three vertices, three edges and two faces (`triNet_planar`).
-/

set_option autoImplicit false

namespace Cslib.Congest.Algorithm

variable {V I J σ σ' : Type*} {B B' : ℕ}

/-- Pad a message with `false`. -/
def padMsg (_h : B ≤ B') (m : Msg B) : Msg B' := fun i => if hi : i.1 < B then m ⟨i.1, hi⟩ else false

/-- The first bits of a message. -/
def cutMsg (h : B ≤ B') (m : Msg B') : Msg B := fun i => m ⟨i.1, lt_of_lt_of_le i.2 h⟩

@[simp] theorem cutMsg_padMsg (h : B ≤ B') (m : Msg B) : cutMsg h (padMsg h m) = m := by
  funext i
  simp [cutMsg, padMsg]

/-- The same algorithm with wider messages. -/
def widen (A : Algorithm V I σ B) (h : B ≤ B') : Algorithm V I σ B' where
  init := A.init
  send v s w := padMsg h (A.send v s w)
  step v s m := A.step v s (fun u => (m u).map (cutMsg h))
  out := A.out

theorem run_widen (A : Algorithm V I σ B) (h : B ≤ B') (G : SimpleGraph V) [DecidableRel G.Adj]
    (inp : V → I) : ∀ t, (A.widen h).run G inp t = A.run G inp t
  | 0 => rfl
  | t + 1 => by
    funext v
    have ih := run_widen A h G inp t
    show A.step v ((A.widen h).run G inp t v) (fun u => Option.map (cutMsg h)
        (if G.Adj u v then some (padMsg h (A.send u ((A.widen h).run G inp t u) v)) else none)) =
      A.step v (A.run G inp t v) (fun u => if G.Adj u v then some (A.send u (A.run G inp t u) v)
        else none)
    rw [ih]
    congr 1
    funext u
    split_ifs <;> simp

/-- Run `A` for `T` rounds, then `A'` on the inputs `f v s` read from the states `s` of `A`. -/
def seq (A : Algorithm V I σ B) (T : ℕ) (f : V → σ → J) (A' : Algorithm V J σ' B) :
    Algorithm V I ((ℕ × σ) ⊕ σ') B where
  init v i := if T = 0 then .inr (A'.init v (f v (A.init v i))) else .inl (0, A.init v i)
  send v s w :=
    match s with
    | .inl p => A.send v p.2 w
    | .inr s => A'.send v s w
  step v s m :=
    match s with
    | .inl p =>
      if p.1 + 1 = T then .inr (A'.init v (f v (A.step v p.2 m))) else .inl (p.1 + 1, A.step v p.2 m)
    | .inr s => .inr (A'.step v s m)
  out v s :=
    match s with
    | .inl p => A.out v p.2
    | .inr s => A'.out v s

variable (A : Algorithm V I σ B) (T : ℕ) (f : V → σ → J) (A' : Algorithm V J σ' B)
  (G : SimpleGraph V) [DecidableRel G.Adj] (inp : V → I)

theorem run_seq_lt : ∀ t, t < T →
    (A.seq T f A').run G inp t = fun v => .inl (t, A.run G inp t v)
  | 0, h => by
    funext v
    show (if T = 0 then _ else _) = _
    rw [ite_eq_right (by omega)]
    rfl
  | t + 1, h => by
    funext v
    have ih := run_seq_lt t (by omega)
    show (A.seq T f A').step v ((A.seq T f A').run G inp t v) (fun w => if G.Adj w v then
      some ((A.seq T f A').send w ((A.seq T f A').run G inp t w) v) else none) = _
    rw [ih]
    show (if t + 1 = T then _ else _) = _
    rw [ite_eq_right (by omega)]
    rfl

/-- The composition runs `A` for `T` rounds and then `A'`. -/
theorem run_seq : ∀ t,
    (A.seq T f A').run G inp (T + t) =
      fun v => .inr (A'.run G (fun v => f v (A.run G inp T v)) t v)
  | 0 => by
    funext v
    cases T with
    | zero => rfl
    | succ T =>
      have ih := run_seq_lt A (T + 1) f A' G inp T (by omega)
      show (A.seq (T + 1) f A').step v ((A.seq (T + 1) f A').run G inp T v) (fun w =>
        if G.Adj w v then
          some ((A.seq (T + 1) f A').send w ((A.seq (T + 1) f A').run G inp T w) v) else none) = _
      rw [ih]
      show (if T + 1 = T + 1 then _ else _) = _
      rw [ite_eq_left rfl]
      rfl
  | t + 1 => by
    funext v
    have ih := run_seq t
    show (A.seq T f A').step v ((A.seq T f A').run G inp (T + t) v) (fun w => if G.Adj w v then
      some ((A.seq T f A').send w ((A.seq T f A').run G inp (T + t) w) v) else none) = _
    rw [ih]
    rfl

/-- Run `A` on inputs read from `J`, with the input kept in the state. -/
def keep (A : Algorithm V I σ B) (g : V → J → I) : Algorithm V J (J × σ) B where
  init v j := (j, A.init v (g v j))
  send v s w := A.send v s.2 w
  step v s m := (s.1, A.step v s.2 m)
  out v s := A.out v s.2

theorem run_keep (A : Algorithm V I σ B) (g : V → J → I) (G : SimpleGraph V) [DecidableRel G.Adj]
    (inp : V → J) : ∀ t,
    (A.keep g).run G inp t = fun v => (inp v, A.run G (fun v => g v (inp v)) t v)
  | 0 => rfl
  | t + 1 => by
    funext v
    have ih := run_keep A g G inp t
    show (A.keep g).step v ((A.keep g).run G inp t v) (fun w => if G.Adj w v then
      some ((A.keep g).send w ((A.keep g).run G inp t w) v) else none) = _
    rw [ih]
    rfl

/-- Run `A` for `T` rounds and keep the state from then on. -/
def stopAt (A : Algorithm V I σ B) (T : ℕ) : Algorithm V I (ℕ × σ) B where
  init v i := (0, A.init v i)
  send v s w := A.send v s.2 w
  step v s m := if s.1 < T then (s.1 + 1, A.step v s.2 m) else s
  out v s := A.out v s.2

theorem run_stopAt (A : Algorithm V I σ B) (T : ℕ) (G : SimpleGraph V) [DecidableRel G.Adj]
    (inp : V → I) : ∀ t,
    (A.stopAt T).run G inp t = fun v => (min t T, A.run G inp (min t T) v)
  | 0 => by
    funext v
    simp only [Nat.zero_min]
    rfl
  | t + 1 => by
    funext v
    have ih := run_stopAt A T G inp t
    show (A.stopAt T).step v ((A.stopAt T).run G inp t v) (fun w => if G.Adj w v then
      some ((A.stopAt T).send w ((A.stopAt T).run G inp t w) v) else none) = _
    rw [ih]
    show (if min t T < T then _ else _) = _
    by_cases h : t < T
    · rw [ite_eq_left (by omega), min_eq_left h.le, min_eq_left (by omega : t + 1 ≤ T)]
      rfl
    · rw [ite_eq_right (by omega), min_eq_right (by omega : T ≤ t),
        min_eq_right (by omega : T ≤ t + 1)]

/-- A number as a message: its lowest `B` bits. -/
def toMsg (B x : ℕ) : Msg B := fun i => x.testBit i

theorem toMsg_inj {B x y : ℕ} (hx : x < 2 ^ B) (hy : y < 2 ^ B) (h : toMsg B x = toMsg B y) :
    x = y := by
  refine Nat.eq_of_testBit_eq fun i => ?_
  by_cases hi : i < B
  · exact congrFun h ⟨i, hi⟩
  · have hB : 2 ^ B ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [Nat.testBit_lt_two_pow (hx.trans_le hB), Nat.testBit_lt_two_pow (hy.trans_le hB)]

open Classical in
/-- The number below `2 ^ B` that a message encodes. -/
noncomputable def ofMsg {B : ℕ} (m : Msg B) : ℕ :=
  if h : ∃ x, x < 2 ^ B ∧ toMsg B x = m then h.choose else 0

theorem ofMsg_toMsg {B x : ℕ} (hx : x < 2 ^ B) : ofMsg (toMsg B x) = x := by
  have h : ∃ y, y < 2 ^ B ∧ toMsg B y = toMsg B x := ⟨x, hx, rfl⟩
  rw [ofMsg, dite_eq_left h]
  exact toMsg_inj h.choose_spec.1 hx h.choose_spec.2

/-- One round in which every node tells its neighbours a number. -/
noncomputable def exch (V : Type*) (B : ℕ) : Algorithm V ℕ (ℕ × (V → Option ℕ)) B where
  init _ x := (x, fun _ => none)
  send _ s _ := toMsg B s.1
  step _ s m := (s.1, fun u => (m u).map ofMsg)
  out _ _ := true

/-- After the exchange a node knows the numbers of its neighbours, if they fit into `B` bits. -/
theorem run_exch (G : SimpleGraph V) [DecidableRel G.Adj] (inp : V → ℕ) (h : ∀ v, inp v < 2 ^ B)
    (v : V) :
    (exch V B).run G inp 1 v = (inp v, fun u => if G.Adj u v then some (inp u) else none) := by
  show (inp v, fun u => (if G.Adj u v then some (toMsg B (inp u)) else none).map ofMsg) = _
  congr 1
  funext u
  split_ifs <;> simp [ofMsg_toMsg (h u)]

/-- Repeat `A` for `T` rounds at a time. Its inputs are read from data in `J`, and after `T` rounds
`u` computes new data from the old data and the state. -/
def iter (A : Algorithm V I σ B) (T : ℕ) (g : V → J → I) (u : V → J → σ → J) :
    Algorithm V J (J × ℕ × σ) B where
  init v j := (j, 0, A.init v (g v j))
  send v s w := A.send v s.2.2 w
  step v s m :=
    if s.2.1 + 1 = T then
      (u v s.1 (A.step v s.2.2 m), 0, A.init v (g v (u v s.1 (A.step v s.2.2 m))))
    else (s.1, s.2.1 + 1, A.step v s.2.2 m)
  out v s := A.out v s.2.2

/-- The data of `iter` after `k` repetitions. -/
def iterData (A : Algorithm V I σ B) (T : ℕ) (g : V → J → I) (u : V → J → σ → J)
    (G : SimpleGraph V) [DecidableRel G.Adj] (j₀ : V → J) : ℕ → V → J
  | 0 => j₀
  | k + 1 => fun v =>
    u v (iterData A T g u G j₀ k v)
      (A.run G (fun v => g v (iterData A T g u G j₀ k v)) T v)

/-- After `k` repetitions and `t` further rounds, `iter` holds the data of the repetition `k` and the
state of `A` after `t` rounds on these data. -/
theorem run_iter (A : Algorithm V I σ B) {T : ℕ} (g : V → J → I) (u : V → J → σ → J)
    (G : SimpleGraph V) [DecidableRel G.Adj] (j₀ : V → J) (hT : 0 < T) (k t : ℕ) (ht : t < T) :
    (A.iter T g u).run G j₀ (k * T + t) = fun v =>
      (iterData A T g u G j₀ k v, t,
        A.run G (fun v => g v (iterData A T g u G j₀ k v)) t v) := by
  have succ_run : ∀ r t' k', (A.iter T g u).run G j₀ r = (fun v =>
      (iterData A T g u G j₀ k' v, t',
        A.run G (fun v => g v (iterData A T g u G j₀ k' v)) t' v)) → ∀ v,
      (A.iter T g u).run G j₀ (r + 1) v =
        if t' + 1 = T then
          (u v (iterData A T g u G j₀ k' v)
            (A.run G (fun v => g v (iterData A T g u G j₀ k' v)) (t' + 1) v), 0,
            A.init v (g v (u v (iterData A T g u G j₀ k' v)
              (A.run G (fun v => g v (iterData A T g u G j₀ k' v)) (t' + 1) v))))
        else (iterData A T g u G j₀ k' v, t' + 1,
          A.run G (fun v => g v (iterData A T g u G j₀ k' v)) (t' + 1) v) := by
    intro r t' k' h v
    show (A.iter T g u).step v ((A.iter T g u).run G j₀ r v) (fun w => if G.Adj w v then
      some ((A.iter T g u).send w ((A.iter T g u).run G j₀ r w) v) else none) = _
    rw [h]
    rfl
  have all_t : ∀ k', (A.iter T g u).run G j₀ (k' * T) = (fun v =>
      (iterData A T g u G j₀ k' v, 0,
        A.run G (fun v => g v (iterData A T g u G j₀ k' v)) 0 v)) → ∀ t', t' < T →
      (A.iter T g u).run G j₀ (k' * T + t') = fun v =>
      (iterData A T g u G j₀ k' v, t',
        A.run G (fun v => g v (iterData A T g u G j₀ k' v)) t' v) := by
    intro k' h0 t'
    induction t' with
    | zero => exact fun _ => h0
    | succ t' ih =>
      intro ht'
      funext v
      have := succ_run _ t' k' (ih (by omega)) v
      rw [ite_eq_right (by omega)] at this
      exact this
  have all_k : ∀ k', (A.iter T g u).run G j₀ (k' * T) = (fun v =>
      (iterData A T g u G j₀ k' v, 0,
        A.run G (fun v => g v (iterData A T g u G j₀ k' v)) 0 v)) := by
    intro k'
    induction k' with
    | zero =>
      rw [Nat.zero_mul]
      rfl
    | succ k' ih =>
      funext v
      have hr : (k' + 1) * T = k' * T + (T - 1) + 1 := by
        rw [Nat.succ_mul]
        omega
      rw [hr]
      have := succ_run _ (T - 1) k' (all_t k' ih (T - 1) (by omega)) v
      rw [ite_eq_left (by omega)] at this
      rw [this, Nat.sub_add_cancel hT]
      rfl
  exact all_t k (all_k k) t ht

/-- **Locality.** The state of `v` after `t` rounds depends only on the inputs within `t` hops and
on the edges at nodes within `t - 1` hops. -/
theorem run_congr (A : Algorithm V I σ B) {G G' : SimpleGraph V} [DecidableRel G.Adj]
    [DecidableRel G'.Adj] {inp inp' : V → I} : ∀ (t : ℕ) (v : V),
    (∀ u, (∃ p : G.Walk u v, p.length ≤ t) → inp u = inp' u) →
    (∀ u a, (∃ p : G.Walk u v, p.length < t) → (G.Adj a u ↔ G'.Adj a u)) →
    A.run G inp t v = A.run G' inp' t v
  | 0, v, hi, _ => by
    show A.init v (inp v) = A.init v (inp' v)
    rw [hi v ⟨.nil, by simp⟩]
  | t + 1, v, hi, ha => by
    have hv : A.run G inp t v = A.run G' inp' t v :=
      run_congr A t v (fun u ⟨p, hp⟩ => hi u ⟨p, by omega⟩)
        (fun u a ⟨p, hp⟩ => ha u a ⟨p, by omega⟩)
    simp only [run]
    rw [hv]
    congr 1
    funext w
    have hw := ha v w ⟨.nil, by simp⟩
    by_cases h : G.Adj w v
    · have h' := hw.1 h
      have hrun : A.run G inp t w = A.run G' inp' t w :=
        run_congr A t w
          (fun u ⟨p, hp⟩ => hi u ⟨p.concat h, by rw [SimpleGraph.Walk.length_concat]; omega⟩)
          (fun u a ⟨p, hp⟩ => ha u a ⟨p.concat h, by rw [SimpleGraph.Walk.length_concat]; omega⟩)
      simp [h, h', hrun]
    · have h' : ¬ G'.Adj w v := fun x => h (hw.2 x)
      simp [h, h']

end Cslib.Congest.Algorithm

namespace SsspFlow.Congest

open FourColor

/-- A plane network: a simple graph on the identifiers `V`, and for every node the list of its
neighbours in rotation order. -/
structure Net (V : Type) [Fintype V] [DecidableEq V] where
  /-- The communication graph. -/
  G : SimpleGraph V
  /-- The neighbours of a node in rotation order. -/
  rotList : V → List V
  nodup : ∀ v, (rotList v).Nodup
  mem_rotList : ∀ v w, w ∈ rotList v ↔ G.Adj v w

namespace Net

variable {V : Type} [Fintype V] [DecidableEq V] (N : Net V)

instance : DecidableRel N.G.Adj := fun u v => decidable_of_iff _ (N.mem_rotList u v)

/-- The rotation of the darts at their tails. -/
def rotPerm : Equiv.Perm N.G.Dart where
  toFun d := ⟨(d.fst, (N.rotList d.fst).formPerm d.snd), (N.mem_rotList _ _).1
    (List.formPerm_apply_mem_of_mem ((N.mem_rotList _ _).2 d.adj))⟩
  invFun d := ⟨(d.fst, (N.rotList d.fst).formPerm.symm d.snd), (N.mem_rotList _ _).1
    (List.formPerm_mem_iff_mem.1 (by simpa using (N.mem_rotList _ _).2 d.adj))⟩
  left_inv d := SimpleGraph.Dart.ext _ _ (Prod.ext rfl (Equiv.symm_apply_apply _ _))
  right_inv d := SimpleGraph.Dart.ext _ _ (Prod.ext rfl (Equiv.apply_symm_apply _ _))

@[simp] theorem rotPerm_fst (d : N.G.Dart) : (N.rotPerm d).fst = d.fst := rfl

@[simp] theorem rotPerm_snd (d : N.G.Dart) :
    (N.rotPerm d).snd = (N.rotList d.fst).formPerm d.snd := rfl

/-- The rotation system of a plane network. -/
def toRot : RotSystem N.G.Dart where
  rev := SimpleGraph.Dart.symm
  rev_rev := SimpleGraph.Dart.symm_symm
  rev_ne := SimpleGraph.Dart.symm_ne
  rot := N.rotPerm

@[simp] theorem toRot_rev (d : N.G.Dart) : N.toRot.rev d = d.symm := rfl
@[simp] theorem toRot_rot (d : N.G.Dart) : N.toRot.rot d = N.rotPerm d := rfl

private theorem iterate_rot (n : ℕ) (d : N.G.Dart) :
    (N.rotPerm^[n] d).fst = d.fst ∧
      (N.rotPerm^[n] d).snd = ((N.rotList d.fst).formPerm ^ n) d.snd := by
  induction n with
  | zero => exact ⟨rfl, rfl⟩
  | succ n ih =>
    rw [Function.iterate_succ_apply', pow_succ', Equiv.Perm.mul_apply, rotPerm_fst, rotPerm_snd,
      ih.1, ih.2]
    exact ⟨rfl, rfl⟩

/-- Two darts have the same tail vertex of `toRot` if and only if they start at the same node. -/
theorem tail_eq_iff {d d' : N.G.Dart} : N.toRot.tail d = N.toRot.tail d' ↔ d.fst = d'.fst := by
  rw [RotSystem.tail_eq_iff]
  show fconnect (⇑N.rotPerm) d d' ↔ _
  constructor
  · intro h
    obtain ⟨n, rfl⟩ := fconnect_iff_iterate.1 h
    exact (N.iterate_rot n d).1.symm
  · intro h
    have hd : d.snd ∈ {a | a ∈ N.rotList d.fst} := (N.mem_rotList _ _).2 d.adj
    have hd' : d'.snd ∈ {a | a ∈ N.rotList d.fst} := by
      rw [h]
      exact (N.mem_rotList _ _).2 d'.adj
    obtain ⟨n, hn⟩ :=
      (N.nodup d.fst).isCycleOn_formPerm.exists_pow_eq' (Set.toFinite _) hd hd'
    exact fconnect_iff_iterate.2 ⟨n, SimpleGraph.Dart.ext _ _
      (Prod.ext ((N.iterate_rot n d).1.trans h) ((N.iterate_rot n d).2.trans hn))⟩

/-- All nodes are within `D` hops of each other. -/
def DiamLE (D : ℕ) : Prop := ∀ u v, ∃ p : N.G.Walk u v, p.length ≤ D

/-- All arc lengths lie in `[1, W]`, in both directions of every edge. -/
def LensIn (ℓ : V → V → ℕ) (W : ℕ) : Prop := ∀ u v, N.G.Adj u v → 1 ≤ ℓ u v ∧ ℓ u v ≤ W

private theorem isWalk_darts {a b : V} (p : N.G.Walk a b) (x y : N.G.Dart) (hx : x.fst = a)
    (hy : y.fst = b) : N.toRot.IsWalk (N.toRot.tail x) p.darts (N.toRot.tail y) := by
  induction p generalizing x with
  | nil => exact N.tail_eq_iff.2 (hx.trans hy.symm)
  | cons h q ih =>
    exact (N.toRot.isWalk_cons _ _ _ _).2 ⟨N.tail_eq_iff.2 hx.symm, ih _ rfl hy⟩

/-- The rotation system of a connected network with at least one edge is connected. -/
theorem toRot_connected (hG : N.G.Connected) (d : N.G.Dart) : N.toRot.Connected := by
  rw [RotSystem.connected_iff]
  refine ⟨⟨d⟩, fun u v => ?_⟩
  obtain ⟨x, rfl⟩ := N.toRot.exists_tail_eq u
  obtain ⟨y, rfl⟩ := N.toRot.exists_tail_eq v
  obtain ⟨p⟩ := hG.preconnected x.fst y.fst
  exact ⟨_, N.isWalk_darts p x y rfl rfl⟩

end Net

/-! ### The triangle -/

/-- The triangle. -/
def triNet : Net (Fin 3) where
  G := ⊤
  rotList := ![[1, 2], [2, 0], [0, 1]]
  nodup := by decide
  mem_rotList := by decide

private def triFace (d : triNet.G.Dart) : Bool := decide ((d.snd : ℕ) = ((d.fst : ℕ) + 1) % 3)

private theorem tri_cnode_iff (x y : triNet.G.Dart) :
    triNet.toRot.toHypermap.cnode x y ↔ x.fst = y.fst :=
  (triNet.toRot.tail_eq_iff x y).symm.trans triNet.tail_eq_iff

private theorem tri_cface_iff (x y : triNet.G.Dart) :
    triNet.toRot.toHypermap.cface x y ↔ triFace x = triFace y := by
  refine RotSystem.fconnect_iff_label _ _ (by decide) (fun x y h => ?_) x y
  have key : ∀ x y : triNet.G.Dart, triFace x = triFace y →
      ∃ n : Fin 3, (triNet.toRot.toHypermap.face)^[(n : ℕ)] x = y := by decide
  obtain ⟨n, hn⟩ := key x y h
  exact ⟨n, hn⟩

theorem triNet_numVertices : triNet.toRot.numVertices = 3 :=
  (RotSystem.fcard_eq_card_image triNet.toRot.toHypermap.cnode_sym (fun d => d.fst)
    tri_cnode_iff).trans (by decide)

theorem triNet_numFaces : triNet.toRot.numFaces = 2 :=
  (RotSystem.fcard_eq_card_image triNet.toRot.toHypermap.cface_sym triFace tri_cface_iff).trans
    (by decide)

theorem triNet_numEdges : triNet.toRot.numEdges = 3 := by
  rw [RotSystem.numEdges_eq]
  decide

theorem triNet_connected : triNet.toRot.Connected :=
  triNet.toRot_connected SimpleGraph.connected_top ⟨(0, 1), by decide⟩

/-- The rotation system of the triangle is planar. -/
theorem triNet_planar : triNet.toRot.Planar := by
  rw [RotSystem.planar_iff_euler _ triNet_connected, triNet_numVertices, triNet_numFaces,
    triNet_numEdges]

theorem triNet_diam : triNet.DiamLE 1 := by
  intro u v
  by_cases h : u = v
  · subst h
    exact ⟨.nil, Nat.zero_le _⟩
  · have hadj : triNet.G.Adj u v := h
    exact ⟨.cons hadj .nil, le_rfl⟩

end SsspFlow.Congest
