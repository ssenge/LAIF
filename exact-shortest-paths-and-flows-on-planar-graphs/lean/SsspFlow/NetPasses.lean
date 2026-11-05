import SsspFlow.NetTree

/-!
# The passes over the tree of a network

Relaxations give each node its depth (`dep_spec`), and the sums over the blocks of the tree by one pass up and
one pass down (`up_spec`, `down_spec`). The numbers of the darts of a node on the first tour and on the tour
through all darts are then functions of its memory (`numFL_eq`, `numPL_eq`), and one more round gives it the
numbers of the reverses of its darts (`rev_spec`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace SsspFlow.Congest

open Cslib.Congest Cslib.Congest.Algorithm FourColor RotSystem RotSystem.RootedTree

variable {n : ℕ}

/-- The number received from the neighbour `key - 1`. -/
def at1 (rcv : Fin n → Option ℕ) (key : ℕ) : ℕ :=
  if h : key - 1 < n then (rcv ⟨key - 1, h⟩).getD 0 else 0

theorem at1_succ (rcv : Fin n → Option ℕ) (u : Fin n) : at1 rcv (u + 1) = (rcv u).getD 0 := by
  unfold at1
  rw [dif_pos (by simpa using u.2)]
  rfl

/-- A relaxation whose state at `0` is the own value of a node, and whose state at `u + 1` is the number last
received from `u`. -/
def passIn (i0 : ℕ) (m : ℕ → Fin n → ℕ) (f : (Fin n → Option ℕ) → ℕ) : RelaxIn (Fin n) where
  init key := if key = 0 then i0 else 0
  msg s w := m (s 0) w
  upd _ rcv key := if key = 0 then f rcv else at1 rcv key

section Pass

variable {B : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (i0 : Fin n → ℕ)
  (m : Fin n → ℕ → Fin n → ℕ) (f : Fin n → (Fin n → Option ℕ) → ℕ)

theorem pass_init (v : Fin n) :
    relaxSt B G (fun v => passIn (i0 v) (m v) (f v)) 0 v 0 = i0 v := rfl

theorem pass_zero (t : ℕ) (v : Fin n) :
    relaxSt B G (fun v => passIn (i0 v) (m v) (f v)) (t + 1) v 0 = f v fun u =>
      if G.Adj u v then
        some (ofMsg (toMsg B (m u (relaxSt B G (fun v => passIn (i0 v) (m v) (f v)) t u 0) v)))
      else none := rfl

theorem pass_nbr (t : ℕ) {u v : Fin n} (hadj : G.Adj u v)
    (hfit : m u (relaxSt B G (fun v => passIn (i0 v) (m v) (f v)) t u 0) v < 2 ^ B) :
    relaxSt B G (fun v => passIn (i0 v) (m v) (f v)) (t + 1) v (u + 1) =
      m u (relaxSt B G (fun v => passIn (i0 v) (m v) (f v)) t u 0) v := by
  have key : ∀ (s : ℕ → ℕ) (rcv : Fin n → Option ℕ),
      (passIn (i0 v) (m v) (f v)).upd s rcv ((u : ℕ) + 1) = (rcv u).getD 0 := by
    intro s rcv
    show (if (u : ℕ) + 1 = 0 then f v rcv else at1 rcv (u + 1)) = _
    rw [if_neg (Nat.succ_ne_zero _), at1_succ]
  rw [relaxSt_succ, key, if_pos hadj]
  exact ofMsg_toMsg hfit

end Pass

variable {B : ℕ} (N : Net (Fin n)) (hG : N.G.Connected) {r : Fin n} {d₀ : N.G.Dart}

section Dep

/-- The least number received. -/
noncomputable def minRcv (rcv : Fin n → Option ℕ) : ℕ := sInf {x | ∃ u, rcv u = some x}

/-- The next depth of a node. -/
noncomputable def depF (r v : Fin n) (rcv : Fin n → Option ℕ) : ℕ :=
  if v = r then 0 else min n (1 + minRcv rcv)

include hG in
theorem dist_lt_n (r v : Fin n) : N.G.dist r v < n := by
  obtain ⟨p, hp, hl⟩ := hG.exists_path_of_dist r v
  have := hp.length_lt
  rw [Fintype.card_fin] at this
  omega

include hG in
/-- **The depth of a node.** -/
theorem dep_spec (hn : n < 2 ^ B) : ∀ t (v : Fin n),
    relaxSt B N.G (fun v => passIn (if v = r then 0 else n) (fun x _ => x) (depF r v)) t v 0 =
      if N.G.dist r v ≤ t then N.G.dist r v else n := by
  intro t
  induction t with
  | zero =>
    intro v
    rw [pass_init]
    by_cases hv : v = r
    · rw [if_pos hv, hv, SimpleGraph.dist_self, if_pos le_rfl]
    · rw [if_neg hv, if_neg]
      have := hG.pos_dist_of_ne (u := r) (v := v) (Ne.symm hv)
      omega
  | succ t ih =>
    intro v
    rw [pass_zero]
    unfold depF
    by_cases hv : v = r
    · rw [if_pos hv, hv, SimpleGraph.dist_self, if_pos (by omega)]
    rw [if_neg hv]
    have hval : ∀ u, (if N.G.dist r u ≤ t then N.G.dist r u else n) ≤ n := fun u => by
      split_ifs with h
      · exact (dist_lt_n N hG r u).le
      · exact le_rfl
    have hS : {x | ∃ u, (if N.G.Adj u v then some (ofMsg (toMsg B (relaxSt B N.G (fun v =>
        passIn (if v = r then 0 else n) (fun x _ => x) (depF r v)) t u 0))) else none) = some x} =
        {x | ∃ u, N.G.Adj u v ∧ (if N.G.dist r u ≤ t then N.G.dist r u else n) = x} := by
      ext x
      simp only [Set.mem_setOf_eq]
      constructor
      · rintro ⟨u, hu⟩
        by_cases ha : N.G.Adj u v
        · rw [if_pos ha, ih u, ofMsg_toMsg (lt_of_le_of_lt (hval u) hn)] at hu
          exact ⟨u, ha, Option.some.inj hu⟩
        · rw [if_neg ha] at hu
          exact absurd hu (by simp)
      · rintro ⟨u, ha, rfl⟩
        refine ⟨u, ?_⟩
        rw [if_pos ha, ih u, ofMsg_toMsg (lt_of_le_of_lt (hval u) hn)]
    have hpa : N.G.Adj (N.parN r v) v := (N.parN_adj hG hv).symm
    have hpd := N.parN_dist hG hv
    have hlow : ∀ u, N.G.Adj u v → N.G.dist r v ≤ N.G.dist r u + 1 := fun u hu => by
      have h1 : N.G.dist r v ≤ N.G.dist r u + N.G.dist u v := hG.dist_triangle
      rw [SimpleGraph.dist_eq_one_iff_adj.2 hu] at h1
      exact h1
    have hltv := dist_lt_n N hG r v
    by_cases hd : N.G.dist r v ≤ t + 1
    · rw [if_pos hd]
      have hmem : N.G.dist r (N.parN r v) ∈
          {x | ∃ u, N.G.Adj u v ∧ (if N.G.dist r u ≤ t then N.G.dist r u else n) = x} :=
        ⟨_, hpa, if_pos (by omega)⟩
      have hinf : sInf {x | ∃ u, N.G.Adj u v ∧ (if N.G.dist r u ≤ t then N.G.dist r u else n) = x} =
          N.G.dist r (N.parN r v) := by
        refine le_antisymm (Nat.sInf_le hmem) (le_csInf ⟨_, hmem⟩ ?_)
        rintro x ⟨u, hu, rfl⟩
        have := hlow u hu
        split_ifs <;> omega
      refine (congrArg (fun S => min n (1 + sInf S)) hS).trans ?_
      beta_reduce
      rw [hinf]
      omega
    · rw [if_neg hd]
      have hmem : n ∈ {x | ∃ u, N.G.Adj u v ∧ (if N.G.dist r u ≤ t then N.G.dist r u else n) = x} :=
        ⟨_, hpa, if_neg (by omega)⟩
      have hinf : sInf {x | ∃ u, N.G.Adj u v ∧ (if N.G.dist r u ≤ t then N.G.dist r u else n) = x} = n := by
        refine le_antisymm (Nat.sInf_le hmem) (le_csInf ⟨_, hmem⟩ ?_)
        rintro x ⟨u, hu, rfl⟩
        have := hlow u hu
        rw [if_neg (by omega)]
      refine (congrArg (fun S => min n (1 + sInf S)) hS).trans ?_
      beta_reduce
      rw [hinf]
      omega

end Dep

/-- The parent of a node from its memory. -/
noncomputable def parR (rl : List (Fin n)) (v : Fin n) (m : Mem) : Fin n :=
  Net.parLoc v (Finset.univ.filter fun u => u ∈ rl ∧ m 1 (u + 1) + 1 = m 1 0)

/-- The parent of a neighbour from the memory of a node. -/
def nparL (m : Mem) (u : Fin n) : ℕ := m 2 (u + 1)

/-- The dart goes from the node to a child. -/
def isC0L (v : Fin n) (m : Mem) (y : Fin n × Bool) : Prop := y.2 = false ∧ nparL m y.1 = v

open Classical in
/-- The weight of a dart at a node in the pass up, by the numbers received. -/
noncomputable def incR (δ : ℕ) (v : Fin n) (m : Mem) (rcv : Fin n → Option ℕ) (y : Fin n × Bool) : ℕ :=
  if isC0L v m y then (rcv y.1).getD 0 else δ

/-- The next value of a node in the pass up. -/
noncomputable def upF (δ : ℕ) (r : Fin n) (rl : List (Fin n)) (v : Fin n) (m : Mem)
    (rcv : Fin n → Option ℕ) : ℕ :=
  if v = r then 0
  else 2 + offBy (rotV rl) (incR δ v m rcv) (parR rl v m, true) (parR rl v m, false)

open Classical in
/-- The weight of a dart at a node after the pass up. -/
noncomputable def incL (δ jUp : ℕ) (v : Fin n) (m : Mem) (y : Fin n × Bool) : ℕ :=
  if isC0L v m y then m jUp (y.1 + 1) else δ

/-- The first dart of a node on the first tour. -/
noncomputable def baseL (r : Fin n) (rl : List (Fin n)) (v : Fin n) (m : Mem) : Fin n × Bool :=
  if v = r then (rl.headD v, true) else (parR rl v m, true)

/-- The message of a node to a child in the pass down. -/
noncomputable def downM (δ jUp : ℕ) (r : Fin n) (rl : List (Fin n)) (v : Fin n) (m : Mem) (x : ℕ)
    (w : Fin n) : ℕ :=
  if nparL m w = v then
    x + offBy (rotV rl) (incL δ jUp v m) (baseL r rl v m) ((rotV rl)⁻¹ (w, false)) + 1
  else 0

/-- The next value of a node in the pass down. -/
noncomputable def downF (r : Fin n) (rl : List (Fin n)) (v : Fin n) (m : Mem)
    (rcv : Fin n → Option ℕ) : ℕ :=
  if v = r then 0 else (rcv (parR rl v m)).getD 0

/-- The number of a dart of a node on the first tour, from the memory. -/
noncomputable def numFL (δ jUp jDown : ℕ) (r : Fin n) (rl : List (Fin n)) (v : Fin n) (m : Mem)
    (y : Fin n × Bool) : ℕ :=
  m jDown 0 + offBy (rotV rl) (incL δ jUp v m) (baseL r rl v m) y

open Classical in
/-- The position of a dart of a node on the tour through all darts, from the memory. -/
noncomputable def numPL (r : Fin n) (rl : List (Fin n)) (v : Fin n) (m : Mem) (y : Fin n × Bool) : ℕ :=
  if isC0L v m y then numFL 1 4 6 r rl v m ((rotV rl)⁻¹ y) + m 1 0 + 1
  else numFL 1 4 6 r rl v m y + m 1 0

/-- The number of the reverse of a dart, from the pair received from its head. -/
def revR (k : ℕ) (m : Mem) (y : Fin n × Bool) : ℕ :=
  if y.2 then (Nat.unpair (m k (y.1 + 1))).1 else (Nat.unpair (m k (y.1 + 1))).2

/-- The message of a node with numbers of its darts: a pair for each neighbour. -/
def revM (val : Fin n × Bool → ℕ) (w : Fin n) : ℕ := Nat.pair (val (w, false)) (val (w, true))

theorem incR_pos {δ : ℕ} {v : Fin n} {m : Mem} {rcv : Fin n → Option ℕ} {y : Fin n × Bool}
    (h : isC0L v m y) : incR δ v m rcv y = (rcv y.1).getD 0 := if_pos h

theorem incR_neg {δ : ℕ} {v : Fin n} {m : Mem} {rcv : Fin n → Option ℕ} {y : Fin n × Bool}
    (h : ¬ isC0L v m y) : incR δ v m rcv y = δ := if_neg h

theorem incL_pos {δ jUp : ℕ} {v : Fin n} {m : Mem} {y : Fin n × Bool}
    (h : isC0L v m y) : incL δ jUp v m y = m jUp (y.1 + 1) := if_pos h

theorem incL_neg {δ jUp : ℕ} {v : Fin n} {m : Mem} {y : Fin n × Bool}
    (h : ¬ isC0L v m y) : incL δ jUp v m y = δ := if_neg h

theorem upF_root {δ : ℕ} {r v : Fin n} {rl : List (Fin n)} {m : Mem} {rcv : Fin n → Option ℕ}
    (hv : v = r) : upF δ r rl v m rcv = 0 := if_pos hv

theorem upF_ne {δ : ℕ} {r v : Fin n} {rl : List (Fin n)} {m : Mem} {rcv : Fin n → Option ℕ}
    (hv : ¬ v = r) : upF δ r rl v m rcv =
      2 + offBy (rotV rl) (incR δ v m rcv) (parR rl v m, true) (parR rl v m, false) := if_neg hv

theorem downF_root {r v : Fin n} {rl : List (Fin n)} {m : Mem} {rcv : Fin n → Option ℕ}
    (hv : v = r) : downF r rl v m rcv = 0 := if_pos hv

theorem downF_ne {r v : Fin n} {rl : List (Fin n)} {m : Mem} {rcv : Fin n → Option ℕ}
    (hv : ¬ v = r) : downF r rl v m rcv = (rcv (parR rl v m)).getD 0 := if_neg hv

theorem upS_root {D V : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V] {R : RotSystem D}
    (t : R.RootedTree V) (δ : ℕ) : t.upS δ t.root = 0 := by
  unfold upS
  simp [upIter]

variable {N}

theorem loc_rot_inv (y : N.G.Dart × Bool) :
    N.locN (N.toRot.double.rot⁻¹ y) = (rotV (N.rotList y.1.fst))⁻¹ (N.locN y) := by
  have h1 := N.loc_rot (N.toRot.double.rot⁻¹ y)
  have h2 : N.toRot.double.rot (N.toRot.double.rot⁻¹ y) = y := perm_apply_inv_self _ _
  have h3 := N.fst_rot (N.toRot.double.rot⁻¹ y)
  rw [h2] at h1 h3
  rw [h1, ← h3, perm_inv_apply_self]

theorem fst_rot_inv (y : N.G.Dart × Bool) : (N.toRot.double.rot⁻¹ y).1.fst = y.1.fst := by
  have h3 := N.fst_rot (N.toRot.double.rot⁻¹ y)
  have h2 : N.toRot.double.rot (N.toRot.double.rot⁻¹ y) = y := perm_apply_inv_self _ _
  rw [h2] at h3
  exact h3.symm

theorem parR_eq {v : Fin n} {m : Mem} (h0 : m 1 0 = N.G.dist r v)
    (h1 : ∀ u, N.G.Adj v u → m 1 (u + 1) = N.G.dist r u) :
    parR (N.rotList v) v m = N.parN r v := by
  unfold parR Net.parN Net.parSet
  congr 1
  ext u
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, N.mem_rotList]
  constructor
  · rintro ⟨h2, h3⟩
    rw [h1 u h2, h0] at h3
    exact ⟨h2, h3⟩
  · rintro ⟨h2, h3⟩
    rw [h1 u h2, h0]
    exact ⟨h2, h3⟩

theorem loc_c1 {v : Fin n} (hv : v ≠ r) : N.locN ((N.treeN hG r d₀).c1 v) = (N.parN r v, true) := by
  obtain ⟨-, h2, h3⟩ := (N.treeN_c1_iff hG d₀ hv _).1 rfl
  exact Prod.ext h2 h3

theorem loc_r0 {v : Fin n} (hv : v ≠ r) : N.locN ((N.treeN hG r d₀).r0 v) = (N.parN r v, false) := by
  obtain ⟨-, h2, h3⟩ := (N.treeN_r0_iff hG d₀ hv _).1 rfl
  exact Prod.ext h2 h3

theorem loc_c0 {v : Fin n} (hv : v ≠ r) : N.locN ((N.treeN hG r d₀).c0 v) = (v, false) := by
  obtain ⟨-, h2, h3⟩ := (N.treeN_c0_iff hG d₀ hv _).1 rfl
  exact Prod.ext h2 h3

theorem fst_c1 {v : Fin n} (hv : v ≠ r) : ((N.treeN hG r d₀).c1 v).1.fst = v :=
  ((N.treeN_c1_iff hG d₀ hv _).1 rfl).1

theorem fst_r0 {v : Fin n} (hv : v ≠ r) : ((N.treeN hG r d₀).r0 v).1.fst = v :=
  ((N.treeN_r0_iff hG d₀ hv _).1 rfl).1

theorem fst_c0 {v : Fin n} (hv : v ≠ r) : ((N.treeN hG r d₀).c0 v).1.fst = N.parN r v :=
  ((N.treeN_c0_iff hG d₀ hv _).1 rfl).1

theorem treeN_par {v : Fin n} (hv : v ≠ r) : (N.treeN hG r d₀).par v = N.parN r v := by
  have := (N.treeN hG r d₀).vertM_c0 v
  rw [N.treeN_vertM, fst_c0 hG hv] at this
  exact this.symm

section Passes

variable (mem : Fin n → Mem) (hpar : ∀ v, parR (N.rotList v) v (mem v) = N.parN r v)
  (hnp : ∀ v u, N.G.Adj u v → nparL (mem v) u = N.parN r u)


include hpar hnp in
/-- A dart at a node is a dart to a child if and only if the node sees that from its memory. -/
theorem isC0L_iff {v : Fin n} {y : N.G.Dart × Bool} (hy : y.1.fst = v) :
    isC0L v (mem v) (N.locN y) ↔ (N.treeN hG r d₀).IsC0 y := by
  rw [N.isC0_iff hG d₀]
  unfold isC0L
  have hadj : N.G.Adj y.1.snd v := by
    rw [← hy]
    exact y.1.adj.symm
  show (y.2 = false ∧ nparL (mem v) y.1.snd = (v : ℕ)) ↔ _
  rw [hnp v _ hadj, hy]
  simp only [Fin.val_inj]

include hpar hnp in
/-- **The pass up.** -/
theorem up_spec (δ : ℕ) (hfit : ∀ v, (N.treeN hG r d₀).upS δ v < 2 ^ B) :
    ∀ k tt (v : Fin n), (N.treeN hG r d₀).depBd - (N.treeN hG r d₀).dep v = k → k < tt →
      relaxSt B N.G (fun v => passIn 0 (fun x _ => x) (upF δ r (N.rotList v) v (mem v))) tt v 0 =
        (N.treeN hG r d₀).upS δ v := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro tt v hk htt
    obtain ⟨tt', rfl⟩ : ∃ tt', tt = tt' + 1 := ⟨tt - 1, by omega⟩
    rw [pass_zero]
    by_cases hv : v = r
    · rw [upF_root hv, hv]
      exact (upS_root (N.treeN hG r d₀) δ).symm
    rw [upF_ne hv, upS_eq (t := N.treeN hG r d₀) δ hv]
    congr 1
    rw [hpar v, ← loc_c1 hG hv, ← loc_r0 hG hv,
      offBy_transport (b := (N.treeN hG r d₀).c1 v) (N.loc_hyp (fst_c1 hG hv))
        (N.loc_inj (fst_c1 hG hv) (fst_r0 hG hv))]
    refine offBy_congr fun y hy => ?_
    have hyf : y.1.fst = v := by
      rw [N.fst_of_fconnect hy, fst_c1 hG hv]
    show incR δ v (mem v) _ (N.locN y) = _
    by_cases hC : (N.treeN hG r d₀).IsC0 y
    · rw [incR_pos ((isC0L_iff hG mem hpar hnp hyf).2 hC)]
      obtain ⟨u, hu, rfl⟩ := hC
      have hu' : u ≠ r := hu
      rw [incOf_c0 _ _ hu, loc_c0 hG hu']
      have hadj : N.G.Adj u v := by
        have := ((N.treeN hG r d₀).c0 u).1.adj
        rw [hyf] at this
        have h2 : ((N.treeN hG r d₀).c0 u).1.snd = u := ((N.treeN_c0_iff hG d₀ hu' _).1 rfl).2.1
        rw [h2] at this
        exact this.symm
      show Option.getD (if N.G.Adj u v then _ else _) 0 = _
      rw [if_pos hadj]
      have hd := dep_of_walk (t := N.treeN hG r d₀) hv hy rfl hu
      have hb := dep_le_depBd (t := N.treeN hG r d₀) u
      have hval := ih _ (by omega) tt' u rfl (by omega)
      show ofMsg (toMsg B (relaxSt B N.G _ tt' u 0)) = _
      rw [hval, ofMsg_toMsg (hfit u)]
    · rw [incR_neg (fun h => hC ((isC0L_iff hG mem hpar hnp hyf).1 h)), incOf_not hC]

variable {δ jUp : ℕ} (hup : ∀ v u, N.G.Adj u v → mem v jUp (u + 1) = (N.treeN hG r d₀).upS δ u)
  (hd₀ : d₀.fst = r) (hhd : d₀.snd = (N.rotList r).headD r)

include hpar hd₀ hhd in
theorem loc_base (v : Fin n) :
    N.locN ((N.treeN hG r d₀).base (d₀, true) v) = baseL r (N.rotList v) v (mem v) := by
  unfold base baseL
  by_cases hv : v = r
  · have hv' : v = (N.treeN hG r d₀).root := hv
    rw [if_pos hv', if_pos hv, hv]
    exact Prod.ext hhd rfl
  · have hv' : ¬ v = (N.treeN hG r d₀).root := hv
    rw [if_neg hv', if_neg hv, hpar v]
    exact loc_c1 hG hv

include hd₀ in
theorem fst_base (v : Fin n) : ((N.treeN hG r d₀).base (d₀, true) v).1.fst = v := by
  have h0 : (N.treeN hG r d₀).vertM (d₀, true) = (N.treeN hG r d₀).root := hd₀
  exact vertM_base h0 v

include hpar hnp hup hd₀ hhd in
/-- The sums along the rotation at a node, from its memory. -/
theorem offBy_loc {v : Fin n} {y : N.G.Dart × Bool} (hy : y.1.fst = v) :
    offBy (rotV (N.rotList v)) (incL δ jUp v (mem v)) (baseL r (N.rotList v) v (mem v)) (N.locN y) =
      offBy N.toRot.double.rot ((N.treeN hG r d₀).incOf δ ((N.treeN hG r d₀).upS δ))
        ((N.treeN hG r d₀).base (d₀, true) v) y := by
  rw [← loc_base hG mem hpar hd₀ hhd, offBy_transport
    (b := (N.treeN hG r d₀).base (d₀, true) v) (N.loc_hyp (fst_base hG hd₀ v))
    (N.loc_inj (fst_base hG hd₀ v) hy)]
  refine offBy_congr fun w hw => ?_
  have hwf : w.1.fst = v := by
    rw [N.fst_of_fconnect hw, fst_base hG hd₀]
  show incL δ jUp v (mem v) (N.locN w) = _
  by_cases hC : (N.treeN hG r d₀).IsC0 w
  · rw [incL_pos ((isC0L_iff hG mem hpar hnp hwf).2 hC)]
    obtain ⟨u, hu, rfl⟩ := hC
    have hu' : u ≠ r := hu
    rw [incOf_c0 _ _ hu, loc_c0 hG hu']
    have hadj : N.G.Adj u v := by
      have := ((N.treeN hG r d₀).c0 u).1.adj
      rw [hwf] at this
      have h2 : ((N.treeN hG r d₀).c0 u).1.snd = u := ((N.treeN_c0_iff hG d₀ hu' _).1 rfl).2.1
      rw [h2] at this
      exact this.symm
    exact hup v u hadj
  · rw [incL_neg (fun h => hC ((isC0L_iff hG mem hpar hnp hwf).1 h)), incOf_not hC]

include hpar hnp hup hd₀ hhd in
/-- **The pass down.** -/
theorem down_spec (hfit : ∀ v, (N.treeN hG r d₀).downS δ (d₀, true) v < 2 ^ B) :
    ∀ k tt (v : Fin n), (N.treeN hG r d₀).dep v = k → k < tt →
      relaxSt B N.G (fun v => passIn 0 (downM δ jUp r (N.rotList v) v (mem v))
        (downF r (N.rotList v) v (mem v))) tt v 0 = (N.treeN hG r d₀).downS δ (d₀, true) v := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro tt v hk htt
    obtain ⟨tt', rfl⟩ : ∃ tt', tt = tt' + 1 := ⟨tt - 1, by omega⟩
    rw [pass_zero]
    by_cases hv : v = r
    · rw [downF_root hv, hv]
      exact (downS_root (t := N.treeN hG r d₀) δ (d₀, true)).symm
    rw [downF_ne hv, hpar v, downS_eq (t := N.treeN hG r d₀) δ (d₀, true) hv]
    have hadj : N.G.Adj (N.parN r v) v := (N.parN_adj hG hv).symm
    show Option.getD (if N.G.Adj (N.parN r v) v then _ else _) 0 = _
    rw [if_pos hadj]
    have hdp := (N.treeN hG r d₀).dep_par_lt hv
    rw [treeN_par hG hv] at hdp ⊢
    rw [ih _ (by omega) tt' (N.parN r v) rfl (by omega)]
    have hnpv : nparL (mem (N.parN r v)) v = (N.parN r v : ℕ) := by
      rw [hnp _ _ (N.parN_adj hG hv)]
    have hfy : (N.toRot.double.rot⁻¹ ((N.treeN hG r d₀).c0 v)).1.fst = N.parN r v := by
      rw [fst_rot_inv, fst_c0 hG hv]
    have hval : downM δ jUp r (N.rotList (N.parN r v)) (N.parN r v) (mem (N.parN r v))
        ((N.treeN hG r d₀).downS δ (d₀, true) (N.parN r v)) v =
        (N.treeN hG r d₀).downS δ (d₀, true) (N.parN r v) +
          offBy N.toRot.double.rot ((N.treeN hG r d₀).incOf δ ((N.treeN hG r d₀).upS δ))
            ((N.treeN hG r d₀).base (d₀, true) (N.parN r v))
            (N.toRot.double.rot⁻¹ ((N.treeN hG r d₀).c0 v)) + 1 := by
      unfold downM
      rw [if_pos hnpv, ← offBy_loc hG mem hpar hnp hup hd₀ hhd hfy, loc_rot_inv, fst_c0 hG hv, loc_c0 hG hv]
    show ofMsg (toMsg B _) = _
    rw [hval]
    have hlt := hfit v
    rw [downS_eq (t := N.treeN hG r d₀) δ (d₀, true) hv, treeN_par hG hv] at hlt
    rw [ofMsg_toMsg hlt]

/-- The node sees the number of a dart on the first tour. -/
theorem numFL_eq {jDown : ℕ} {v : Fin n} (hdown : mem v jDown 0 = (N.treeN hG r d₀).downS δ (d₀, true) v)
    {y : N.G.Dart × Bool} (hy : y.1.fst = v)
    (hpar : ∀ v, parR (N.rotList v) v (mem v) = N.parN r v)
    (hnp : ∀ v u, N.G.Adj u v → nparL (mem v) u = N.parN r u)
    (hup : ∀ v u, N.G.Adj u v → mem v jUp (u + 1) = (N.treeN hG r d₀).upS δ u)
    (hd₀ : d₀.fst = r) (hhd : d₀.snd = (N.rotList r).headD r) :
    numFL δ jUp jDown r (N.rotList v) v (mem v) (N.locN y) =
      (N.treeN hG r d₀).numF δ (d₀, true) y := by
  unfold numFL numF
  rw [hdown, offBy_loc hG mem hpar hnp hup hd₀ hhd hy, N.treeN_vertM, hy]

/-- The message of the exchange is a pair of numbers of the two darts to a neighbour. -/
theorem rev_spec {val : Fin n → Fin n × Bool → ℕ} {k : ℕ} {t' : ℕ} {z : N.G.Dart × Bool}
    (hfit : revM (val z.1.snd) z.1.fst < 2 ^ B) {m : Mem}
    (hm : m k = relaxSt B N.G (fun v => passIn 0 (fun _ w => revM (val v) w) (fun _ => 0)) (t' + 1) z.1.fst) :
    revR k m (N.locN z) = val z.1.snd (N.locN (N.toRot.double.rev z)) := by
  unfold revR
  have h1 := pass_nbr (B := B) N.G (fun _ => 0) (fun v _ w => revM (val v) w) (fun _ _ => 0) t' z.1.adj.symm hfit
  show (if z.2 then (Nat.unpair (m k (z.1.snd + 1))).1 else (Nat.unpair (m k (z.1.snd + 1))).2) = _
  rw [hm, h1]
  obtain ⟨d, _ | _⟩ := z
  · show (Nat.unpair (revM (val d.snd) d.fst)).2 = val d.snd (d.fst, true)
    unfold revM
    rw [Nat.unpair_pair]
  · show (Nat.unpair (revM (val d.snd) d.fst)).1 = val d.snd (d.fst, false)
    unfold revM
    rw [Nat.unpair_pair]

end Passes

section Bounds

variable {D V : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V] {R : RotSystem D}
  {t : R.RootedTree V} {w₀ : D × Bool} {T₀ : Finset (D × Bool)} {δ : ℕ}

theorem phi_le_card (t : R.RootedTree V) (T₀ : Finset (D × Bool)) (w₀ z : D × Bool) :
    t.phi T₀ w₀ z ≤ T₀.card := by
  classical
  unfold phi mass
  exact Finset.card_filter_le _ _

theorem downS_le_card (h₀ : t.vertM w₀ = t.root) (h₁ : w₀.2 = true) (hL₀ : t.IsLevel {w₀}) (hR : R.Planar)
    (hc : R.Connected) (hmk : ∀ y ∈ t.marks {w₀}, SsspFlow.ind T₀ y = 1)
    (hδ : ∀ y, y ∉ t.marks {w₀} → SsspFlow.ind T₀ y = δ) (v : V) : t.downS δ w₀ v ≤ T₀.card := by
  have h1 := phi_eq h₀ h₁ hL₀ hR hc hmk hδ (t.base w₀ v)
  unfold numF at h1
  rw [vertM_base h₀, offBy_self] at h1
  have h2 := phi_le_card t T₀ w₀ (t.base w₀ v)
  omega

theorem upS_le_card (h₀ : t.vertM w₀ = t.root) (h₁ : w₀.2 = true) (hL₀ : t.IsLevel {w₀}) (hR : R.Planar)
    (hc : R.Connected) (hmk : ∀ y ∈ t.marks {w₀}, SsspFlow.ind T₀ y = 1)
    (hδ : ∀ y, y ∉ t.marks {w₀} → SsspFlow.ind T₀ y = δ) (v : V) : t.upS δ v ≤ T₀.card + 2 := by
  by_cases hv : v = t.root
  · rw [hv, upS_root t δ]
    omega
  have h1 := phi_eq h₀ h₁ hL₀ hR hc hmk hδ (t.r0 v)
  unfold numF at h1
  rw [t.vertM_r0 hv] at h1
  have hb : t.base w₀ v = t.c1 v := if_neg hv
  rw [hb] at h1
  rw [upS_eq δ hv]
  have h2 := phi_le_card t T₀ w₀ (t.r0 v)
  omega

end Bounds

theorem le_two_mul_add (n : ℕ) : n ≤ 2 * n * n + 2 := by
  nlinarith [Nat.le_mul_self n]

/-- What the constant phases of a run compute. -/
structure ConstRun (N : Net (Fin n)) (B Tr : ℕ) (r : Fin n) (mem : ℕ → Fin n → Mem) : Prop where
  stable : ∀ {j k}, j < k → ∀ v, mem k v j = mem (j + 1) v j
  hDep : ∀ v, mem 2 v 1 = relaxSt B N.G
    (fun v => passIn (if v = r then 0 else n) (fun x _ => x) (depF r v)) Tr v
  hPar : ∀ v, mem 3 v 2 = relaxSt B N.G
    (fun v => passIn 0 (fun _ _ => (parR (N.rotList v) v (mem 2 v) : ℕ)) (fun _ => 0)) Tr v
  hUpF : ∀ v, mem 4 v 3 = relaxSt B N.G
    (fun v => passIn 0 (fun x _ => x) (upF 0 r (N.rotList v) v (mem 3 v))) Tr v
  hUpU : ∀ v, mem 5 v 4 = relaxSt B N.G
    (fun v => passIn 0 (fun x _ => x) (upF 1 r (N.rotList v) v (mem 4 v))) Tr v
  hDownF : ∀ v, mem 6 v 5 = relaxSt B N.G
    (fun v => passIn 0 (downM 0 3 r (N.rotList v) v (mem 5 v)) (downF r (N.rotList v) v (mem 5 v))) Tr v
  hDownU : ∀ v, mem 7 v 6 = relaxSt B N.G
    (fun v => passIn 0 (downM 1 4 r (N.rotList v) v (mem 6 v)) (downF r (N.rotList v) v (mem 6 v))) Tr v
  hRevF : ∀ v, mem 8 v 7 = relaxSt B N.G
    (fun v => passIn 0 (fun _ w => revM (numFL 0 3 5 r (N.rotList v) v (mem 7 v)) w) (fun _ => 0)) Tr v
  hRevU : ∀ v, mem 9 v 8 = relaxSt B N.G
    (fun v => passIn 0 (fun _ w => revM (numFL 1 4 6 r (N.rotList v) v (mem 8 v)) w) (fun _ => 0)) Tr v
  hRevP : ∀ v, mem 10 v 9 = relaxSt B N.G
    (fun v => passIn 0 (fun _ w => revM (numPL r (N.rotList v) v (mem 9 v)) w) (fun _ => 0)) Tr v

/-- The memory of a node after the constant phases. -/
structure ConstAt (N : Net (Fin n)) (hG : N.G.Connected) (r : Fin n) (d₀ : N.G.Dart) (m : Mem) (v : Fin n) :
    Prop where
  dep0 : m 1 0 = N.G.dist r v
  dep1 : ∀ u, N.G.Adj v u → m 1 (u + 1) = N.G.dist r u
  par1 : ∀ u, N.G.Adj u v → m 2 (u + 1) = N.parN r u
  upF1 : ∀ u, N.G.Adj u v → m 3 (u + 1) = (N.treeN hG r d₀).upS 0 u
  upU1 : ∀ u, N.G.Adj u v → m 4 (u + 1) = (N.treeN hG r d₀).upS 1 u
  downF0 : m 5 0 = (N.treeN hG r d₀).downS 0 (d₀, true) v
  downU0 : m 6 0 = (N.treeN hG r d₀).downS 1 (d₀, true) v
  revF : ∀ z : N.G.Dart × Bool, z.1.fst = v → revR 7 m (N.locN z) =
    (N.treeN hG r d₀).phi ((N.treeN hG r d₀).marks {(d₀, true)}) (d₀, true) (N.toRot.double.rev z)
  revU : ∀ z : N.G.Dart × Bool, z.1.fst = v → revR 8 m (N.locN z) =
    (N.treeN hG r d₀).phi Finset.univ (d₀, true) (N.toRot.double.rev z)
  revP : ∀ z : N.G.Dart × Bool, z.1.fst = v → revR 9 m (N.locN z) =
    pos ((N.treeN hG r d₀).tau (d₀, true)) (d₀, true) (N.toRot.double.rev z)

section Numbers

variable (M : Fin n → Mem) (hd₀ : d₀.fst = r) (hhd : d₀.snd = (N.rotList r).headD r)
  (hR : N.toRot.Planar) (hc : N.toRot.Connected)
  (hpM : ∀ v, parR (N.rotList v) v (M v) = N.parN r v)
  (hnM : ∀ v u, N.G.Adj u v → nparL (M v) u = N.parN r u)

include hd₀ hhd hR hc hpM hnM in
/-- The node sees the number of a dart on the first tour counting the marks. -/
theorem numF0_eq (hup : ∀ v u, N.G.Adj u v → M v 3 (u + 1) = (N.treeN hG r d₀).upS 0 u)
    (hdown : ∀ v, M v 5 0 = (N.treeN hG r d₀).downS 0 (d₀, true) v) {v : Fin n} {z : N.G.Dart × Bool}
    (hz : z.1.fst = v) : numFL 0 3 5 r (N.rotList v) v (M v) (N.locN z) =
      (N.treeN hG r d₀).phi ((N.treeN hG r d₀).marks {(d₀, true)}) (d₀, true) z := by
  have h₀ : (N.treeN hG r d₀).vertM (d₀, true) = (N.treeN hG r d₀).root := hd₀
  refine (numFL_eq hG M (hdown v) hz hpM hnM hup hd₀ hhd).trans ?_
  exact phi_eq h₀ rfl (isLevel_singleton h₀ rfl) hR hc (fun y hy => if_pos hy) (fun y hy => if_neg hy) z

include hd₀ hhd hR hc hpM hnM in
/-- The node sees the position of a dart on the first tour. -/
theorem numF1_eq (hup : ∀ v u, N.G.Adj u v → M v 4 (u + 1) = (N.treeN hG r d₀).upS 1 u)
    (hdown : ∀ v, M v 6 0 = (N.treeN hG r d₀).downS 1 (d₀, true) v) {v : Fin n} {z : N.G.Dart × Bool}
    (hz : z.1.fst = v) : numFL 1 4 6 r (N.rotList v) v (M v) (N.locN z) =
      (N.treeN hG r d₀).phi Finset.univ (d₀, true) z := by
  have h₀ : (N.treeN hG r d₀).vertM (d₀, true) = (N.treeN hG r d₀).root := hd₀
  refine (numFL_eq hG M (hdown v) hz hpM hnM hup hd₀ hhd).trans ?_
  exact phi_eq h₀ rfl (isLevel_singleton h₀ rfl) hR hc (fun y _ => if_pos (Finset.mem_univ y))
    (fun y _ => if_pos (Finset.mem_univ y)) z

include hd₀ hhd hR hc hpM hnM in
/-- The node sees the position of a dart on the tour through all darts. -/
theorem numPL_eq (hdep : ∀ v, M v 1 0 = N.G.dist r v)
    (hup : ∀ v u, N.G.Adj u v → M v 4 (u + 1) = (N.treeN hG r d₀).upS 1 u)
    (hdown : ∀ v, M v 6 0 = (N.treeN hG r d₀).downS 1 (d₀, true) v) {v : Fin n} {z : N.G.Dart × Bool}
    (hz : z.1.fst = v) : numPL r (N.rotList v) v (M v) (N.locN z) =
      pos ((N.treeN hG r d₀).tau (d₀, true)) (d₀, true) z := by
  subst hz
  have h₀ : (N.treeN hG r d₀).vertM (d₀, true) = (N.treeN hG r d₀).root := hd₀
  rw [pos_tau_eq h₀ rfl (isLevel_singleton h₀ rfl) hR hc z]
  have hF := fun y hy => numF1_eq (hG := hG) M hd₀ hhd hR hc hpM hnM hup hdown (v := z.1.fst) (z := y) hy
  unfold numPL numP
  by_cases hC : (N.treeN hG r d₀).IsC0 z
  · rw [if_pos ((isC0L_iff hG M hpM hnM rfl).2 hC), if_pos hC, ← loc_rot_inv z, hF _ (fst_rot_inv z), hdep]
    rfl
  · rw [if_neg (fun h => hC ((isC0L_iff hG M hpM hnM rfl).1 h)), if_neg hC, hF _ rfl, hdep]
    rfl

end Numbers

section Run

variable {Tr : ℕ} {mem : ℕ → Fin n → Mem}

include hG in
theorem dep0_run (h : ConstRun N B (Tr + 1) r mem) (hd : ∀ v, N.G.dist r v + 1 ≤ Tr)
    (hfit : ∀ x, x ≤ 2 * n * n + 2 → x < 2 ^ B) {k : ℕ} (hk : 2 ≤ k) (v : Fin n) :
    mem k v 1 0 = N.G.dist r v := by
  have e : mem k v 1 = _ := (h.stable (by omega) v).trans (h.hDep v)
  rw [e, dep_spec N hG (hfit n (le_two_mul_add n)), if_pos (by have := hd v; omega)]

include hG in
theorem dep1_run (h : ConstRun N B (Tr + 1) r mem) (hd : ∀ v, N.G.dist r v + 1 ≤ Tr)
    (hfit : ∀ x, x ≤ 2 * n * n + 2 → x < 2 ^ B) {k : ℕ} (hk : 2 ≤ k) {v u : Fin n} (hadj : N.G.Adj u v) :
    mem k v 1 (u + 1) = N.G.dist r u := by
  have e : mem k v 1 = _ := (h.stable (by omega) v).trans (h.hDep v)
  rw [e]
  have hs : relaxSt B N.G (fun v => passIn (if v = r then 0 else n) (fun x _ => x) (depF r v)) Tr u 0 =
      N.G.dist r u := by
    rw [dep_spec N hG (hfit n (le_two_mul_add n)), if_pos (by have := hd u; omega)]
  have hlt : N.G.dist r u ≤ 2 * n * n + 2 := by
    have := dist_lt_n N hG r u
    have := le_two_mul_add n
    omega
  refine (pass_nbr N.G _ (fun _ x _ => x) _ Tr hadj ?_).trans hs
  show relaxSt B N.G _ Tr u 0 < _
  rw [hs]
  exact hfit _ hlt

include hG in
theorem hpar_run (h : ConstRun N B (Tr + 1) r mem) (hd : ∀ v, N.G.dist r v + 1 ≤ Tr)
    (hfit : ∀ x, x ≤ 2 * n * n + 2 → x < 2 ^ B) {k : ℕ} (hk : 2 ≤ k) (v : Fin n) :
    parR (N.rotList v) v (mem k v) = N.parN r v :=
  parR_eq (dep0_run hG h hd hfit hk v) fun u hu => dep1_run hG h hd hfit hk hu.symm

include hG in
theorem hnp_run (h : ConstRun N B (Tr + 1) r mem) (hd : ∀ v, N.G.dist r v + 1 ≤ Tr)
    (hfit : ∀ x, x ≤ 2 * n * n + 2 → x < 2 ^ B) {k : ℕ} (hk : 3 ≤ k) (v u : Fin n) (hadj : N.G.Adj u v) :
    nparL (mem k v) u = N.parN r u := by
  have e : mem k v 2 = _ := (h.stable (by omega) v).trans (h.hPar v)
  unfold nparL
  rw [e]
  have hlt : ∀ x : Fin n, (x : ℕ) ≤ 2 * n * n + 2 := fun x => by
    have := x.2
    have := le_two_mul_add n
    omega
  refine (pass_nbr N.G _ (fun v _ _ => (parR (N.rotList v) v (mem 2 v) : ℕ)) _ Tr hadj (hfit _ (hlt _))).trans ?_
  show ((parR (N.rotList u) u (mem 2 u) : Fin n) : ℕ) = _
  rw [hpar_run hG h hd hfit le_rfl u]

/-- The value of a node in a pass up, as received by a neighbour. -/
theorem up_nbr (M : Fin n → Mem) (hpar : ∀ v, parR (N.rotList v) v (M v) = N.parN r v)
    (hnp : ∀ v u, N.G.Adj u v → nparL (M v) u = N.parN r u) (δ : ℕ)
    (hbd : ∀ v, (N.treeN hG r d₀).upS δ v < 2 ^ B) (hd : (N.treeN hG r d₀).depBd < Tr)
    {v u : Fin n} (hadj : N.G.Adj u v) :
    relaxSt B N.G (fun v => passIn 0 (fun x _ => x) (upF δ r (N.rotList v) v (M v))) (Tr + 1) v (u + 1) =
      (N.treeN hG r d₀).upS δ u := by
  have hs : relaxSt B N.G (fun v => passIn 0 (fun x _ => x) (upF δ r (N.rotList v) v (M v))) Tr u 0 =
      (N.treeN hG r d₀).upS δ u := up_spec hG M hpar hnp δ hbd _ Tr u rfl (by omega)
  refine (pass_nbr N.G _ (fun _ x _ => x) _ Tr hadj ?_).trans hs
  show relaxSt B N.G _ Tr u 0 < _
  rw [hs]
  exact hbd u

include hG in
theorem depBd_lt (hd : ∀ v, N.G.dist r v + 1 ≤ Tr) : (N.treeN hG r d₀).depBd < Tr := by
  have h0 := hd r
  have h1 : (N.treeN hG r d₀).depBd ≤ Tr - 1 := Finset.sup_le fun v _ => by
    have := hd v
    show N.G.dist r v ≤ _
    omega
  omega

/-- A run of the constant phases leaves the numbers of the tree in the memories. -/
theorem constAt_of_run (h : ConstRun N B (Tr + 1) r mem) (hd : ∀ v, N.G.dist r v + 1 ≤ Tr)
    (hfit : ∀ x, x ≤ 2 * n * n + 2 → x < 2 ^ B)
    (hpair : ∀ a b, a ≤ 2 * n * n + 2 → b ≤ 2 * n * n + 2 → Nat.pair a b < 2 ^ B)
    (hd₀ : d₀.fst = r) (hhd : d₀.snd = (N.rotList r).headD r) (hR : N.toRot.Planar)
    (hc : N.toRot.Connected) {k : ℕ} (hk : 10 ≤ k) (v : Fin n) : ConstAt N hG r d₀ (mem k v) v := by
  have h₀ : (N.treeN hG r d₀).vertM (d₀, true) = (N.treeN hG r d₀).root := hd₀
  have hL₀ := isLevel_singleton h₀ rfl
  have hcard : ∀ T : Finset (N.G.Dart × Bool), T.card ≤ 2 * n * n := fun T =>
    (Finset.card_le_univ T).trans N.card_le
  have hTr := depBd_lt (d₀ := d₀) hG hd
  have hP : ∀ {k}, 2 ≤ k → ∀ v, parR (N.rotList v) v (mem k v) = N.parN r v := fun hk =>
    hpar_run hG h hd hfit hk
  have hQ : ∀ {k}, 3 ≤ k → ∀ v u, N.G.Adj u v → nparL (mem k v) u = N.parN r u := fun hk =>
    hnp_run hG h hd hfit hk
  have hUF : ∀ v, (N.treeN hG r d₀).upS 0 v ≤ 2 * n * n + 2 := fun v =>
    (upS_le_card h₀ rfl hL₀ hR hc (fun y hy => if_pos hy) (fun y hy => if_neg hy) v).trans
      (Nat.add_le_add_right (hcard _) 2)
  have hUU : ∀ v, (N.treeN hG r d₀).upS 1 v ≤ 2 * n * n + 2 := fun v =>
    (upS_le_card (T₀ := Finset.univ) h₀ rfl hL₀ hR hc (fun y _ => if_pos (Finset.mem_univ y))
      (fun y _ => if_pos (Finset.mem_univ y)) v).trans (Nat.add_le_add_right (hcard _) 2)
  have hDF : ∀ v, (N.treeN hG r d₀).downS 0 (d₀, true) v ≤ 2 * n * n + 2 := fun v =>
    (downS_le_card h₀ rfl hL₀ hR hc (fun y hy => if_pos hy) (fun y hy => if_neg hy) v).trans
      ((hcard _).trans (by omega))
  have hDU : ∀ v, (N.treeN hG r d₀).downS 1 (d₀, true) v ≤ 2 * n * n + 2 := fun v =>
    (downS_le_card (T₀ := Finset.univ) h₀ rfl hL₀ hR hc (fun y _ => if_pos (Finset.mem_univ y))
      (fun y _ => if_pos (Finset.mem_univ y)) v).trans ((hcard _).trans (by omega))
  have hupF : ∀ {k}, 4 ≤ k → ∀ v u, N.G.Adj u v → mem k v 3 (u + 1) = (N.treeN hG r d₀).upS 0 u :=
    fun {k'} hk v u hu => by
      have e : mem k' v 3 = _ := (h.stable (by omega) v).trans (h.hUpF v)
      rw [e]
      exact up_nbr hG (mem 3) (hP (by omega)) (hQ le_rfl) 0 (fun v => hfit _ (hUF v)) hTr hu
  have hupU : ∀ {k}, 5 ≤ k → ∀ v u, N.G.Adj u v → mem k v 4 (u + 1) = (N.treeN hG r d₀).upS 1 u :=
    fun {k'} hk v u hu => by
      have e : mem k' v 4 = _ := (h.stable (by omega) v).trans (h.hUpU v)
      rw [e]
      exact up_nbr hG (mem 4) (hP (by omega)) (hQ (by omega)) 1 (fun v => hfit _ (hUU v)) hTr hu
  have hdownF : ∀ {k}, 6 ≤ k → ∀ v, mem k v 5 0 = (N.treeN hG r d₀).downS 0 (d₀, true) v := fun {k'} hk v => by
    have e : mem k' v 5 = _ := (h.stable (by omega) v).trans (h.hDownF v)
    rw [e]
    exact down_spec hG (mem 5) (hP (by omega)) (hQ (by omega)) (hupF (by omega)) hd₀ hhd
      (fun v => hfit _ (hDF v)) _ (Tr + 1) v rfl (by have := hd v; show N.G.dist r v < _; omega)
  have hdownU : ∀ {k}, 7 ≤ k → ∀ v, mem k v 6 0 = (N.treeN hG r d₀).downS 1 (d₀, true) v := fun {k'} hk v => by
    have e : mem k' v 6 = _ := (h.stable (by omega) v).trans (h.hDownU v)
    rw [e]
    exact down_spec hG (mem 6) (hP (by omega)) (hQ (by omega)) (hupU (by omega)) hd₀ hhd
      (fun v => hfit _ (hDU v)) _ (Tr + 1) v rfl (by have := hd v; show N.G.dist r v < _; omega)
  have hF0 : ∀ {k}, 6 ≤ k → ∀ {v} {z : N.G.Dart × Bool}, z.1.fst = v →
      numFL 0 3 5 r (N.rotList v) v (mem k v) (N.locN z) =
        (N.treeN hG r d₀).phi ((N.treeN hG r d₀).marks {(d₀, true)}) (d₀, true) z := fun hk _ _ hz =>
    numF0_eq (hG := hG) (mem _) hd₀ hhd hR hc (hP (by omega)) (hQ (by omega)) (hupF (by omega))
      (hdownF hk) hz
  have hF1 : ∀ {k}, 7 ≤ k → ∀ {v} {z : N.G.Dart × Bool}, z.1.fst = v →
      numFL 1 4 6 r (N.rotList v) v (mem k v) (N.locN z) =
        (N.treeN hG r d₀).phi Finset.univ (d₀, true) z := fun hk _ _ hz =>
    numF1_eq (hG := hG) (mem _) hd₀ hhd hR hc (hP (by omega)) (hQ (by omega)) (hupU (by omega))
      (hdownU hk) hz
  have hPos : ∀ {k}, 7 ≤ k → ∀ {v} {z : N.G.Dart × Bool}, z.1.fst = v →
      numPL r (N.rotList v) v (mem k v) (N.locN z) =
        pos ((N.treeN hG r d₀).tau (d₀, true)) (d₀, true) z := fun hk _ _ hz =>
    numPL_eq (hG := hG) (mem _) hd₀ hhd hR hc (hP (by omega)) (hQ (by omega))
      (fun v => dep0_run hG h hd hfit (by omega) v) (hupU (by omega)) (hdownU hk) hz
  have hphiF : ∀ z, (N.treeN hG r d₀).phi ((N.treeN hG r d₀).marks {(d₀, true)}) (d₀, true) z ≤
      2 * n * n + 2 := fun z => (phi_le_card _ _ _ _).trans ((hcard _).trans (by omega))
  have hphiU : ∀ z, (N.treeN hG r d₀).phi Finset.univ (d₀, true) z ≤ 2 * n * n + 2 := fun z =>
    (phi_le_card _ _ _ _).trans ((hcard _).trans (by omega))
  have hτ : ∀ z, pos ((N.treeN hG r d₀).tau (d₀, true)) (d₀, true) z ≤ 2 * n * n + 2 := fun z => by
    have h1 := pos_lt_card_univ (f := (N.treeN hG r d₀).tau (d₀, true)) (fconnect_tau h₀ rfl) (x := (d₀, true)) (y := z)
    have h2 : Fintype.card (N.G.Dart × Bool) ≤ 2 * n * n := N.card_le
    omega
  have hread : ∀ {val : Fin n → Fin n × Bool → ℕ},
      (∀ y : N.G.Dart × Bool, val y.1.fst (N.locN y) ≤ 2 * n * n + 2) → ∀ {j : ℕ} {z : N.G.Dart × Bool},
      (mem k z.1.fst j = relaxSt B N.G (fun v => passIn 0 (fun _ w => revM (val v) w) (fun _ => 0))
        (Tr + 1) z.1.fst) → revR j (mem k z.1.fst) (N.locN z) = val z.1.snd (N.locN (N.toRot.double.rev z)) :=
    fun hv _ z hm => rev_spec (hfit := hpair _ _ (hv (z.1.symm, false)) (hv (z.1.symm, true))) hm
  refine
    { dep0 := dep0_run hG h hd hfit (by omega) v
      dep1 := fun u hu => dep1_run hG h hd hfit (by omega) hu.symm
      par1 := fun u hu => hQ (by omega) v u hu
      upF1 := hupF (by omega) v
      upU1 := hupU (by omega) v
      downF0 := hdownF (by omega) v
      downU0 := hdownU (by omega) v
      revF := fun z hz => ?_
      revU := fun z hz => ?_
      revP := fun z hz => ?_ }
  · subst hz
    have hm := (h.stable (j := 7) (k := k) (by omega) z.1.fst).trans (h.hRevF z.1.fst)
    refine (hread (val := fun v => numFL 0 3 5 r (N.rotList v) v (mem 7 v)) (fun y => ?_) hm).trans
      (hF0 (by omega) rfl)
    exact (hF0 (by omega) rfl).le.trans (hphiF y)
  · subst hz
    have hm := (h.stable (j := 8) (k := k) (by omega) z.1.fst).trans (h.hRevU z.1.fst)
    refine (hread (val := fun v => numFL 1 4 6 r (N.rotList v) v (mem 8 v)) (fun y => ?_) hm).trans
      (hF1 (by omega) rfl)
    exact (hF1 (by omega) rfl).le.trans (hphiU y)
  · subst hz
    have hm := (h.stable (j := 9) (k := k) (by omega) z.1.fst).trans (h.hRevP z.1.fst)
    refine (hread (val := fun v => numPL r (N.rotList v) v (mem 9 v)) (fun y => ?_) hm).trans
      (hPos (by omega) rfl)
    exact (hPos (by omega) rfl).le.trans (hτ y)

end Run

section Const

variable {m : Fin n → Mem} (hC : ∀ v, ConstAt N hG r d₀ (m v) v)

include hC in
theorem constAt_par (v : Fin n) : parR (N.rotList v) v (m v) = N.parN r v :=
  parR_eq (hC v).dep0 (hC v).dep1

include hC in
theorem constAt_np (v u : Fin n) (hu : N.G.Adj u v) : nparL (m v) u = N.parN r u := (hC v).par1 u hu

variable (hd₀ : d₀.fst = r) (hhd : d₀.snd = (N.rotList r).headD r) (hR : N.toRot.Planar)
  (hc : N.toRot.Connected)

include hC hd₀ hhd hR hc in
theorem constAt_numF0 {v : Fin n} {z : N.G.Dart × Bool} (hz : z.1.fst = v) :
    numFL 0 3 5 r (N.rotList v) v (m v) (N.locN z) =
      (N.treeN hG r d₀).phi ((N.treeN hG r d₀).marks {(d₀, true)}) (d₀, true) z :=
  numF0_eq (hG := hG) m hd₀ hhd hR hc (constAt_par hG hC) (constAt_np hG hC)
    (fun v => (hC v).upF1) (fun v => (hC v).downF0) hz

include hC hd₀ hhd hR hc in
theorem constAt_numF1 {v : Fin n} {z : N.G.Dart × Bool} (hz : z.1.fst = v) :
    numFL 1 4 6 r (N.rotList v) v (m v) (N.locN z) =
      (N.treeN hG r d₀).phi Finset.univ (d₀, true) z :=
  numF1_eq (hG := hG) m hd₀ hhd hR hc (constAt_par hG hC) (constAt_np hG hC)
    (fun v => (hC v).upU1) (fun v => (hC v).downU0) hz

include hC hd₀ hhd hR hc in
theorem constAt_numP {v : Fin n} {z : N.G.Dart × Bool} (hz : z.1.fst = v) :
    numPL r (N.rotList v) v (m v) (N.locN z) =
      pos ((N.treeN hG r d₀).tau (d₀, true)) (d₀, true) z :=
  numPL_eq (hG := hG) m hd₀ hhd hR hc (constAt_par hG hC) (constAt_np hG hC) (fun v => (hC v).dep0)
    (fun v => (hC v).upU1) (fun v => (hC v).downU0) hz

end Const

end SsspFlow.Congest
