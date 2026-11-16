import SsspFlow.CutPathKap
import SsspFlow.MinFlood
import SsspFlow.GHatLevelLen
import SsspFlow.GHatTheoremD

/-!
# The indices of the corners of the cut path at the nodes

Three phases in the message model: the nodes simulate the two runs along the parent chain of the
dual network, then every node sends each neighbour the count of their common dart, capped at `n²`, and
whether it is the first dart of the source or of the target, and finally the length `m`, which the
source holds at the corner of its first dart, is flooded. Each node then knows, for every dart at it,
the indices of the corners `p_τ^0` and `p_τ^1` of a shortest cut path at its corners, and `m`.

* `dualE`: the identifiers of the dual network.
* `dartMsg`: the message on a dart, with `msgC`, `msgS`, `msgT` to read it.
* `cpAlg`, `cpOut`: the three phases and what a node reads from its state.
* `cpAlg_spec`: after `T₁ + (1 + D)` rounds every node holds `m` and the indices of the corners of its
  darts on a shortest cut path from the first dart of `s` to the first dart of `t`.
-/

set_option autoImplicit false

open Cslib.Congest Cslib.Congest.Algorithm

namespace SsspFlow.Congest

open XNode Kind
open scoped ENNReal

/-- The identifiers of the dual network. -/
noncomputable def dualE (n : ℕ) : Fin n × Fin n × Kind ≃ Fin (n * (n * 5)) :=
  Fintype.equivFinOfCardEq (by simp [Kind.card_eq])

/-- The message on a dart: its count, and whether it is the first dart of the source or of the
target. -/
def dartMsg (c : ℕ∞) (fs ft : Bool) : ℕ := 4 * encC c + 2 * fs.toNat + ft.toNat

/-- The count in a message. -/
def msgC (k : ℕ) : ℕ∞ := decC (k / 4)

/-- The flag of the source in a message. -/
def msgS (k : ℕ) : Bool := decide (k / 2 % 2 = 1)

/-- The flag of the target in a message. -/
def msgT (k : ℕ) : Bool := decide (k % 2 = 1)

theorem msg_dartMsg (c : ℕ∞) (fs ft : Bool) :
    msgC (dartMsg c fs ft) = c ∧ msgS (dartMsg c fs ft) = fs ∧ msgT (dartMsg c fs ft) = ft := by
  unfold msgC msgS msgT dartMsg
  refine ⟨?_, ?_, ?_⟩
  · rw [show (4 * encC c + 2 * fs.toNat + ft.toNat) / 4 = encC c by
      cases fs <;> cases ft <;> simp <;> omega]
    exact decC_encC c
  · cases fs <;> cases ft <;> simp <;> omega
  · cases fs <;> cases ft <;> simp <;> omega

theorem encC_min_le (c : ℕ∞) (L : ℕ) : encC (min c L) ≤ L + 1 := by
  unfold encC
  split_ifs with h
  · omega
  · have : (min c L).toNat ≤ L := by
      have hle : min c (L : ℕ∞) ≤ L := min_le_right _ _
      exact ENat.toNat_le_of_le_coe hle
    omega

variable {n : ℕ}

/-- Whether the dart from `w` to `u` is the first dart of the source, as `w` knows it. -/
def fsOf (h : DualHostIn (Fin n)) (w u : Fin n) : Bool := h.isS && decide (u = h.nbrs.headD w)

/-- Whether the dart from `w` to `u` is the first dart of the target, as `w` knows it. -/
def ftOf (h : DualHostIn (Fin n)) (w u : Fin n) : Bool := h.isT && decide (u = h.nbrs.headD w)

/-- The local data of a node after the runs along the chain: its input, the counts of its darts and
the count at the corner of its first dart. -/
structure CpLoc (n : ℕ) where
  /-- The input. -/
  h : DualHostIn (Fin n)
  /-- The counts of the darts, capped at `n²`. -/
  cnt : Fin n → ℕ∞
  /-- The count at the corner of the first dart. -/
  root : ℕ∞

/-- What a node reads from its state: `m` and the indices of the corners of the darts out of it and
into it. -/
def cpRead (w : Fin n) (q : CpLoc n) (rc : Fin n → Option ℕ) (m : ℕ) :
    ℕ × (Fin n → Bool → (ℕ → Bool) × (ℕ → Bool)) × (Fin n → Bool → (ℕ → Bool) × (ℕ → Bool)) :=
  (m, fun u b => kapOf m (q.cnt u) (msgC ((rc u).getD 0)) (fsOf q.h w u) (ftOf q.h w u) (msgS ((rc u).getD 0)) b,
    fun u b => kapOf m (msgC ((rc u).getD 0)) (q.cnt u) (msgS ((rc u).getD 0)) (msgT ((rc u).getD 0))
      (fsOf q.h w u) b)

theorem adj_headD (N : Net (Fin n)) (hN : ∀ v, ∃ u, N.G.Adj v u) (v : Fin n) :
    N.G.Adj v ((N.rotList v).headD v) := by
  obtain ⟨u, hu⟩ := hN v
  have hm : u ∈ N.rotList v := (N.mem_rotList _ _).2 hu
  cases hl : N.rotList v with
  | nil => rw [hl] at hm; simp at hm
  | cons a l =>
    have : a ∈ N.rotList v := by rw [hl]; exact List.mem_cons_self
    simpa using (N.mem_rotList _ _).1 this

theorem fsOf_iff (N : Net (Fin n)) (g : Fin n → Fin n → ℕ) {s t : Fin n}
    (hs : N.G.Adj s ((N.rotList s).headD s)) (d : N.G.Dart) :
    fsOf (dualHostOf N g s t d.fst) d.fst d.snd = true ↔ d = firstDart N hs := by
  unfold fsOf dualHostOf firstDart
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨h1, h2⟩
    subst h1
    exact SimpleGraph.Dart.ext _ _ (Prod.ext rfl h2)
  · rintro rfl
    exact ⟨rfl, rfl⟩

theorem ftOf_iff (N : Net (Fin n)) (g : Fin n → Fin n → ℕ) {s t : Fin n}
    (ht : N.G.Adj t ((N.rotList t).headD t)) (d : N.G.Dart) :
    ftOf (dualHostOf N g s t d.fst) d.fst d.snd = true ↔ d = firstDart N ht := by
  unfold ftOf dualHostOf firstDart
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨h1, h2⟩
    subst h1
    exact SimpleGraph.Dart.ext _ _ (Prod.ext rfl h2)
  · rintro rfl
    exact ⟨rfl, rfl⟩

theorem min_coe_eq_iff {c : ℕ∞} {k L : ℕ} (hk : k < L) : min c (L : ℕ∞) = k ↔ c = k := by
  rcases le_total c L with h | h
  · rw [min_eq_left h]
  · rw [min_eq_right h]
    constructor
    · intro e; exact absurd (by exact_mod_cast e : L = k) (by omega)
    · intro e; subst e; exact absurd (by exact_mod_cast h : L ≤ k) (by omega)

theorem sq_lt_pow (n : ℕ) : n * n < 2 ^ (2 * logN n) := by
  have h : n + 2 < 2 ^ logN n := by unfold logN; exact Nat.lt_pow_succ_log_self (by norm_num) _
  rw [two_mul, pow_add]
  exact Nat.mul_lt_mul'' (by omega) (by omega)

section Alg

variable (hE : ExactSsspBound) (K D n : ℕ)

/-- The rounds of one run of the oracle on the dual network. -/
noncomputable abbrev cpT₁ : ℕ := hE.cC K * logN (n * (n * 5)) ^ hE.cc K * (5 * D + 6)

/-- The width of the oracle on the dual network. -/
noncomputable abbrev cpBo : ℕ := hE.cC K * logN (n * (n * 5)) ^ hE.cc K

/-- The width of the three phases. -/
noncomputable abbrev cpBx : ℕ := ((cpBo hE K n + 3) + (cpBo hE K n + 3)) + (2 * logN n + 4)

/-- The runs along the chain of the dual network, at the hosts. -/
noncomputable abbrev cpChain :=
  chainHost (dualE n) (chainAlg (hE.alg K (n * (n * 5)) (5 * D + 6) (by omega))
    (hE.out K (n * (n * 5)) (5 * D + 6) (by omega)) (cpT₁ hE K D n))

/-- The out-of-chain count cap. -/
abbrev cpL : ℕ := n * n

/-- **The three phases.** The runs along the chain of the dual network at the hosts; one round in which
every node sends each neighbour the count of their common dart, capped at `n²`, and the two flags; and
the flood of the count at the corner of the first dart of the source. -/
noncomputable def cpAlg :=
  ((cpChain hE K D n).widen (Nat.le_add_right ((cpBo hE K n + 3) + (cpBo hE K n + 3)) (2 * logN n + 4))).seq
    (cpT₁ hE K D n + (1 + (cpT₁ hE K D n + cpT₁ hE K D n)))
    (fun w s => (⟨s.1,
      fun u => min ((chainOut (hE.out K (n * (n * 5)) (5 * D + 6) (by omega)) (dualE n (w, u, m1))
        (s.2 (dualE n (w, u, m1)))).2.1.1) ((cpL n : ℕ) : ℕ∞),
      (chainOut (hE.out K (n * (n * 5)) (5 * D + 6) (by omega)) (dualE n (w, s.1.nbrs.headD w, corner))
        (s.2 (dualE n (w, s.1.nbrs.headD w, corner)))).2.1.1⟩ : CpLoc n))
    ((((exchTo (Fin n) (cpBx hE K n)).keep
        (fun w (q : CpLoc n) => fun u => dartMsg (q.cnt u) (fsOf q.h w u) (ftOf q.h w u))).seq 1
      (fun _ s => (s.1, s.2.2))
      ((minFlood (cpBx hE K n)).keep
        (fun _ (r : CpLoc n × (Fin n → Option ℕ)) => if r.1.h.isS then r.1.root.toNat else cpL n))))

end Alg

/-- What a node reads from the state of the three phases. -/
def cpOut {α β : Type} (w : Fin n) :
    α ⊕ (β ⊕ ((CpLoc n × (Fin n → Option ℕ)) × (ℕ × ℕ × (ℕ × (Fin n → Option ℕ))))) →
      ℕ × (Fin n → Bool → (ℕ → Bool) × (ℕ → Bool)) × (Fin n → Bool → (ℕ → Bool) × (ℕ → Bool))
  | .inr (.inr p) => cpRead w p.1.1 p.1.2 p.2.1
  | _ => (0, fun _ _ => (fun _ => false, fun _ => false), fun _ _ => (fun _ => false, fun _ => false))

open Classical in
/-- **The indices of the corners at the nodes.** Assuming the Exact SSSP bound, for costs from `1` to
`(n' + 2) ^ K` with `n' = 5 n²` and two nodes `s ≠ t` of a planar connected network of diameter at most
`D`, after the three phases the dual has a cut path from the first dart of `s` to the first dart of `t`
that is shortest for the costs, every node holds its length `m`, and every node holds the indices of the
corners `p_τ^0` and `p_τ^1` at the corners of the darts out of it and into it. -/
theorem cpAlg_spec (hE : ExactSsspBound) (K D : ℕ) (N : Net (Fin n)) (g : Fin n → Fin n → ℕ) {s t : Fin n}
    (hs : N.G.Adj s ((N.rotList s).headD s)) (ht : N.G.Adj t ((N.rotList t).headD t)) (hst : s ≠ t)
    (hP : N.toRot.Planar) (hN : ∀ v, ∃ u, N.G.Adj v u) (hDi : N.DiamLE D) (hc : N.toRot.Connected)
    (hgK : ∀ u v, g u v ≤ (n * (n * 5) + 2) ^ K) (hg1 : ∀ d : N.G.Dart, 1 ≤ g d.fst d.snd) :
    let st := (cpAlg hE K D n).run N.G (dualHostOf N g s t)
      (cpT₁ hE K D n + (1 + (cpT₁ hE K D n + cpT₁ hE K D n)) + (1 + D))
    ∃ C : N.toRot.dual.CutPath, C.cs = firstDart N hs ∧ C.ct = firstDart N ht ∧
      (∀ q, N.toRot.dual.IsWalk (C.v 0) q (C.v C.m) →
        C.pos (fun x => g x.fst x.snd) C.m ≤ (q.map fun x => g x.fst x.snd).sum) ∧
      (∀ w, (cpOut w (st w)).1 = C.m) ∧
      (∀ (d : N.G.Dart) b τ, ((((cpOut d.fst (st d.fst)).2.1 d.snd b).1 τ = true ↔ (d, b) = C.k 0 τ) ∧
        (((cpOut d.fst (st d.fst)).2.1 d.snd b).2 τ = true ↔ (d, b) = C.k 1 τ))) ∧
      (∀ (d : N.G.Dart) b τ, ((((cpOut d.snd (st d.snd)).2.2 d.fst b).1 τ = true ↔ (d, b) = C.k 0 τ) ∧
        (((cpOut d.snd (st d.snd)).2.2 d.fst b).2 τ = true ↔ (d, b) = C.k 1 τ))) := by
  intro st
  set e := dualE n with he
  set T₁ := cpT₁ hE K D n
  set out := hE.out K (n * (n * 5)) (5 * D + 6) (by omega)
  set inp := dualHostOf N g s t with hinp
  have hcp := chainHost_cutPath e hE K D N g hs ht hst hP hN hDi hc hgK hg1
  simp only at hcp
  obtain ⟨C, hcs, hct, hmin, hidx, hpast, hroot⟩ := hcp
  set S₁ := (cpChain hE K D n).run N.G inp (T₁ + (1 + (T₁ + T₁))) with hS₁
  have hS1 : ∀ v, (S₁ v).1 = inp v := fun v => (chainHost_sim _ hs ht _ v).1
  have hm : C.m + 1 ≤ n * n := RotSystem.RData.cutPath_m_lt C
  -- the counts
  set cnt' : N.G.Dart → ℕ∞ := fun x => min ((chainOut out (idx N e m1 x)
    ((S₁ (e.symm (idx N e m1 x)).1).2 (idx N e m1 x))).2.1.1) ((cpL n : ℕ) : ℕ∞) with hcnt'
  have hidx' : ∀ x τ, τ < C.m → (C.e τ = x ↔ cnt' x = ((C.m - 1 - τ : ℕ) : ℕ∞)) := fun x τ hτ => by
    rw [hidx x τ hτ, hcnt', min_coe_eq_iff (by simp only [cpL]; omega)]
  -- the phases
  set I₂ : Fin n → CpLoc n := fun w => ⟨(S₁ w).1,
      fun u => min ((chainOut out (e (w, u, m1)) ((S₁ w).2 (e (w, u, m1)))).2.1.1) ((cpL n : ℕ) : ℕ∞),
      (chainOut out (e (w, (S₁ w).1.nbrs.headD w, corner)) ((S₁ w).2 (e (w, (S₁ w).1.nbrs.headD w, corner)))).2.1.1⟩
    with hI₂
  set M₂ : Fin n → Fin n → ℕ := fun w u => dartMsg ((I₂ w).cnt u) (fsOf (I₂ w).h w u) (ftOf (I₂ w).h w u)
    with hM₂
  set R : Fin n → Fin n → Option ℕ := fun w u => if N.G.Adj u w then some (M₂ u w) else none with hR
  set X₀ : Fin n → ℕ := fun w => if (I₂ w).h.isS then (I₂ w).root.toNat else cpL n with hX₀
  have hpow : 2 ^ (2 * logN n) ≤ 2 ^ cpBx hE K n := Nat.pow_le_pow_right (by norm_num) (by
    show 2 * logN n ≤ ((cpBo hE K n + 3) + (cpBo hE K n + 3)) + (2 * logN n + 4); omega)
  have hsq := sq_lt_pow n
  have hmsg : ∀ u w, M₂ u w < 2 ^ cpBx hE K n := fun u w => by
    have h1 := encC_min_le ((chainOut out (e (u, w, m1)) ((S₁ u).2 (e (u, w, m1)))).2.1.1) (cpL n)
    have h2 : M₂ u w ≤ 4 * (cpL n + 1) + 3 := by
      have e0 : (I₂ u).cnt w = min ((chainOut out (e (u, w, m1)) ((S₁ u).2 (e (u, w, m1)))).2.1.1)
          ((cpL n : ℕ) : ℕ∞) := rfl
      simp only [hM₂, dartMsg, e0]
      have hb1 : (fsOf (I₂ u).h u w).toNat ≤ 1 := Bool.toNat_le _
      have hb2 : (ftOf (I₂ u).h u w).toNat ≤ 1 := Bool.toNat_le _
      omega
    have h3 : 2 ^ (2 * logN n + 4) ≤ 2 ^ cpBx hE K n := Nat.pow_le_pow_right (by norm_num) (by
      show 2 * logN n + 4 ≤ ((cpBo hE K n + 3) + (cpBo hE K n + 3)) + (2 * logN n + 4); omega)
    have h4 : 2 ^ (2 * logN n + 4) = 2 ^ (2 * logN n) * 16 := by rw [pow_add]; norm_num
    simp only [cpL] at h2
    omega
  have hrun : ∀ w, st w = .inr (.inr ((I₂ w, R w), (minFlood (cpBx hE K n)).run N.G X₀ D w)) := by
    intro w
    simp only [st, cpAlg]
    rw [run_seq]
    simp only [run_widen]
    rw [run_seq]
    simp only [run_keep]
    rw [run_exchTo N.G _ hmsg]
  have hroot' : X₀ s = C.m := by
    simp only [hX₀, hI₂, hS1, hinp, dualHostOf, decide_true, ite_true]
    have h := hroot
    have e1 : idx N e corner (firstDart N hs) = e (s, (N.rotList s).headD s, corner) := rfl
    rw [e1, Equiv.symm_apply_apply] at h
    rw [h]
    rfl
  have hge : ∀ u, C.m ≤ X₀ u := fun u => by
    by_cases hu : u = s
    · rw [hu, hroot']
    · have : (I₂ u).h.isS = false := by simp [hI₂, hS1, hinp, dualHostOf, hu]
      simp only [hX₀, this, Bool.false_eq_true, ite_false, cpL]
      omega
  have hbits : ∀ v, X₀ v < 2 ^ cpBx hE K n := fun v => by
    have : X₀ v ≤ cpL n := by
      by_cases hu : v = s
      · rw [hu, hroot']; simp only [cpL]; omega
      · have : (I₂ v).h.isS = false := by simp [hI₂, hS1, hinp, dualHostOf, hu]
        simp only [hX₀, this]; rfl
    exact lt_of_le_of_lt this (lt_of_lt_of_le hsq hpow)
  have hfl : ∀ w, ((minFlood (cpBx hE K n)).run N.G X₀ D w).1 = C.m :=
    fun w => run_minFlood N.G X₀ hbits hDi hge ⟨s, hroot'⟩ w
  have hout : ∀ w, cpOut w (st w) = cpRead w (I₂ w) (R w) C.m := fun w => by
    rw [hrun w]
    show cpRead w (I₂ w) (R w) _ = _
    rw [hfl]
  -- the counts at the nodes
  have hcO : ∀ d : N.G.Dart, (I₂ d.fst).cnt d.snd = cnt' d := fun d => by
    simp only [hI₂, hcnt', idx, Equiv.symm_apply_apply]
  have hcR : ∀ d : N.G.Dart, msgC ((R d.snd d.fst).getD 0) = cnt' d ∧
      msgS ((R d.snd d.fst).getD 0) = fsOf (I₂ d.fst).h d.fst d.snd ∧
      msgT ((R d.snd d.fst).getD 0) = ftOf (I₂ d.fst).h d.fst d.snd := fun d => by
    simp only [hR, if_pos d.adj, Option.getD_some, hM₂]
    obtain ⟨h1, h2, h3⟩ := msg_dartMsg ((I₂ d.fst).cnt d.snd) (fsOf (I₂ d.fst).h d.fst d.snd)
      (ftOf (I₂ d.fst).h d.fst d.snd)
    exact ⟨h1.trans (hcO d), h2, h3⟩
  have hfs : ∀ d : N.G.Dart, fsOf (I₂ d.fst).h d.fst d.snd = true ↔ d = C.cs := fun d => by
    rw [hcs]; simp only [hI₂, hS1]; exact fsOf_iff N g hs d
  have hft : ∀ d : N.G.Dart, ftOf (I₂ d.fst).h d.fst d.snd = true ↔ d = C.ct := fun d => by
    rw [hct]; simp only [hI₂, hS1]; exact ftOf_iff N g ht d
  refine ⟨C, hcs, hct, hmin, fun w => by rw [hout]; rfl, fun d b τ => ?_, fun d b τ => ?_⟩
  · rw [hout]
    show ((kapOf C.m ((I₂ d.fst).cnt d.snd) (msgC ((R d.fst d.snd).getD 0)) (fsOf (I₂ d.fst).h d.fst d.snd)
      (ftOf (I₂ d.fst).h d.fst d.snd) (msgS ((R d.fst d.snd).getD 0)) b).1 τ = true ↔ _) ∧
      ((kapOf C.m ((I₂ d.fst).cnt d.snd) (msgC ((R d.fst d.snd).getD 0)) (fsOf (I₂ d.fst).h d.fst d.snd)
      (ftOf (I₂ d.fst).h d.fst d.snd) (msgS ((R d.fst d.snd).getD 0)) b).2 τ = true ↔ _)
    have e1 := hcR d.symm
    simp only [SimpleGraph.Dart.symm_toProd, Prod.fst_swap, Prod.snd_swap] at e1
    rw [hcO d, e1.1, e1.2.1]
    exact kapOf_spec C cnt' hidx' hpast d (hfs d) (hft d) (hfs d.symm) b τ
  · rw [hout]
    show ((kapOf C.m (msgC ((R d.snd d.fst).getD 0)) ((I₂ d.snd).cnt d.fst) (msgS ((R d.snd d.fst).getD 0))
      (msgT ((R d.snd d.fst).getD 0)) (fsOf (I₂ d.snd).h d.snd d.fst) b).1 τ = true ↔ _) ∧
      ((kapOf C.m (msgC ((R d.snd d.fst).getD 0)) ((I₂ d.snd).cnt d.fst) (msgS ((R d.snd d.fst).getD 0))
      (msgT ((R d.snd d.fst).getD 0)) (fsOf (I₂ d.snd).h d.snd d.fst) b).2 τ = true ↔ _)
    have e1 := hcR d
    have e2 := hcO d.symm
    simp only [SimpleGraph.Dart.symm_toProd, Prod.fst_swap, Prod.snd_swap] at e2
    have e3 := hfs d.symm
    simp only [SimpleGraph.Dart.symm_toProd, Prod.fst_swap, Prod.snd_swap] at e3
    rw [e1.1, e1.2.1, e1.2.2, e2]
    exact kapOf_spec C cnt' hidx' hpast d (hfs d) (hft d) e3 b τ

end SsspFlow.Congest
