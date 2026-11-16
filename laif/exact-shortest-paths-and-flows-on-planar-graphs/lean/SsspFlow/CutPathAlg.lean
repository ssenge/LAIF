import SsspFlow.CutPathChain
import SsspFlow.OracleChainAlg
import SsspFlow.HostSim

/-!
# The parent chain of the dual network in the message model

Every node hosts the identifiers of the dual network whose first coordinate it is, and computes
their inputs for the two runs along the chains from its rotation list, the costs of its darts and
whether it is the node of the source or of the target: lengths `dualLen e g`, offset `0` at the corner
of the first dart of the source, the corner of the first dart of the target as target, and the nodes of
kind `m1` flagged.

* `chainIn_eq`: the host computes the inputs of its identifiers.
* `run_chainHost`: the hosts simulate `chainAlg` on the dual network.
-/

set_option autoImplicit false

open Cslib.Congest
open scoped ENNReal

namespace SsspFlow.Congest

open XNode Kind

/-- The input of a host for the chain of the dual network: its rotation list, the costs of its darts,
and whether it is the node of the source or of the target. -/
structure DualHostIn (V : Type) where
  /-- The rotation list. -/
  nbrs : List V
  /-- The costs of the darts. -/
  cost : V → ℕ
  /-- Whether the host is the node of the source. -/
  isS : Bool
  /-- Whether the host is the node of the target. -/
  isT : Bool

/-- An integer weight as a length, `⊤` for no arc. -/
def toLen : Option ℤ → ℕ∞
  | some y => (y.toNat : ℕ∞)
  | none => ⊤

section Hosts

variable {V : Type} [Fintype V] [DecidableEq V] {W : Type} [Fintype W] [DecidableEq W]
  (e : V × V × Kind ≃ W)

theorem dualLen_eq (g : V → V → ℕ) (a b : W) :
    dualLen e g a b = toLen (dualW e (fun u v => (g u v : ℤ)) a b) := by
  unfold dualLen toLen
  cases dualW e (fun u v => (g u v : ℤ)) a b <;> rfl

/-- The input of an identifier for the chain, as its host `v` computes it. -/
noncomputable def vChainIn (v : V) (h : DualHostIn V) (a : W) : ChainI W :=
  ((⟨(vNegIn e v h.nbrs (fun u => (h.cost u : ℤ)) h.isS a).nbrs,
      fun b => toLen ((vNegIn e v h.nbrs (fun u => (h.cost u : ℤ)) h.isS a).wOut b),
      fun b => toLen ((vNegIn e v h.nbrs (fun u => (h.cost u : ℤ)) h.isS a).wIn b),
      if (vNegIn e v h.nbrs (fun u => (h.cost u : ℤ)) h.isS a).isSource then 0 else ⊤⟩ : OracleIn W),
    ((vNegIn e v h.nbrs (fun u => (h.cost u : ℤ)) h.isT a).isSource,
      decide ((e.symm a).2.2 = m1 ∧ (e.symm a).2.1 ∈ h.nbrs), false))

variable (N : Net V) (g : V → V → ℕ)

/-- The input of a host for the costs `g` and the nodes `s` and `t`. -/
def dualHostOf (s t : V) (v : V) : DualHostIn V := ⟨N.rotList v, g v, decide (v = s), decide (v = t)⟩

/-- The first dart of a node with a neighbour. -/
def firstDart {u : V} (hu : N.G.Adj u ((N.rotList u).headD u)) : N.G.Dart := ⟨(u, (N.rotList u).headD u), hu⟩

/-- The inputs of the identifiers for the chain. -/
noncomputable def chainInp {s t : V} (hs : N.G.Adj s ((N.rotList s).headD s))
    (ht : N.G.Adj t ((N.rotList t).headD t)) (a : W) : ChainI W :=
  ((dualNet N e).oracleIn (dualLen e g) (cornerOff N e (firstDart N hs)) a,
    (decide (a = idx N e corner (firstDart N ht)), (m1Dart N e a).isSome, false))

variable {N e g}

/-- **The host knows the inputs of its identifiers.** -/
theorem chainIn_eq {s t : V} (hs : N.G.Adj s ((N.rotList s).headD s)) (ht : N.G.Adj t ((N.rotList t).headD t))
    {v : V} {a : W} (ha : (e.symm a).1 = v) :
    chainInp e N g hs ht a = vChainIn e v (dualHostOf N g s t v) a := by
  have h1 := negIn_eq (N := N) (e := e) (g := fun u v => (g u v : ℤ)) s ha
  have h2 := negIn_eq (N := N) (e := e) (g := fun u v => (g u v : ℤ)) t ha
  unfold vChainIn dualHostOf
  simp only at h1 h2 ⊢
  rw [← h1, ← h2]
  unfold chainInp Net.oracleIn Net.negIn
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ rfl))
  · simp only
    congr 1
    · funext u
      by_cases hu : (dualNet N e).G.Adj a u <;> simp [hu, dualLen_eq, toLen]
    · funext u
      by_cases hu : (dualNet N e).G.Adj a u <;> simp [hu, dualLen_eq, toLen]
    · simp [cornerOff, idx, firstDart]
  · simp [idx, firstDart]
  · simp only
    unfold m1Dart
    subst ha
    have hm : (e.symm a).2.1 ∈ N.rotList (e.symm a).1 ↔ N.G.Adj (e.symm a).1 (e.symm a).2.1 :=
      N.mem_rotList _ _
    by_cases h : N.G.Adj (e.symm a).1 (e.symm a).2.1 ∧ (e.symm a).2.2 = m1
    · rw [dif_pos h]; simp [hm, h.1, h.2]
    · rw [dif_neg h]
      simp only [Option.isSome_none]
      symm
      simp only [decide_eq_false_iff_not, hm]
      tauto

variable (e) in
/-- The hosts run an algorithm on the identifiers of the dual network. -/
noncomputable def chainHost {σ : Type} {B : ℕ} (A : Algorithm W (ChainI W) σ B) :
    Algorithm V (DualHostIn V) (DualHostIn V × (W → σ)) (B + B) :=
  Algorithm.simulate A (fun a => (e.symm a).1)
    (fun v h b a => a ∈ vRot e v h.nbrs (e.symm b).2.1 (e.symm b).2.2) (crossId e) (vChainIn e)

/-- **The hosts simulate the dual network.** -/
theorem run_chainHost {σ : Type} {B : ℕ} (A : Algorithm W (ChainI W) σ B) {s t : V}
    (hs : N.G.Adj s ((N.rotList s).headD s)) (ht : N.G.Adj t ((N.rotList t).headD t)) (T : ℕ) (a : W) :
    ((chainHost e A).run N.G (dualHostOf N g s t) T (e.symm a).1).2 a =
      A.run (dualNet N e).G (chainInp e N g hs ht) T a := by
  refine (Algorithm.run_simulate A (fun a => (e.symm a).1)
    (fun v h b a => a ∈ vRot e v h.nbrs (e.symm b).2.1 (e.symm b).2.2) (crossId e) (vChainIn e) N.G
    (dualNet N e).G (dualHostOf N g s t) (chainInp e N g hs ht) ?_ ?_ ?_ T _).2 a rfl
  · intro a
    exact chainIn_eq hs ht rfl
  · intro b a hba
    show a ∈ vRot e (e.symm a).1 (N.rotList (e.symm a).1) (e.symm b).2.1 (e.symm b).2.2 ↔ _
    rw [← hba, ← dualNet_rotList (N := N) (e := e)]
    have : e ((e.symm b).1, (e.symm b).2.1, (e.symm b).2.2) = b := by simp
    rw [this]
    exact (dualNet N e).mem_rotList _ _
  · intro b a hba
    exact dual_adj_cross hba

theorem m1Flag_eq (a : W) : m1Flag N e a = (((m1Dart N e a).isSome.toNat : ℕ) : ℕ∞) := by
  unfold m1Flag
  cases m1Dart N e a <;> rfl

/-- The lengths of the dual network are `⊤`, `0` or a cost. -/
theorem dualLen_cases (a b : W) :
    dualLen e g a b = ⊤ ∨ dualLen e g a b = 0 ∨ ∃ u v, dualLen e g a b = g u v := by
  rw [dualLen_eq]
  unfold dualW
  split_ifs
  · left; rfl
  · cases hk : kindW ((g (e.symm a).1 (e.symm a).2.1 : ℕ) : ℤ) (e.symm a).2.2 (e.symm b).2.2 with
    | none => left; rfl
    | some y =>
      rcases kindW_cases hk with ⟨-, -, rfl⟩ | ⟨rfl, -⟩
      · right; right; exact ⟨(e.symm a).1, (e.symm a).2.1, by simp [toLen]⟩
      · right; left; simp [toLen]

end Hosts

section Spec

variable {n n' : ℕ} (e : Fin n × Fin n × Kind ≃ Fin n') (hE : ExactSsspBound) (K D : ℕ)

open Classical in
/-- **The parent chain of the dual network at the hosts.** Assuming the Exact SSSP bound, for costs
at least `1` and at most `(n' + 2) ^ K` on a planar connected network of diameter at most `D`, after
`3 C log^c n' (5 D + 6) + 1` rounds the hosts hold, at their identifiers, outputs of the two runs that
meet the specification of the oracle: the first from the corner of the first dart of `s`, the second
counting the nodes of kind `m1` below the corner of the first dart of `t`. -/
theorem chainHost_spec (N : Net (Fin n)) (g : Fin n → Fin n → ℕ) {s t : Fin n}
    (hs : N.G.Adj s ((N.rotList s).headD s)) (ht : N.G.Adj t ((N.rotList t).headD t))
    (hP : N.toRot.Planar) (hN : ∀ v, ∃ u, N.G.Adj v u) (hDi : N.DiamLE D) (hc : N.toRot.Connected)
    (hgK : ∀ u v, g u v ≤ (n' + 2) ^ K) :
    let out := hE.out K n' (5 * D + 6) (by omega)
    let T₁ := hE.cC K * logN n' ^ hE.cc K * (5 * D + 6)
    let st := fun a => chainOut out a (((chainHost e (chainAlg (hE.alg K n' (5 * D + 6) (by omega)) out T₁)).run
      N.G (dualHostOf N g s t) (T₁ + (1 + (T₁ + T₁))) (e.symm a).1).2 a)
    (dualNet N e).ExactSpec (dualLen e g) (cornerOff N e (firstDart N hs)) (fun a => (st a).1) ∧
      (dualNet N e).ExactSpec (Net.markLenW (fun a => (st a).1) (m1Flag N e))
        (Net.markOffB fun a => decide (a = idx N e corner (firstDart N ht))) (fun a => (st a).2.1) := by
  intro out T₁ st
  have hval : OracleValid (dualNet N e) 0 ((n' + 2) ^ K) (dualLen e g) (cornerOff N e (firstDart N hs)) := by
    refine ⟨fun a b _ => ?_, fun a => ?_⟩
    · rcases dualLen_cases (e := e) (g := g) a b with h | h | ⟨u, v, h⟩
      · exact Or.inl h
      · exact Or.inr ⟨by simp, by rw [h]; exact bot_le⟩
      · exact Or.inr ⟨by simp, by rw [h]; exact_mod_cast hgK u v⟩
    · unfold cornerOff
      split_ifs
      · exact Or.inr bot_le
      · exact Or.inl rfl
  have hsp := chainAlg_spec hE K n' (5 * D + 6) (by omega) (dualNet N e) (dualLen e g)
    (cornerOff N e (firstDart N hs)) (fun a => (chainInp e N g hs ht a).2)
    (dualNet_planar hP hN hDi hc) (dualNet_diam hDi) hval
  simp only at hsp
  have hrun : ∀ a, st a = chainOut out a ((chainAlg (hE.alg K n' (5 * D + 6) (by omega)) out T₁).run
      (dualNet N e).G (fun v => ((dualNet N e).oracleIn (dualLen e g) (cornerOff N e (firstDart N hs)) v,
        (chainInp e N g hs ht v).2)) (T₁ + (1 + (T₁ + T₁))) a) := fun a => by
    simp only [st]
    rw [run_chainHost]
    rfl
  have hf : (m1Flag N e) = fun a => (((chainInp e N g hs ht a).2.2.1).toNat : ℕ∞) := by
    funext a
    rw [m1Flag_eq]
    rfl
  refine ⟨?_, ?_⟩
  · rw [show (fun a => (st a).1) = _ from funext fun a => by rw [hrun a]]
    exact hsp.1
  · rw [show (fun a => (st a).2.1) = _ from funext fun a => by rw [hrun a],
      show (fun a => (st a).1) = _ from funext fun a => by rw [hrun a], hf]
    exact hsp.2.1

open Classical FourColor in
/-- **The shortest cut path at the hosts.** For costs at least `1` and two nodes `s ≠ t`, the dual has
a cut path from the first dart of `s` to the first dart of `t` that is shortest for the costs, and the
hosts hold its data after the two runs: the identifier of kind `m1` of the dart `e τ` holds the count
`m - 1 - τ`, the darts past the end are `cs`, and the corner of the first dart of `s` holds `m`. -/
theorem chainHost_cutPath (N : Net (Fin n)) (g : Fin n → Fin n → ℕ) {s t : Fin n}
    (hs : N.G.Adj s ((N.rotList s).headD s)) (ht : N.G.Adj t ((N.rotList t).headD t)) (hst : s ≠ t)
    (hP : N.toRot.Planar) (hN : ∀ v, ∃ u, N.G.Adj v u) (hDi : N.DiamLE D) (hc : N.toRot.Connected)
    (hgK : ∀ u v, g u v ≤ (n' + 2) ^ K) (hg1 : ∀ d : N.G.Dart, 1 ≤ g d.fst d.snd) :
    let out := hE.out K n' (5 * D + 6) (by omega)
    let T₁ := hE.cC K * logN n' ^ hE.cc K * (5 * D + 6)
    let st := fun a => chainOut out a (((chainHost e (chainAlg (hE.alg K n' (5 * D + 6) (by omega)) out T₁)).run
      N.G (dualHostOf N g s t) (T₁ + (1 + (T₁ + T₁))) (e.symm a).1).2 a)
    ∃ C : N.toRot.dual.CutPath, C.cs = firstDart N hs ∧ C.ct = firstDart N ht ∧
      (∀ q, N.toRot.dual.IsWalk (C.v 0) q (C.v C.m) →
        C.pos (fun x => g x.fst x.snd) C.m ≤ (q.map fun x => g x.fst x.snd).sum) ∧
      (∀ (x : N.G.Dart) (τ : ℕ), τ < C.m → (C.e τ = x ↔ (st (idx N e m1 x)).2.1.1 = ((C.m - 1 - τ : ℕ) : ℕ∞))) ∧
      (∀ τ, C.m ≤ τ → C.e τ = C.cs) ∧
      (st (idx N e corner (firstDart N hs))).2.1.1 = (C.m : ℕ∞) := by
  intro out T₁ st
  obtain ⟨h1, h2⟩ := chainHost_spec e hE K D N g hs ht hP hN hDi hc hgK
  have hf : ¬ fconnect N.toRot.dual.facePerm (firstDart N hs) (firstDart N ht) := by
    intro hfc
    apply hst
    have h' := (fconnect_congr N.toRot.dual.facePerm_apply).1 hfc
    have : N.toRot.tail (firstDart N hs) = N.toRot.tail (firstDart N ht) := by
      rw [← N.toRot.dual_faceOf_eq_iff, RotSystem.faceOf_eq_iff]
      exact h'
    exact N.tail_eq_iff.1 this
  have hw : ∃ q, N.toRot.dual.IsWalk (N.toRot.dual.tail (firstDart N hs)) q
      (N.toRot.dual.tail (firstDart N ht)) :=
    ((N.toRot.dual.connected_iff).1 (N.toRot.connected_dual.2 hc)).2 _ _
  obtain ⟨C, hcs, hct, hmin, hidx, hpast, hroot⟩ := chain_cutPath g hg1 hf hw h1
  have hd : ∀ a, ((st a).2.1.1 : ℝ≥0∞) = (dualNet N e).dsrcTop (Net.markLenW (fun a => (st a).1) (m1Flag N e))
      (Net.markOffB fun a => decide (a = idx N e corner (firstDart N ht))) a := h2.dist_eq
  refine ⟨C, hcs, hct, hmin, fun x τ hτ => ?_, hpast, ?_⟩
  · rw [hidx x τ hτ, ← hd, ← ENat.toENNReal_coe, ENat.toENNReal_inj]
  · have := hroot
    rw [← hd, ← ENat.toENNReal_coe, ENat.toENNReal_inj] at this
    exact this

end Spec

end SsspFlow.Congest
