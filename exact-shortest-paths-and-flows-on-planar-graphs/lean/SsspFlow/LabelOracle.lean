import Mathlib.Algebra.Order.Floor.Extended
import SsspFlow.LabelHypothesis

/-!
# Approximate distances from the labels in the message model

`approxOracle`: from `LabelHypothesis` and `AggBox`, a `(1 + 1/e)`-approximate oracle for shortest
paths from a virtual source, on planar networks with lengths and offsets of polynomial size, in
`Õ(D e)` rounds with words of polylogarithmically many bits. This is the corollary of the Virtual
Source Lemma in the paper.

The algorithm computes the labels for the lengths with `⊤` replaced by a large number `M`, runs one
aggregation over the subgraphs of all bags, and answers `⊤` for estimates of at least `M`.

* `Walk.nwt`, `Walk.exists_nodup`, `Walk.exists_last`, `ndsrc`: walks and distances from a virtual
  source with natural lengths.
* `PolyLog`, `PolyN`: polylogarithmic and polynomial bounds, closed under sums and products.
* `labelAggIn_valid`: the labels give a valid input of `AggBox`.
* `labelAnswer_eq`: the answer of a node is the query of `lemmaV_chain₂`.
* `capped_bounds`: an answer for the lengths with `⊤` replaced by `M` is correct for the given lengths.
-/

set_option autoImplicit false

open scoped ENNReal
open Cslib.Congest

namespace SsspFlow

namespace Walk

variable {V : Type} {adj : V → V → Prop}

/-- The length of a walk under natural arc lengths. -/
def nwt (x : V → V → ℕ) : {a b : V} → Walk adj a b → ℕ
  | _, _, nil _ => 0
  | _, _, @cons _ _ a m _ _ p => x a m + p.nwt x

@[simp] lemma nwt_nil (x : V → V → ℕ) (a : V) : (nil a : Walk adj a a).nwt x = 0 := rfl

@[simp] lemma nwt_cons (x : V → V → ℕ) {a b c : V} (e : adj a b) (p : Walk adj b c) :
    (cons e p).nwt x = x a b + p.nwt x := rfl

lemma nwt_append (x : V → V → ℕ) : ∀ {a b c : V} (p : Walk adj a b) (q : Walk adj b c),
    (p.append q).nwt x = p.nwt x + q.nwt x
  | _, _, _, nil _, q => by simp [append]
  | _, _, _, cons e p, q => by simp [append, nwt_append x p q, Nat.add_assoc]

lemma wt_lenOf (x : V → V → ℕ) : ∀ {a b : V} (p : Walk adj a b),
    p.wt (Congest.lenOf x) = (p.nwt x : ℝ≥0∞)
  | _, _, nil _ => by simp
  | _, _, cons e p => by simp [wt_lenOf x p, Congest.lenOf]

lemma wt_mono {w w' : V → V → ℝ≥0∞} (h : ∀ a b, w a b ≤ w' a b) :
    ∀ {a b : V} (p : Walk adj a b), p.wt w ≤ p.wt w'
  | _, _, nil _ => by simp
  | _, _, cons e p => by
    simp only [wt_cons]
    exact add_le_add (h _ _) (wt_mono h p)

lemma exists_map {adj' : V → V → Prop} (h : ∀ a b, adj a b → adj' a b) :
    ∀ {a b : V} (p : Walk adj a b), ∃ q : Walk adj' a b, q.support = p.support
  | _, _, nil a => ⟨nil a, rfl⟩
  | _, _, cons e p => by
    obtain ⟨q, hq⟩ := exists_map h p
    exact ⟨cons (h _ _ e) q, by simp [hq]⟩

/-- The part of a walk that starts at one of its vertices. -/
lemma exists_suffix (w : V → V → ℝ≥0∞) {a b c : V} (q : Walk adj b c) (ha : a ∈ q.support) :
    ∃ r : Walk adj a c, r.support.Sublist q.support ∧ r.wt w ≤ q.wt w := by
  induction q with
  | nil b =>
    obtain rfl : a = b := by simpa using ha
    exact ⟨nil a, List.Sublist.refl _, le_rfl⟩
  | @cons x y z e q ih =>
    by_cases hax : a = x
    · subst hax
      exact ⟨cons e q, List.Sublist.refl _, le_rfl⟩
    · obtain ⟨r, h₁, h₂⟩ := ih (by simpa [hax] using ha)
      exact ⟨r, h₁.cons _, h₂.trans (by simp)⟩

/-- Every walk can be replaced by one without repeated vertices that is not longer. -/
lemma exists_nodup [DecidableEq V] (w : V → V → ℝ≥0∞) : ∀ {a b : V} (p : Walk adj a b),
    ∃ q : Walk adj a b, q.support.Nodup ∧ q.wt w ≤ p.wt w
  | _, _, nil a => ⟨nil a, by simp, le_rfl⟩
  | a, _, cons e p => by
    obtain ⟨q, hq, hw⟩ := exists_nodup w p
    by_cases ha : a ∈ q.support
    · obtain ⟨r, h₁, h₂⟩ := exists_suffix w q ha
      exact ⟨r, h₁.nodup hq, h₂.trans (hw.trans (by simp))⟩
    · exact ⟨cons e q, by simp [ha, hq], by simp only [wt_cons]; gcongr⟩

/-- A walk is empty or ends with an arc. -/
lemma exists_last (x : V → V → ℕ) : ∀ {a b : V} (p : Walk adj a b),
    (a = b ∧ p.nwt x = 0) ∨ ∃ u, adj u b ∧ ∃ r : Walk adj a u, p.nwt x = r.nwt x + x u b
  | _, _, nil a => .inl ⟨rfl, rfl⟩
  | a, b, @cons _ _ _ m _ e p => by
    right
    rcases exists_last x p with ⟨rfl, hp⟩ | ⟨u, hu, r, hr⟩
    · exact ⟨a, e, nil a, by simp [hp]⟩
    · exact ⟨u, hu, cons e r, by simp [hr, Nat.add_assoc]⟩

end Walk

namespace Congest

section Dist

variable {V : Type} {adj : V → V → Prop}

theorem dsrc_le_walk (w : V → V → ℝ≥0∞) (φ : V → ℝ≥0∞) {a v : V} (p : Walk adj a v) :
    dsrc adj w φ v ≤ φ a + p.wt w := by
  refine (iInf_le _ a).trans ?_
  gcongr
  exact iInf₂_le p (by simp)

theorem le_dsrc {w : V → V → ℝ≥0∞} {φ : V → ℝ≥0∞} {c : ℝ≥0∞} {v : V}
    (h : ∀ a (p : Walk adj a v), c ≤ φ a + p.wt w) : c ≤ dsrc adj w φ v := by
  simp only [dsrc, dist, ENNReal.add_iInf, le_iInf_iff]
  exact fun a p _ => h a p

theorem dsrc_lt_iff {w : V → V → ℝ≥0∞} {φ : V → ℝ≥0∞} {c : ℝ≥0∞} {v : V} :
    dsrc adj w φ v < c ↔ ∃ a, ∃ p : Walk adj a v, φ a + p.wt w < c := by
  constructor
  · intro h
    by_contra hc
    push Not at hc
    exact absurd (le_dsrc hc) (not_le.2 h)
  · rintro ⟨a, p, h⟩
    exact (dsrc_le_walk w φ p).trans_lt h

/-- The distance from a virtual source for natural lengths and offsets. -/
noncomputable def ndsrc (adj : V → V → Prop) (x : V → V → ℕ) (y : V → ℕ) (v : V) : ℕ :=
  sInf {k | ∃ a, ∃ p : Walk adj a v, k = y a + p.nwt x}

theorem ndsrc_spec (adj : V → V → Prop) (x : V → V → ℕ) (y : V → ℕ) (v : V) :
    ∃ a, ∃ p : Walk adj a v, ndsrc adj x y v = y a + p.nwt x :=
  Nat.sInf_mem (s := {k | ∃ a, ∃ p : Walk adj a v, k = y a + p.nwt x}) ⟨_, v, .nil v, rfl⟩

variable {x : V → V → ℕ} {y : V → ℕ}

theorem ndsrc_le {a v : V} (p : Walk adj a v) : ndsrc adj x y v ≤ y a + p.nwt x :=
  Nat.sInf_le ⟨a, p, rfl⟩

theorem ndsrc_le_off (v : V) : ndsrc adj x y v ≤ y v := by
  simpa using ndsrc_le (adj := adj) (x := x) (y := y) (Walk.nil v)

theorem ndsrc_triangle {a b : V} (h : adj a b) :
    ndsrc adj x y b ≤ ndsrc adj x y a + x a b := by
  obtain ⟨c, p, hp⟩ := ndsrc_spec adj x y a
  have := ndsrc_le (x := x) (y := y) (p.append (.cons h (.nil b)))
  rw [Walk.nwt_append] at this
  simp only [Walk.nwt_cons, Walk.nwt_nil] at this
  omega

/-- The distance is an offset, or the distance of a neighbour plus an arc. -/
theorem ndsrc_bellman (v : V) :
    ndsrc adj x y v = y v ∨ ∃ u, adj u v ∧ ndsrc adj x y u + x u v = ndsrc adj x y v := by
  obtain ⟨a, p, hp⟩ := ndsrc_spec adj x y v
  rcases Walk.exists_last x p with ⟨rfl, h0⟩ | ⟨u, hu, r, hr⟩
  · left
    omega
  · right
    refine ⟨u, hu, le_antisymm ?_ (ndsrc_triangle hu)⟩
    have := ndsrc_le (x := x) (y := y) r
    omega

theorem dsrc_nat (adj : V → V → Prop) (x : V → V → ℕ) (y : V → ℕ) (v : V) :
    dsrc adj (lenOf x) (fun v => (y v : ℝ≥0∞)) v = (ndsrc adj x y v : ℝ≥0∞) := by
  apply le_antisymm
  · obtain ⟨a, p, hp⟩ := ndsrc_spec adj x y v
    refine (dsrc_le_walk _ _ p).trans_eq ?_
    rw [hp, Walk.wt_lenOf, Nat.cast_add]
  · refine le_dsrc fun a p => ?_
    rw [Walk.wt_lenOf, ← Nat.cast_add]
    exact Nat.cast_le.2 (ndsrc_le p)

/-- A walk with all lengths at most `W` or `⊤`, and of finite length, is short in terms of `W`. -/
theorem wt_top_add_le {ℓ : V → V → ℕ∞} {W : ℕ} (h : ∀ a b, adj a b → ℓ a b = ⊤ ∨ ℓ a b ≤ W) :
    ∀ {a b : V} (p : Walk adj a b), p.wt (lenTop ℓ) ≠ ⊤ →
      p.wt (lenTop ℓ) + W ≤ ((p.support.length * W : ℕ) : ℝ≥0∞)
  | _, _, .nil a, _ => by simp
  | _, _, @Walk.cons _ _ a m _ e p, hne => by
    rw [Walk.wt_cons] at hne ⊢
    have h₁ : lenTop ℓ a m ≠ ⊤ := fun h' => hne (by rw [h', top_add])
    have h₂ : p.wt (lenTop ℓ) ≠ ⊤ := fun h' => hne (by rw [h', add_top])
    have hℓ : lenTop ℓ a m ≤ (W : ℝ≥0∞) := by
      rcases h _ _ e with h' | h'
      · exact absurd (by simp [lenTop, h']) h₁
      · simpa [lenTop] using ENat.toENNReal_mono h'
    have ih := wt_top_add_le h p h₂
    rw [add_assoc]
    refine (add_le_add hℓ ih).trans_eq ?_
    simp only [Walk.support_cons, List.length_cons]
    push_cast
    ring

end Dist

/-! ### Polylogarithmic and polynomial bounds -/

/-- `f` is at most polylogarithmic. -/
def PolyLog (f : ℕ → ℕ) : Prop := ∃ C c : ℕ, ∀ n, f n ≤ C * logN n ^ c

/-- `f` is at most polynomial. -/
def PolyN (f : ℕ → ℕ) : Prop := ∃ k : ℕ, ∀ n, f n ≤ (n + 2) ^ k

theorem one_le_logN (n : ℕ) : 1 ≤ logN n := Nat.le_add_left _ _

theorem lt_two_pow_logN (n : ℕ) : n + 2 < 2 ^ logN n := Nat.lt_pow_succ_log_self (by norm_num) _

theorem PolyLog.const (a : ℕ) : PolyLog fun _ => a := ⟨a, 0, fun n => by simp⟩

theorem polyLog_logN : PolyLog logN := ⟨1, 1, fun n => by simp⟩

theorem polyLog_pow (C c : ℕ) : PolyLog fun n => C * logN n ^ c := ⟨C, c, fun _ => le_rfl⟩

theorem PolyLog.mono {f g : ℕ → ℕ} (h : ∀ n, f n ≤ g n) (hg : PolyLog g) : PolyLog f := by
  obtain ⟨C, c, hg⟩ := hg
  exact ⟨C, c, fun n => (h n).trans (hg n)⟩

theorem PolyLog.add {f g : ℕ → ℕ} (hf : PolyLog f) (hg : PolyLog g) :
    PolyLog fun n => f n + g n := by
  obtain ⟨C₁, c₁, h₁⟩ := hf
  obtain ⟨C₂, c₂, h₂⟩ := hg
  refine ⟨C₁ + C₂, max c₁ c₂, fun n => ?_⟩
  have hL := one_le_logN n
  have e₁ : logN n ^ c₁ ≤ logN n ^ max c₁ c₂ := Nat.pow_le_pow_right hL (le_max_left _ _)
  have e₂ : logN n ^ c₂ ≤ logN n ^ max c₁ c₂ := Nat.pow_le_pow_right hL (le_max_right _ _)
  calc f n + g n ≤ C₁ * logN n ^ c₁ + C₂ * logN n ^ c₂ := add_le_add (h₁ n) (h₂ n)
    _ ≤ C₁ * logN n ^ max c₁ c₂ + C₂ * logN n ^ max c₁ c₂ := by gcongr
    _ = _ := by ring

theorem PolyLog.mul {f g : ℕ → ℕ} (hf : PolyLog f) (hg : PolyLog g) :
    PolyLog fun n => f n * g n := by
  obtain ⟨C₁, c₁, h₁⟩ := hf
  obtain ⟨C₂, c₂, h₂⟩ := hg
  refine ⟨C₁ * C₂, c₁ + c₂, fun n => ?_⟩
  calc f n * g n ≤ (C₁ * logN n ^ c₁) * (C₂ * logN n ^ c₂) := Nat.mul_le_mul (h₁ n) (h₂ n)
    _ = _ := by ring

theorem PolyN.mono {f g : ℕ → ℕ} (h : ∀ n, f n ≤ g n) (hg : PolyN g) : PolyN f := by
  obtain ⟨k, hg⟩ := hg
  exact ⟨k, fun n => (h n).trans (hg n)⟩

theorem PolyN.const (a : ℕ) : PolyN fun _ => a :=
  ⟨a, fun n => Nat.lt_two_pow_self.le.trans (Nat.pow_le_pow_left (by omega) a)⟩

theorem polyN_id : PolyN fun n => n := ⟨1, fun n => by simp⟩

theorem polyN_pow (K : ℕ) : PolyN fun n => (n + 2) ^ K := ⟨K, fun _ => le_rfl⟩

theorem PolyN.add {f g : ℕ → ℕ} (hf : PolyN f) (hg : PolyN g) : PolyN fun n => f n + g n := by
  obtain ⟨a, h₁⟩ := hf
  obtain ⟨b, h₂⟩ := hg
  refine ⟨max a b + 1, fun n => ?_⟩
  have hX : 1 ≤ n + 2 := by omega
  have e₁ : (n + 2) ^ a ≤ (n + 2) ^ max a b := Nat.pow_le_pow_right hX (le_max_left _ _)
  have e₂ : (n + 2) ^ b ≤ (n + 2) ^ max a b := Nat.pow_le_pow_right hX (le_max_right _ _)
  have := h₁ n
  have := h₂ n
  rw [pow_succ]
  nlinarith [Nat.zero_le ((n + 2) ^ max a b)]

theorem PolyN.mul {f g : ℕ → ℕ} (hf : PolyN f) (hg : PolyN g) : PolyN fun n => f n * g n := by
  obtain ⟨a, h₁⟩ := hf
  obtain ⟨b, h₂⟩ := hg
  exact ⟨a + b, fun n => by rw [pow_add]; exact Nat.mul_le_mul (h₁ n) (h₂ n)⟩

theorem pow_le_two_pow (n k : ℕ) : (n + 2) ^ k ≤ 2 ^ (logN n * k) := by
  rw [pow_mul]
  exact Nat.pow_le_pow_left (lt_two_pow_logN n).le k

/-- The logarithm of a polynomial is polylogarithmic. -/
theorem PolyN.log {f : ℕ → ℕ} (hf : PolyN f) : PolyLog fun n => Nat.log 2 (f n) := by
  obtain ⟨k, hk⟩ := hf
  refine ⟨k, 1, fun n => ?_⟩
  have h := Nat.log_mono_right (b := 2) ((hk n).trans (pow_le_two_pow n k))
  rw [Nat.log_pow (by norm_num)] at h
  rw [pow_one, mul_comm]
  exact h

/-- A number of polynomial size fits into `O(log n)` bits. -/
theorem lt_two_pow_of_le {x n k : ℕ} (h : x ≤ (n + 2) ^ k) : x < 2 ^ (logN n * k + 1) :=
  (h.trans (pow_le_two_pow n k)).trans_lt (Nat.pow_lt_pow_right (by norm_num) (by omega))

/-! ### The labels as an input of the aggregation -/

variable {n : ℕ}

/-- The input of a node for one aggregation over the subgraphs of all bags: for every bag on its chain
and every hub with a finite value, the sum of its offset and its estimate to the hub. -/
def labelAggIn (lab : LabelOut (Fin n)) (off : ℕ∞) : AggIn (Fin n) where
  subgraphs u := (lab.treeBags u).dedup
  member := lab.chain.map BagEntry.bag
  items := lab.chain.flatMap fun E =>
    (E.hubs.filter fun F => off + F.toHub ≠ ⊤).map fun F =>
      (E.bag, (F.hub : ℕ), (off + F.toHub).toNat)

theorem mem_labelItems {lab : LabelOut (Fin n)} {off : ℕ∞} {t : ℕ × ℕ × ℕ} :
    t ∈ (labelAggIn lab off).items ↔
      ∃ E ∈ lab.chain, ∃ F ∈ E.hubs, off + F.toHub ≠ ⊤ ∧
        t = (E.bag, (F.hub : ℕ), (off + F.toHub).toNat) := by
  simp only [labelAggIn, List.mem_flatMap, List.mem_map, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨E, hE, F, ⟨hF, hne⟩, rfl⟩
    exact ⟨E, hE, F, hF, hne, rfl⟩
  · rintro ⟨E, hE, F, hF, hne, rfl⟩
    exact ⟨E, hE, F, ⟨hF, hne⟩, rfl⟩

section Witness

variable {N : Net (Fin n)} {ℓ : Fin n → Fin n → ℕ} {e h s w : ℕ} {out : Fin n → LabelOut (Fin n)}

/-- The labels and bounded offsets give a valid input of the aggregation: subgraphs of diameter `s`,
congestion `2 * (h + 1)`, at most `s` keys per subgraph, and fields of `b` bits. -/
theorem labelAggIn_valid (L : LabelWitness N ℓ e h s w out) {φ : Fin n → ℕ∞} {W b : ℕ}
    (hφ : ∀ v, φ v = ⊤ ∨ φ v ≤ W) (hb₁ : w ≤ b) (hb₂ : n ≤ 2 ^ b) (hb₃ : W + 2 ^ w ≤ 2 ^ b) :
    AggIn.Valid N (fun v => labelAggIn (out v) (φ v)) s (2 * (h + 1)) s b where
  symm v u hvu x := by
    simp only [labelAggIn, List.mem_dedup]
    rw [L.tree_know v u hvu, L.tree_know u v hvu.symm]
    exact ⟨L.tree_symm x v u, L.tree_symm x u v⟩
  span x a a' ha ha' := by
    obtain ⟨E, hE, rfl⟩ := List.mem_map.1 ha
    obtain ⟨E', hE', hx⟩ := List.mem_map.1 ha'
    have ca := (L.chain_iff a E.bag).2 ⟨E, hE, rfl⟩
    have ca' := (L.chain_iff a' E.bag).2 ⟨E', hE', hx⟩
    obtain ⟨p, hp⟩ := L.tree_span E.bag a a' (RHierarchy.Chain.mem _ ca) (RHierarchy.Chain.mem _ ca')
    obtain ⟨q, hq⟩ := Walk.exists_map (adj' := fun u v =>
      N.G.Adj u v ∧ E.bag ∈ (labelAggIn (out u) (φ u)).subgraphs v) (fun u v huv => by
        have hadj := L.tree_adj _ u v huv
        exact ⟨hadj, List.mem_dedup.2 ((L.tree_know u v hadj E.bag).2 huv)⟩) p
    exact ⟨q, hq ▸ hp⟩
  congestion v u hvu := by
    classical
    choose F hF using fun d => L.congestion d v u
    have hsub : ((out v).treeBags u).toFinset ⊆ (Finset.range (h + 1)).biUnion F := by
      intro x hx
      have ht : L.tree x v u := (L.tree_know v u hvu x).1 (List.mem_toFinset.1 hx)
      exact Finset.mem_biUnion.2 ⟨L.depth x, Finset.mem_range.2 (Nat.lt_succ_of_le (L.height x)),
        (hF _).2 x rfl ht⟩
    show ((out v).treeBags u).dedup.length ≤ _
    rw [← List.card_toFinset]
    calc ((out v).treeBags u).toFinset.card ≤ ((Finset.range (h + 1)).biUnion F).card :=
          Finset.card_le_card hsub
      _ ≤ ∑ d ∈ Finset.range (h + 1), (F d).card := Finset.card_biUnion_le
      _ ≤ ∑ _d ∈ Finset.range (h + 1), 2 := Finset.sum_le_sum fun d _ => (hF d).1
      _ = 2 * (h + 1) := by simp [mul_comm]
  keys x := by
    classical
    refine ⟨((L.H.hub x).toFinite.toFinset).image Fin.val, ?_, ?_⟩
    · exact Finset.card_image_le.trans
        ((Set.ncard_eq_toFinset_card _ _).symm.le.trans (L.hub_card x))
    · intro v t ht hx
      obtain ⟨E, hE, F, hF, -, rfl⟩ := mem_labelItems.1 ht
      obtain rfl : E.bag = x := hx
      refine Finset.mem_image.2 ⟨F.hub, ?_, rfl⟩
      simpa using (L.hubs_iff v E hE F.hub).2 ⟨F, hF, rfl⟩
  items_member v t ht := by
    obtain ⟨E, hE, F, hF, -, rfl⟩ := mem_labelItems.1 ht
    exact List.mem_map.2 ⟨E, hE, rfl⟩
  fields v t ht := by
    obtain ⟨E, hE, F, hF, hne, rfl⟩ := mem_labelItems.1 ht
    refine ⟨(L.name_lt v E hE).trans_le (Nat.pow_le_pow_right (by norm_num) hb₁),
      F.hub.2.trans_le hb₂, ?_⟩
    have h1 : φ v ≠ ⊤ := fun h' => hne (by simp [h'])
    have h2 : F.toHub ≠ ⊤ := fun h' => hne (by simp [h'])
    have hv := (hφ v).resolve_left h1
    have hf := ((L.value_lt v E hE F hF).1).resolve_left h2
    obtain ⟨x, hx⟩ := ENat.ne_top_iff_exists.1 h1
    obtain ⟨y, hy⟩ := ENat.ne_top_iff_exists.1 h2
    rw [← hx] at hv
    rw [← hy] at hf
    have hv' : x ≤ W := by exact_mod_cast hv
    have hf' : y < 2 ^ w := by exact_mod_cast hf
    show (φ v + F.toHub).toNat < 2 ^ b
    rw [← hx, ← hy, ← Nat.cast_add, ENat.toNat_natCast]
    omega
  names v u x hx :=
    (L.treeBags_lt v u x (List.mem_dedup.1 hx)).trans_le (Nat.pow_le_pow_right (by norm_num) hb₁)

/-- A result of the aggregation as a number in `ℕ∞`. -/
def optTop : Option ℕ → ℕ∞
  | none => ⊤
  | some m => m

theorem optTop_eq_aggC (L : LabelWitness N ℓ e h s w out) (φ : Fin n → ℕ∞) {x : ℕ} {y : Fin n}
    {r : Option ℕ} (hr : AggIn.IsMin (fun v => labelAggIn (out v) (φ v)) x y r) :
    ((optTop r : ℕ∞) : ℝ≥0∞) = L.H.aggC (offTop φ) (toH out) x y := by
  apply le_antisymm
  · simp only [RHierarchy.aggC, toH, ENNReal.add_iInf, le_iInf_iff]
    rintro a ha E hE rfl F hF rfl
    simp only [offTop]
    rw [← ENat.toENNReal_add, ENat.toENNReal_le]
    by_cases hne : φ a + F.toHub = ⊤
    · rw [hne]
      exact le_top
    · have hit := mem_labelItems.2 ⟨E, hE, F, hF, hne, rfl⟩
      cases r with
      | none => exact absurd hit (hr a _)
      | some m =>
        have hm := hr.2 a _ hit
        show (m : ℕ∞) ≤ _
        rw [← ENat.natCast_toNat hne]
        exact_mod_cast hm
  · cases r with
    | none => exact le_top
    | some m =>
      obtain ⟨v, hv⟩ := hr.1
      obtain ⟨E, hE, F, hF, hne, ht⟩ := mem_labelItems.1 hv
      simp only [Prod.mk.injEq] at ht
      obtain ⟨rfl, hy, rfl⟩ := ht
      obtain rfl : y = F.hub := Fin.ext hy
      have hc := (L.chain_iff v E.bag).2 ⟨E, hE, rfl⟩
      calc L.H.aggC (offTop φ) (toH out) E.bag F.hub
          ≤ offTop φ v + toH out E.bag v F.hub := iInf₂_le v hc
        _ ≤ offTop φ v + (F.toHub : ℝ≥0∞) := by
            gcongr
            exact iInf_le_of_le E <| iInf_le_of_le hE <| iInf_le_of_le rfl <|
              iInf_le_of_le F <| iInf_le_of_le hF <| iInf_le _ rfl
        _ = _ := by
            simp only [offTop, optTop]
            rw [← ENat.toENNReal_add, ENat.natCast_toNat hne]

/-- The answer of a node from its labels and the minima of the aggregation. -/
noncomputable def labelAnswer (lab : LabelOut (Fin n)) (res : ℕ → ℕ → Option ℕ) : ℕ∞ :=
  ⨅ E ∈ lab.chain, ⨅ F ∈ E.hubs, optTop (res E.bag F.hub) + F.fromHub

/-- The answer of a node is the query of `lemmaV_chain₂`. -/
theorem labelAnswer_eq (L : LabelWitness N ℓ e h s w out) (φ : Fin n → ℕ∞)
    (res : Fin n → ℕ → ℕ → Option ℕ)
    (hres : ∀ v, ∀ x ∈ (labelAggIn (out v) (φ v)).member, ∀ κ,
      AggIn.IsMin (fun v => labelAggIn (out v) (φ v)) x κ (res v x κ)) (z : Fin n) :
    (labelAnswer (out z) (res z) : ℝ≥0∞) = L.H.queryC₂ (offTop φ) (toH out) (fromH out) z := by
  have key : ∀ E ∈ (out z).chain, ∀ y : Fin n,
      ((optTop (res z E.bag y) : ℕ∞) : ℝ≥0∞) = L.H.aggC (offTop φ) (toH out) E.bag y :=
    fun E hE y => optTop_eq_aggC L φ (hres z E.bag (List.mem_map.2 ⟨E, hE, rfl⟩) y)
  simp only [labelAnswer, ENat.toENNReal_iInf, ENat.toENNReal_add]
  apply le_antisymm
  · simp only [RHierarchy.queryC₂, fromH, ENNReal.add_iInf, le_iInf_iff]
    rintro x hx y hy E hE rfl F hF rfl
    rw [← key E hE F.hub]
    exact iInf₂_le_of_le E hE (iInf₂_le_of_le F hF le_rfl)
  · refine le_iInf₂ fun E hE => le_iInf₂ fun F hF => ?_
    rw [key E hE F.hub]
    have hc := (L.chain_iff z E.bag).2 ⟨E, hE, rfl⟩
    have hh := (L.hubs_iff z E hE F.hub).2 ⟨F, hF, rfl⟩
    calc L.H.queryC₂ (offTop φ) (toH out) (fromH out) z
        ≤ L.H.aggC (offTop φ) (toH out) E.bag F.hub + fromH out E.bag F.hub z :=
          (iInf₂_le E.bag hc).trans (iInf₂_le F.hub hh)
      _ ≤ _ := by
          gcongr
          exact iInf_le_of_le E <| iInf_le_of_le hE <| iInf_le_of_le rfl <|
            iInf_le_of_le F <| iInf_le_of_le hF <| iInf_le _ rfl

end Witness

/-! ### Replacing `⊤` by a large number -/

/-- `⊤` replaced by `M`. -/
def capTop (M : ℕ) (x : ℕ∞) : ℕ := if x = ⊤ then M else x.toNat

@[simp] theorem capTop_top (M : ℕ) : capTop M ⊤ = M := by simp [capTop]

@[simp] theorem capTop_coe (M m : ℕ) : capTop M m = m := by simp [capTop]

/-- Estimates of at least `M` mean `⊤`. -/
def topAbove (M : ℕ) (x : ℕ∞) : ℕ∞ := if (M : ℕ∞) ≤ x then ⊤ else x

section Cap

variable {V : Type} {adj : V → V → Prop} {M : ℕ} {ℓ : V → V → ℕ∞}

/-- The lengths with `⊤` replaced by `M`. -/
def lenCap (M : ℕ) (ℓ : V → V → ℕ∞) : V → V → ℕ := fun a b => capTop M (ℓ a b)

theorem lenCap_le (a b : V) : lenOf (lenCap M ℓ) a b ≤ lenTop ℓ a b := by
  simp only [lenOf, lenCap, lenTop]
  by_cases h : ℓ a b = ⊤
  · simp [h]
  · obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.1 h
    simp [← hm]

/-- A walk shorter than `M` under the capped lengths has the same length under the given lengths. -/
theorem wt_top_eq_of_lt : ∀ {a b : V} (p : Walk adj a b), p.wt (lenOf (lenCap M ℓ)) < M →
    p.wt (lenTop ℓ) = p.wt (lenOf (lenCap M ℓ))
  | _, _, .nil a, _ => by simp
  | _, _, @Walk.cons _ _ a m _ e p, h => by
    rw [Walk.wt_cons] at h ⊢
    rw [Walk.wt_cons]
    have h₁ : lenOf (lenCap M ℓ) a m < M := lt_of_le_of_lt le_self_add h
    have h₂ : p.wt (lenOf (lenCap M ℓ)) < M := lt_of_le_of_lt le_add_self h
    rw [wt_top_eq_of_lt p h₂]
    congr 1
    simp only [lenOf, lenCap, lenTop] at h₁ ⊢
    by_cases hℓ : ℓ a m = ⊤
    · simp [hℓ] at h₁
    · obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.1 hℓ
      simp [← hk]

end Cap

/-- A finite distance from the virtual source is at most `|V| W`. -/
theorem dsrcTop_le {V : Type} [Fintype V] [DecidableEq V] {N : Net V} {m W : ℕ}
    {ℓ : V → V → ℕ∞} {φ : V → ℕ∞} (hv : OracleValid N m W ℓ φ) {z : V}
    (h : N.dsrcTop ℓ φ z ≠ ⊤) : N.dsrcTop ℓ φ z ≤ ((Fintype.card V * W : ℕ) : ℝ≥0∞) := by
  obtain ⟨a, p, hp⟩ := dsrc_lt_iff.1 (lt_top_iff_ne_top.2 h)
  obtain ⟨q, hq, hw⟩ := Walk.exists_nodup (lenTop ℓ) p
  have h₁ : offTop φ a ≠ ⊤ := fun h' => hp.ne (by rw [h', top_add])
  have h₂ : p.wt (lenTop ℓ) ≠ ⊤ := fun h' => hp.ne (by rw [h', add_top])
  have h₃ : q.wt (lenTop ℓ) ≠ ⊤ := ne_top_of_le_ne_top h₂ hw
  have h₄ : offTop φ a ≤ (W : ℝ≥0∞) := by
    have h₅ : φ a ≠ ⊤ := fun h' => h₁ (by simp [offTop, h'])
    simpa [offTop] using ENat.toENNReal_mono ((hv.2 a).resolve_left h₅)
  have h₆ := wt_top_add_le (fun a b hab => (hv.1 a b hab).imp_right fun h => h.2) q h₃
  have h₇ : q.support.length ≤ Fintype.card V := hq.length_le_card
  calc N.dsrcTop ℓ φ z ≤ offTop φ a + q.wt (lenTop ℓ) := dsrc_le_walk _ _ q
    _ ≤ q.wt (lenTop ℓ) + W := by rw [add_comm]; gcongr
    _ ≤ ((q.support.length * W : ℕ) : ℝ≥0∞) := h₆
    _ ≤ _ := by exact_mod_cast Nat.mul_le_mul_right W h₇

/-- An approximate answer for the lengths with `⊤` replaced by `M`, with values of at least `M`
replaced by `⊤`, is correct for the given lengths. -/
theorem capped_bounds {N : Net (Fin n)} {m W e M : ℕ} {ℓ : Fin n → Fin n → ℕ∞} {φ : Fin n → ℕ∞}
    (hv : OracleValid N m W ℓ φ) (he : 1 ≤ e) (hM : 2 * (n * W) < M) {z : Fin n} {q : ℕ∞}
    (h₁ : dsrc N.G.Adj (lenOf (lenCap M ℓ)) (offTop φ) z ≤ (q : ℝ≥0∞))
    (h₂ : (q : ℝ≥0∞) ≤ (1 + (e : ℝ≥0∞)⁻¹) * dsrc N.G.Adj (lenOf (lenCap M ℓ)) (offTop φ) z) :
    N.dsrcTop ℓ φ z ≤ (topAbove M q : ℝ≥0∞) ∧
      (topAbove M q : ℝ≥0∞) ≤ (1 + (e : ℝ≥0∞)⁻¹) * N.dsrcTop ℓ φ z := by
  have hle : dsrc N.G.Adj (lenOf (lenCap M ℓ)) (offTop φ) z ≤ N.dsrcTop ℓ φ z :=
    le_dsrc fun a p => (dsrc_le_walk _ _ p).trans (by
      gcongr
      exact Walk.wt_mono lenCap_le p)
  constructor
  · unfold topAbove
    split_ifs with hq
    · simp
    · have hqM : (q : ℝ≥0∞) < M := ENat.toENNReal_lt_natCast.2 (not_le.1 hq)
      refine le_trans ?_ h₁
      by_contra hc
      push Not at hc
      have hlt : dsrc N.G.Adj (lenOf (lenCap M ℓ)) (offTop φ) z < min (N.dsrcTop ℓ φ z) M :=
        lt_min hc (h₁.trans_lt hqM)
      obtain ⟨a, p, hp⟩ := dsrc_lt_iff.1 hlt
      have hpM : p.wt (lenOf (lenCap M ℓ)) < M :=
        (le_add_self.trans_lt hp).trans_le (min_le_right _ _)
      have h₃ : N.dsrcTop ℓ φ z ≤ offTop φ a + p.wt (lenOf (lenCap M ℓ)) := by
        rw [← wt_top_eq_of_lt p hpM]
        exact dsrc_le_walk _ _ p
      exact absurd (h₃.trans_lt (hp.trans_le (min_le_left _ _))) (lt_irrefl _)
  · by_cases hT : N.dsrcTop ℓ φ z = ⊤
    · rw [hT, ENNReal.mul_top (by simp)]
      exact le_top
    · have hB := dsrcTop_le hv hT
      rw [Fintype.card_fin] at hB
      have he' : (e : ℝ≥0∞)⁻¹ ≤ 1 := ENNReal.inv_le_one.2 (Nat.one_le_cast.2 he)
      have hq₂ : (q : ℝ≥0∞) ≤ (1 + (e : ℝ≥0∞)⁻¹) * N.dsrcTop ℓ φ z := by
        refine h₂.trans ?_
        gcongr
      have hq₃ : (q : ℝ≥0∞) < M := by
        refine (hq₂.trans (mul_le_mul' (add_le_add_right he' 1) hB)).trans_lt ?_
        have : (1 + 1 : ℝ≥0∞) * ((n * W : ℕ) : ℝ≥0∞) = ((2 * (n * W) : ℕ) : ℝ≥0∞) := by
          push_cast
          norm_num
        rw [this]
        exact_mod_cast hM
      have hq₄ : ¬ (M : ℕ∞) ≤ q := not_le.2 (ENat.toENNReal_lt_natCast.1 hq₃)
      unfold topAbove
      rw [ite_eq_right hq₄]
      exact hq₂

/-! ### The oracle -/

/-- The input of the labels: the arcs of a node with `⊤` replaced by `M`. -/
def toLocal (M : ℕ) (i : OracleIn (Fin n)) : LocalIn (Fin n) where
  nbrs := i.nbrs
  lenOut u := if u ∈ i.nbrs then capTop M (i.lenOut u) else 0
  lenIn u := if u ∈ i.nbrs then capTop M (i.lenIn u) else 0

theorem toLocal_oracleIn (N : Net (Fin n)) (ℓ : Fin n → Fin n → ℕ∞) (φ : Fin n → ℕ∞) (M : ℕ)
    (v : Fin n) : toLocal M (N.oracleIn ℓ φ v) = N.localIn (lenCap M ℓ) v := by
  simp only [toLocal, Net.oracleIn, Net.localIn, lenCap, N.mem_rotList]
  congr 1 <;>
  · funext u
    by_cases h : N.G.Adj v u <;> simp [h]

section Alg

variable {σL σa : Type} {B B₁ B₂ : ℕ}

/-- The oracle: the labels for `TL` rounds, then one aggregation. -/
noncomputable def labelOracle (AL : Algorithm (Fin n) (LocalIn (Fin n)) σL B₁)
    (outL : Fin n → σL → LabelOut (Fin n)) (Aa : Algorithm (Fin n) (AggIn (Fin n)) σa B₂) (M TL : ℕ)
    (h₁ : B₁ ≤ B) (h₂ : B₂ ≤ B) :
    Algorithm (Fin n) (OracleIn (Fin n))
      ((ℕ × (OracleIn (Fin n) × σL)) ⊕ ((LabelOut (Fin n) × ℕ∞) × σa)) B :=
  ((AL.keep fun _ i => toLocal M i).widen h₁).seq TL (fun v s => (outL v s.2, s.1.offset))
    ((Aa.keep fun _ j => labelAggIn j.1 j.2).widen h₂)

/-- The answer of the oracle. -/
noncomputable def labelOracleOut (outa : Fin n → σa → ℕ → ℕ → Option ℕ) (M : ℕ) :
    Fin n → ((ℕ × (OracleIn (Fin n) × σL)) ⊕ ((LabelOut (Fin n) × ℕ∞) × σa)) → ℕ∞
  | _, .inl _ => ⊤
  | v, .inr s => topAbove M (labelAnswer s.1.1 (outa v s.2))

theorem run_labelOracle (AL : Algorithm (Fin n) (LocalIn (Fin n)) σL B₁)
    (outL : Fin n → σL → LabelOut (Fin n)) (Aa : Algorithm (Fin n) (AggIn (Fin n)) σa B₂) (M TL Ta : ℕ)
    (h₁ : B₁ ≤ B) (h₂ : B₂ ≤ B) (N : Net (Fin n)) (ℓ : Fin n → Fin n → ℕ∞) (φ : Fin n → ℕ∞)
    (v : Fin n) :
    (labelOracle AL outL Aa M TL h₁ h₂).run N.G (N.oracleIn ℓ φ) (TL + Ta) v =
      .inr ((outL v (AL.run N.G (N.localIn (lenCap M ℓ)) TL v), φ v),
        Aa.run N.G (fun v => labelAggIn (outL v (AL.run N.G (N.localIn (lenCap M ℓ)) TL v)) (φ v))
          Ta v) := by
  have hloc : (fun v => toLocal M (N.oracleIn ℓ φ v)) = N.localIn (lenCap M ℓ) :=
    funext (toLocal_oracleIn N ℓ φ M)
  have hf : (fun v => (fun (v : Fin n) (s : OracleIn (Fin n) × σL) => (outL v s.2, s.1.offset)) v
      (((AL.keep fun _ i => toLocal M i).widen h₁).run N.G (N.oracleIn ℓ φ) TL v)) =
      fun v => (outL v (AL.run N.G (N.localIn (lenCap M ℓ)) TL v), φ v) := by
    funext w
    rw [Algorithm.run_widen, Algorithm.run_keep, hloc]
    rfl
  have h3 := congrFun (Algorithm.run_seq ((AL.keep fun _ i => toLocal M i).widen h₁) TL
    (fun v s => (outL v s.2, s.1.offset)) ((Aa.keep fun _ j => labelAggIn j.1 j.2).widen h₂)
    N.G (N.oracleIn ℓ φ) Ta) v
  rw [hf, Algorithm.run_widen, Algorithm.run_keep] at h3
  exact h3

end Alg

/-- An oracle for larger lengths and a better accuracy is an oracle for smaller ones. -/
theorem ApproxOracleOK.mono {σ : Type} {B W W' e e' D T : ℕ}
    {A : Algorithm (Fin n) (OracleIn (Fin n)) σ B} {out : Fin n → σ → ℕ∞}
    (h : ApproxOracleOK n W' e' D T A out) (hW : W ≤ W') (he : e ≤ e') :
    ApproxOracleOK n W e D T A out := by
  intro N ℓ φ hP hD hV v
  have hV' : OracleValid N 1 W' ℓ φ := by
    have hc : (W : ℕ∞) ≤ W' := by exact_mod_cast hW
    exact ⟨fun u w huw => (hV.1 u w huw).imp_right fun h => ⟨h.1, h.2.trans hc⟩,
      fun w => (hV.2 w).imp_right fun h => h.trans hc⟩
  obtain ⟨h₁, h₂⟩ := h N ℓ φ hP hD hV' v
  refine ⟨h₁, h₂.trans ?_⟩
  gcongr

/-- The oracle is correct, given correct labels and a correct aggregation. -/
theorem labelOracle_ok {σL σa : Type} {B B₁ B₂ e h s w b W M LW D TL Ta : ℕ}
    (AL : Algorithm (Fin n) (LocalIn (Fin n)) σL B₁) (outL : Fin n → σL → LabelOut (Fin n))
    (Aa : Algorithm (Fin n) (AggIn (Fin n)) σa B₂) (outa : Fin n → σa → ℕ → ℕ → Option ℕ)
    (h₁ : B₁ ≤ B) (h₂ : B₂ ≤ B)
    (hAL : ∀ (N : Net (Fin n)) (ℓ : Fin n → Fin n → ℕ), N.toRot.Planar → N.DiamLE D →
      N.LensIn ℓ LW → LabelsOK N ℓ e h s w (fun v => outL v (AL.run N.G (N.localIn ℓ) TL v)))
    (hAa : ∀ (N : Net (Fin n)) (inp : Fin n → AggIn (Fin n)), AggIn.Valid N inp s (2 * (h + 1)) s b →
      ∀ v, ∀ x ∈ (inp v).member, ∀ κ, AggIn.IsMin inp x κ (outa v (Aa.run N.G inp Ta v) x κ))
    (he : 1 ≤ e) (hb₁ : w ≤ b) (hb₂ : n ≤ 2 ^ b) (hb₃ : W + 2 ^ w ≤ 2 ^ b) (hM : 2 * (n * W) < M)
    (hMW : M ≤ LW) (hWW : W ≤ LW) :
    ApproxOracleOK n W e D (TL + Ta) (labelOracle AL outL Aa M TL h₁ h₂) (labelOracleOut outa M) := by
  intro N ℓ φ hP hD' hV v
  have hLens : N.LensIn (lenCap M ℓ) LW := by
    intro a a' haa
    simp only [lenCap]
    rcases hV.1 a a' haa with hT | ⟨h1, h2⟩
    · rw [hT, capTop_top]
      exact ⟨by omega, hMW⟩
    · have hne : ℓ a a' ≠ ⊤ := ne_top_of_le_ne_top (by simp) h2
      obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.1 hne
      rw [← hm] at h1 h2 ⊢
      rw [capTop_coe]
      have h1' : 1 ≤ m := by exact_mod_cast h1
      have h2' : m ≤ W := by exact_mod_cast h2
      exact ⟨h1', h2'.trans hWW⟩
  obtain ⟨Lw⟩ := hAL N (lenCap M ℓ) hP hD' hLens
  have hres := hAa N _ (labelAggIn_valid Lw (φ := φ) (W := W) (b := b) hV.2 hb₁ hb₂ hb₃)
  have hans := labelAnswer_eq Lw φ _ hres v
  obtain ⟨hq₁, hq₂⟩ := Lw.query_bound he (offTop φ) v
  rw [← hans] at hq₁ hq₂
  rw [run_labelOracle]
  exact capped_bounds hV he hM hq₁ hq₂

/-- **The approximate oracle.** From the labels and the aggregation, an oracle with accuracy `1/e` in
`Õ(D e)` rounds, with words of polylogarithmically many bits. -/
theorem approxOracle (hL : LabelHypothesis) (hA : AggBox) (K : ℕ) :
    ∃ g gB : ℕ → ℕ, PolyLog g ∧ PolyLog gB ∧ ∀ n e D : ℕ, 1 ≤ e → e ≤ (n + 2) ^ K → 1 ≤ D →
      ∃ (T : ℕ) (σ : Type) (A : Algorithm (Fin n) (OracleIn (Fin n)) σ (gB n))
        (out : Fin n → σ → ℕ∞), T ≤ g n * D * e ∧ ApproxOracleOK n ((n + 2) ^ K) e D T A out := by
  obtain ⟨C, c, hLK⟩ := hL (K + 2)
  obtain ⟨Ca, hAg⟩ := hA
  refine ⟨fun n => C * logN n ^ c + Ca * (2 * (C * logN n + 1)) * (2 * (C * logN n ^ c) + 1),
    fun n => C * logN n ^ c + Ca * (C * logN n ^ c + logN n * K + logN n + 1 + logN n), ?_, ?_, ?_⟩
  · exact (polyLog_pow C c).add (((PolyLog.const Ca).mul ((PolyLog.const 2).mul
      (((PolyLog.const C).mul polyLog_logN).add (PolyLog.const 1)))).mul
      (((PolyLog.const 2).mul (polyLog_pow C c)).add (PolyLog.const 1)))
  · exact (polyLog_pow C c).add ((PolyLog.const Ca).mul
      ((((((polyLog_pow C c).add (polyLog_logN.mul (PolyLog.const K))).add polyLog_logN)).add
        (PolyLog.const 1)).add polyLog_logN))
  intro n e D he heK hD
  have hX : 1 ≤ n + 2 := by omega
  obtain ⟨σL, AL, outL, hAL⟩ := hLK n e D he (heK.trans (Nat.pow_le_pow_right hX (by omega))) hD
  obtain ⟨σa, Aa, outa, hAa⟩ := hAg n (C * logN n ^ c * D) (2 * (C * logN n + 1))
    (C * logN n ^ c * D) (C * logN n ^ c + logN n * K + logN n + 1)
  have hlt := lt_two_pow_logN n
  have hb₂ : n ≤ 2 ^ (C * logN n ^ c + logN n * K + logN n + 1) :=
    (by omega : n ≤ n + 2).trans (hlt.le.trans (Nat.pow_le_pow_right (by norm_num) (by omega)))
  have hb₃ : (n + 2) ^ K + 2 ^ (C * logN n ^ c) ≤
      2 ^ (C * logN n ^ c + logN n * K + logN n + 1) := by
    have e₁ : (n + 2) ^ K ≤ 2 ^ (C * logN n ^ c + logN n * K) :=
      (pow_le_two_pow n K).trans (Nat.pow_le_pow_right (by norm_num) (by omega))
    have e₂ : 2 ^ (C * logN n ^ c) ≤ 2 ^ (C * logN n ^ c + logN n * K) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    have e₃ : 2 ^ (C * logN n ^ c + logN n * K + 1) ≤
        2 ^ (C * logN n ^ c + logN n * K + logN n + 1) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [pow_succ _ (C * logN n ^ c + logN n * K)] at e₃
    omega
  have hMX : 2 * (n * (n + 2) ^ K) + 1 ≤ (n + 2) ^ (K + 2) := by
    have hW1 : 1 ≤ (n + 2) ^ K := Nat.one_le_pow _ _ (by omega)
    rw [pow_add]
    generalize (n + 2) ^ K = P at hW1
    calc 2 * (n * P) + 1 ≤ (2 * n + 1) * P := by nlinarith
      _ ≤ (n + 2) ^ 2 * P := Nat.mul_le_mul_right _ (by nlinarith)
      _ = P * (n + 2) ^ 2 := mul_comm _ _
  refine ⟨_, _, _, _, ?_, labelOracle_ok AL outL Aa outa (Nat.le_add_right _ _)
    (Nat.le_add_left _ _) hAL hAa he (by omega) hb₂ hb₃ (M := 2 * (n * (n + 2) ^ K) + 1) (by omega)
    hMX (Nat.pow_le_pow_right hX (by omega))⟩
  beta_reduce
  generalize C * logN n ^ c = w
  generalize Ca * (2 * (C * logN n + 1)) = Z
  have h1 : w * D + w * D + 1 ≤ (2 * w + 1) * D * e := by
    calc w * D + w * D + 1 ≤ (2 * w + 1) * D := by nlinarith
      _ ≤ (2 * w + 1) * D * e := Nat.le_mul_of_pos_right _ he
  calc w * D * e + Z * (w * D + w * D + 1)
      ≤ w * D * e + Z * ((2 * w + 1) * D * e) := by gcongr
    _ = (w + Z * (2 * w + 1)) * D * e := by ring

end Congest

end SsspFlow
