import SsspFlow.GHatLevelSssp
import SsspFlow.GHatPhase

/-!
# Components of a level from one shortest-path computation

Let every token length be `0` or at least `M`. Then every walk of `Ĝ_ℓ` has length `0` or at least
`M` (`RData.awt_zero_or`), and the walks of length `0` are the walks along zero arcs: E_R edges and the
E_C edges of tokens of length `0` (`RData.ZR`, `RData.arcDist_eq_zero_iff_rtg`). With token lengths
`0` the zero arcs are the E_R and E_C edges, with token lengths `M` they are the E_R edges.

Give every copy an offset below `M`, distinct for distinct copies. Then the distance from the virtual
source at a copy is the least offset of the copies joined to it by zero arcs (`RData.zlab_spec`), so two
copies get the same value exactly when they are joined by zero arcs (`RData.zlab_eq_iff`).

* `RData.levelConn_sim`: given the Exact SSSP bound, the nodes of the network compute such labels
  of the copies of a level in `C log^c n' · (12 D + 16)` rounds, with `n' = 21 n²`, if each node
  knows the edges and inputs at its own identifiers.
-/

set_option autoImplicit false

namespace SsspFlow

open FourColor SsspFlow.Congest
open scoped ENNReal

namespace RotSystem

namespace RData

section Zero

variable {E : Type} [Fintype E] [DecidableEq E] {G : RotSystem E} (S : G.RData) (lam : S.Tok → ℕ)
  (M : ℕ)

/-- A zero arc: an E_R edge, or the E_C edge of a token of length `0`. -/
def ZR (a b : Copy G.Vertex E) : Prop :=
  S.ER a b ∨ ∃ x : S.Tok, lam x = 0 ∧ S.att x.1 = a ∧ S.att (G.partner x.1) = b

theorem zr_symm (hl : ∀ x, lam (S.partnerTok x) = lam x) {a b : Copy G.Vertex E} (h : S.ZR lam a b) :
    S.ZR lam b a := by
  rcases h with h | ⟨x, hx, ha, hb⟩
  · exact .inl (S.er_symm h)
  · refine .inr ⟨S.partnerTok x, by rw [hl]; exact hx, hb, ?_⟩
    show S.att (G.partner (G.partner x.1)) = a
    rw [G.partner_partner]
    exact ha

theorem rtg_symm (hl : ∀ x, lam (S.partnerTok x) = lam x) {a b : Copy G.Vertex E}
    (h : Relation.ReflTransGen (S.ZR lam) a b) : Relation.ReflTransGen (S.ZR lam) b a := by
  induction h with
  | refl => exact .refl
  | tail _ hbc ih => exact Relation.ReflTransGen.head (S.zr_symm lam hl hbc) ih

theorem arcW_zero_or (hlam : ∀ x, lam x = 0 ∨ M ≤ lam x) {a b : Copy G.Vertex E} (e : S.Arc a b) :
    (S.arcW lam M a b e = 0 ∧ S.ZR lam a b) ∨ M ≤ S.arcW lam M a b e := by
  cases e with
  | er x => exact .inl ⟨rfl, .inl ⟨x, .inl ⟨rfl, rfl⟩⟩⟩
  | er' x => exact .inl ⟨rfl, .inl ⟨x, .inr ⟨rfl, rfl⟩⟩⟩
  | ec x =>
    rcases hlam x with h | h
    · exact .inl ⟨h, .inr ⟨x, h, rfl, rfl⟩⟩
    · exact .inr h
  | es h => exact .inr le_rfl
  | es' h => exact .inr le_rfl

/-- Every walk has length `0`, along zero arcs, or at least `M`. -/
theorem awt_zero_or (hlam : ∀ x, lam x = 0 ∨ M ≤ lam x) : ∀ {a b : Copy G.Vertex E}
    (q : FaceDisjoint.Walk S.Arc a b),
    (S.awt lam M q = 0 ∧ Relation.ReflTransGen (S.ZR lam) a b) ∨ M ≤ S.awt lam M q
  | _, _, .nil _ => .inl ⟨rfl, .refl⟩
  | _, _, .cons e q => by
    rcases S.arcW_zero_or lam M hlam e with ⟨h1, h2⟩ | h1
    · rcases awt_zero_or hlam q with ⟨h3, h4⟩ | h3
      · exact .inl ⟨by simp only [awt, h1, h3], Relation.ReflTransGen.head h2 h4⟩
      · exact .inr (by simp only [awt]; omega)
    · exact .inr (by simp only [awt]; omega)

theorem zeroWalk_of_rtg {a b : Copy G.Vertex E} (h : Relation.ReflTransGen (S.ZR lam) a b) :
    ∃ q : FaceDisjoint.Walk S.Arc a b, S.awt lam M q = 0 := by
  induction h with
  | refl => exact ⟨.nil _, rfl⟩
  | tail _ hbc ih =>
    obtain ⟨q, hq⟩ := ih
    rcases hbc with ⟨x, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ | ⟨x, hx, rfl, rfl⟩
    · exact ⟨q.append (.cons (.er x) (.nil _)), by rw [S.awt_append]; simp [awt, arcW, hq]⟩
    · exact ⟨q.append (.cons (.er' x) (.nil _)), by rw [S.awt_append]; simp [awt, arcW, hq]⟩
    · exact ⟨q.append (.cons (.ec x) (.nil _)), by rw [S.awt_append]; simp [awt, arcW, hq, hx]⟩

theorem arcDist_eq_zero_iff_rtg (hlam : ∀ x, lam x = 0 ∨ M ≤ lam x) (hM : 1 ≤ M)
    {a b : Copy G.Vertex E} : S.arcDist lam M a b = 0 ↔ Relation.ReflTransGen (S.ZR lam) a b := by
  constructor
  · intro h
    have h1 : S.arcDist lam M a b < 1 := by rw [h]; exact zero_lt_one
    obtain ⟨q, hq⟩ := iInf_lt_iff.1 h1
    have hq' : S.awt lam M q < 1 := by exact_mod_cast hq
    rcases S.awt_zero_or lam M hlam q with ⟨-, h2⟩ | h2
    · exact h2
    · omega
  · intro h
    obtain ⟨q, hq⟩ := S.zeroWalk_of_rtg lam M h
    exact le_antisymm (iInf_le_of_le q (by simp [hq])) bot_le

theorem le_arcDist (hlam : ∀ x, lam x = 0 ∨ M ≤ lam x) {a b : Copy G.Vertex E}
    (h : ¬ Relation.ReflTransGen (S.ZR lam) a b) : (M : ℝ≥0∞) ≤ S.arcDist lam M a b :=
  le_iInf fun q => by
    rcases S.awt_zero_or lam M hlam q with ⟨-, h'⟩ | h'
    · exact absurd h' h
    · exact_mod_cast h'

/-- With token lengths `0`, the zero arcs are the E_R and E_C edges. -/
theorem zr_zero : S.ZR (fun _ => 0) = S.ERC := by
  funext a b
  apply propext
  constructor
  · rintro (h | ⟨x, -, h⟩)
    · exact .inl h
    · exact .inr ⟨x, h⟩
  · rintro (h | ⟨x, h⟩)
    · exact .inl h
    · exact .inr ⟨x, rfl, h⟩

/-- With token lengths `M ≥ 1`, the zero arcs are the E_R edges. -/
theorem zr_const {M : ℕ} (hM : 1 ≤ M) : S.ZR (fun _ => M) = S.ER := by
  funext a b
  apply propext
  constructor
  · rintro (h | ⟨x, hx, -⟩)
    · exact h
    · have h0 : M = 0 := hx
      omega
  · exact .inl

end Zero

section Lab

variable {n : ℕ} {N : Net (Fin n)} (S : N.toRot.RData) (lam : S.Tok → ℕ) (M : ℕ)
  (φ : S.hRot.Vertex → ℕ)

/-- The least offset plus distance over all copies. -/
noncomputable def zlab (v : S.hRot.Vertex) : ℝ≥0∞ :=
  ⨅ u, (φ u : ℝ≥0∞) + S.arcDist lam M (S.vcopy u) (S.vcopy v)

/-- **The label of a copy is the least offset of the copies joined to it by zero arcs.** -/
theorem zlab_spec (hlam : ∀ x, lam x = 0 ∨ M ≤ lam x) (hφ : ∀ u, φ u < M) (v : S.hRot.Vertex) :
    ∃ w, Relation.ReflTransGen (S.ZR lam) (S.vcopy w) (S.vcopy v) ∧ S.zlab lam M φ v = φ w ∧
      ∀ u, Relation.ReflTransGen (S.ZR lam) (S.vcopy u) (S.vcopy v) → φ w ≤ φ u := by
  classical
  have hM : 1 ≤ M := by have := hφ v; omega
  obtain ⟨w, hw, hmin⟩ := (Finset.univ.filter fun u =>
    Relation.ReflTransGen (S.ZR lam) (S.vcopy u) (S.vcopy v)).exists_min_image φ
    ⟨v, by simp [Relation.ReflTransGen.refl]⟩
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw hmin
  refine ⟨w, hw, le_antisymm ?_ ?_, hmin⟩
  · refine iInf_le_of_le w ?_
    rw [(S.arcDist_eq_zero_iff_rtg lam M hlam hM).2 hw, add_zero]
  · refine le_iInf fun u => ?_
    by_cases hu : Relation.ReflTransGen (S.ZR lam) (S.vcopy u) (S.vcopy v)
    · exact le_add_right (by exact_mod_cast hmin u hu)
    · refine le_add_left ((?_ : (φ w : ℝ≥0∞) ≤ M).trans (S.le_arcDist lam M hlam hu))
      exact_mod_cast (hφ w).le

/-- **Two copies have the same label exactly when they are joined by zero arcs.** -/
theorem zlab_eq_iff (hlam : ∀ x, lam x = 0 ∨ M ≤ lam x) (hl : ∀ x, lam (S.partnerTok x) = lam x)
    (hφ : ∀ u, φ u < M) (hinj : Function.Injective φ) (u v : S.hRot.Vertex) :
    S.zlab lam M φ u = S.zlab lam M φ v ↔ Relation.ReflTransGen (S.ZR lam) (S.vcopy u) (S.vcopy v) := by
  obtain ⟨w, hw, hu, hwm⟩ := S.zlab_spec lam M φ hlam hφ u
  obtain ⟨w', hw', hv, hwm'⟩ := S.zlab_spec lam M φ hlam hφ v
  rw [hu, hv]
  constructor
  · intro h
    obtain rfl := hinj (by exact_mod_cast h)
    exact (S.rtg_symm lam hl hw).trans hw'
  · intro h
    have h1 := hwm' w (hw.trans h)
    have h2 := hwm w' (hw'.trans (S.rtg_symm lam hl h))
    rw [le_antisymm h2 h1]

end Lab


section LevelConn

variable {n : ℕ} {N : Net (Fin n)} (S : N.toRot.RData) (hN : ∀ u, ∃ w, N.G.Adj u w)
  (lam : S.Tok → ℕ) (M : ℕ)

/-- With offsets only at copies, the distance from the virtual source at a copy is the least offset
plus distance in `Ĝ_ℓ`. -/
theorem dsrcTop_copies (ψ : Fin (n * (n * 21)) → ℕ∞)
    (hψ : ∀ z, (∀ u, z ≠ (S.levelPad hN).ι (.inl u)) → ψ z = ⊤) (v : S.hRot.Vertex) :
    (S.levelNet hN).dsrcTop (S.levelLen hN lam M) ψ ((S.levelPad hN).ι (.inl v)) =
      ⨅ u, (ψ ((S.levelPad hN).ι (.inl u)) : ℝ≥0∞) + S.arcDist lam M (S.vcopy u) (S.vcopy v) := by
  unfold Net.dsrcTop dsrc
  apply le_antisymm
  · refine le_iInf fun u => iInf_le_of_le ((S.levelPad hN).ι (.inl u)) ?_
    simp only [offTop, S.levelNet_dist hN lam M u v, le_refl]
  · refine le_iInf fun a => ?_
    by_cases ha : ∃ u, a = (S.levelPad hN).ι (.inl u)
    · obtain ⟨u, rfl⟩ := ha
      refine iInf_le_of_le u ?_
      simp only [offTop, S.levelNet_dist hN lam M u v, le_refl]
    · simp only [not_exists] at ha
      simp [offTop, hψ a ha]

/-- The offset of a copy for its label: distinct for distinct copies and below `n'`. -/
noncomputable def copyOff (u : S.hRot.Vertex) : ℕ :=
  n * (n * 21) - 1 - ((S.levelPad hN).ι (.inl u)).val

theorem copyOff_lt (u : S.hRot.Vertex) : S.copyOff hN u < n * (n * 21) := by
  have := ((S.levelPad hN).ι (.inl u)).isLt
  unfold copyOff
  omega

theorem copyOff_injective : Function.Injective (S.copyOff hN) := by
  intro u v h
  have h1 := ((S.levelPad hN).ι (.inl u)).isLt
  have h2 := ((S.levelPad hN).ι (.inl v)).isLt
  unfold copyOff at h
  have h3 : (S.levelPad hN).ι (.inl u) = (S.levelPad hN).ι (.inl v) := Fin.ext (by omega)
  have h4 := congrArg (S.levelPad hN).back h3
  rw [(S.levelPad hN).back_ι, (S.levelPad hN).back_ι] at h4
  exact Sum.inl_injective h4

open Classical in
/-- The offsets of the label computation: the offset of a copy at its identifier, `∞` elsewhere. -/
noncomputable def labOff (z : Fin (n * (n * 21))) : ℕ∞ :=
  if ∃ u, z = (S.levelPad hN).ι (.inl u) then ((n * (n * 21) - 1 - z.val : ℕ) : ℕ∞) else ⊤

theorem labOff_ι (u : S.hRot.Vertex) :
    S.labOff hN ((S.levelPad hN).ι (.inl u)) = (S.copyOff hN u : ℕ∞) := by
  unfold labOff
  rw [ite_cond_eq_true _ _ (eq_true ⟨u, rfl⟩)]
  rfl

theorem labOff_le (z : Fin (n * (n * 21))) : S.labOff hN z = ⊤ ∨ S.labOff hN z < n * (n * 21) := by
  unfold labOff
  split_ifs with h
  · obtain ⟨u, rfl⟩ := h
    exact .inr (by exact_mod_cast S.copyOff_lt hN u)
  · exact .inl rfl

/-- **The distance from the virtual source with the label offsets is the label.** -/
theorem dsrcTop_labOff (v : S.hRot.Vertex) :
    (S.levelNet hN).dsrcTop (S.levelLen hN lam M) (S.labOff hN) ((S.levelPad hN).ι (.inl v)) =
      S.zlab lam M (S.copyOff hN) v := by
  classical
  rw [S.dsrcTop_copies hN lam M _ (fun z hz => by
    unfold labOff
    rw [ite_cond_eq_false _ _ (eq_false (fun ⟨u, hu⟩ => hz u hu))]) v]
  simp only [S.labOff_ι hN, ENat.toENNReal_coe]
  rfl

end LevelConn

/-- **Components of a level.** Given the Exact SSSP bound, one algorithm, fixed for `n` and `D`, run
by the nodes of every connected plane network on `n` nodes of diameter at most `D` on the network of
a level, gives two copies the same output exactly when they are joined by zero arcs of `Ĝ_ℓ`, in
`C log^c n' · (12 D + 16)` rounds with messages of four times the width, if each node knows the edges
and inputs at its own identifiers. Here every token length is `0` or at least `M`, the same for the
two tokens of a pair, and `n' ≤ M`, with lengths at most `(n' + 2) ^ K`. -/
theorem levelConn_sim (hE : ExactSsspBound) (K : ℕ) : ∃ C c : ℕ, ∀ n D : ℕ,
    ∃ (σ : Type) (A : Cslib.Congest.Algorithm (Fin (n * (n * 21))) (OracleIn (Fin (n * (n * 21)))) σ
      (C * logN (n * (n * 21)) ^ c)) (out : Fin (n * (n * 21)) → σ → ℕ∞ × Option (Fin (n * (n * 21)))),
    ∀ (I : Type) (view : I → Fin (n * (n * 21)) → Fin (n * (n * 21)) → Prop)
      (vin : Fin n → I → Fin (n * (n * 21)) → OracleIn (Fin (n * (n * 21)))),
    ∀ (N : Net (Fin n)) (S : N.toRot.RData) (hN : ∀ u, ∃ w, N.G.Adj u w) (lam : S.Tok → ℕ) (M : ℕ)
      (inp : Fin n → I),
      N.toRot.Planar → N.toRot.Connected → S.NoConflict → S.cut.card ≤ 3 → N.DiamLE D →
      (∀ x, lam x = 0 ∨ M ≤ lam x) → (∀ x, lam (S.partnerTok x) = lam x) → n * (n * 21) ≤ M →
      (∀ x, lam x ≤ (n * (n * 21) + 2) ^ K) → M ≤ (n * (n * 21) + 2) ^ K →
      (∀ a, (S.levelNet hN).oracleIn (S.levelLen hN lam M) (S.labOff hN) a =
        vin (hostOf a) (inp (hostOf a)) a) →
      (∀ w b a, (hostOf b = w ∨ hostOf a = w) → (view (inp w) b a ↔ (S.levelNet hN).G.Adj b a)) →
      ∀ u v : S.hRot.Vertex,
        (out ((S.levelPad hN).ι (.inl u))
          (((Cslib.Congest.Algorithm.simulateView (k := 4) A hostOf view vin).run N.G inp
            (C * logN (n * (n * 21)) ^ c * (12 * D + 16)) (hostOf ((S.levelPad hN).ι (.inl u)))).2
              ((S.levelPad hN).ι (.inl u)))).1 =
        (out ((S.levelPad hN).ι (.inl v))
          (((Cslib.Congest.Algorithm.simulateView (k := 4) A hostOf view vin).run N.G inp
            (C * logN (n * (n * 21)) ^ c * (12 * D + 16)) (hostOf ((S.levelPad hN).ι (.inl v)))).2
              ((S.levelPad hN).ι (.inl v)))).1 ↔
          Relation.ReflTransGen (S.ZR lam) (S.vcopy u) (S.vcopy v) := by
  obtain ⟨C, c, hC⟩ := hE K
  refine ⟨C, c, fun n D => ?_⟩
  obtain ⟨σ, A, out, hA⟩ := hC (n * (n * 21)) (12 * D + 16) (by omega)
  refine ⟨σ, A, out, fun I view vin N S hN lam M inp hP hc hS hcut hD hlam hl hn hlamW hMW hin hview
    u v => ?_⟩
  have key : ∀ x : S.hRot.Vertex, ((out ((S.levelPad hN).ι (.inl x))
      (((Cslib.Congest.Algorithm.simulateView (k := 4) A hostOf view vin).run N.G inp
        (C * logN (n * (n * 21)) ^ c * (12 * D + 16)) (hostOf ((S.levelPad hN).ι (.inl x)))).2
          ((S.levelPad hN).ι (.inl x)))).1 : ℝ≥0∞) = S.zlab lam M (S.copyOff hN) x := by
    intro x
    have hval : OracleValid (S.levelNet hN) 0 ((n * (n * 21) + 2) ^ K) (S.levelLen hN lam M)
        (S.labOff hN) := by
      refine ⟨(S.oracleValid_level hN lam M hlamW hMW x).1, fun z => ?_⟩
      rcases S.labOff_le hN z with h | h
      · exact .inl h
      · exact .inr (h.le.trans (by exact_mod_cast (hn.trans hMW)))
    rw [S.run_levelSim hN A view vin inp _ hin hview _ _ _ rfl,
      (hA (S.levelNet hN) (S.levelLen hN lam M) (S.labOff hN) (S.levelNet_planar hN hP hc hS hcut hD)
        (S.levelNet_diam hN hcut hD) hval).dist_eq, S.dsrcTop_labOff]
  rw [← ENat.toENNReal_inj, key, key]
  exact S.zlab_eq_iff lam M (S.copyOff hN) hlam hl
    (fun w => (S.copyOff_lt hN w).trans_le hn) (S.copyOff_injective hN) u v

end RData

end RotSystem

end SsspFlow
