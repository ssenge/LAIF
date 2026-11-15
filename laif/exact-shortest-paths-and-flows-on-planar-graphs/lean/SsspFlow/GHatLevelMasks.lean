import SsspFlow.GHatPieceAll
import SsspFlow.GHatChainCorners

/-!
# Inputs of a level at every identifier, from the values at the copies

The run on the pieces gives values at the identifiers of copies. The inputs of a level need values at
every identifier: the least index of the cut path at the piece of a copy and `⊤` elsewhere, and the
flags of a node, which are read at the copy of the node (`RData.copyAt`). The host of an identifier
decides from its own data whether the identifier names a copy, and which copy belongs to it: the
identifier itself for a copy, the first entry of its rotation list for the name of a dart, and the
star centre of the host otherwise.

* `RData.isCopyL`, `RData.isCopy_iff`: the local test for the identifiers of copies.
* `RData.cpIdL`, `RData.cpId_spec`: the identifier of the copy of an identifier, from local data.
* `RData.ixOf`, `RData.ixOf_spec`: the least index at the piece of each copy, `⊤` elsewhere, from the
  capped values of the run on the pieces.
* `RData.pieceFlag_iff`: a flag read at the copy of an identifier from the run on the pieces with
  values `0` and `⊤` is set exactly when a corner at the piece of that copy has the flag.
-/

set_option autoImplicit false

namespace SsspFlow

open FourColor SsspFlow.Congest
open scoped ENNReal

namespace RotSystem

namespace RData

/-- The local test for the identifier of a copy. -/
def isCopyL {n : ℕ} (R : List (Fin n)) (f g : Fin n → DInfo) (w : Fin n) (q : Fin n × Fin 21) : Bool :=
  rawReal R f g w q && decide (q.2.val < 5)

/-- The identifier of the copy that belongs to an identifier, from local data. -/
def cpIdL {n : ℕ} (R : List (Fin n)) (f g : Fin n → DInfo) (w : Fin n) (q : Fin n × Fin 21) :
    Fin (n * (n * 21)) :=
  if rawReal R f g w q then
    if q.2.val < 5 then idEquiv (w, q.1, q.2) else (rawAt R f g w q).headD (idEquiv (w, w, 0))
  else idEquiv (w, w, 0)

/-- The input `ixI` of a level from a capped value at a copy, `⊤` elsewhere. -/
noncomputable def ixOf (M : ℕ) (isC : Bool) (x : ℕ∞) : ℕ∞ := if isC then ENat.uncap M x else ⊤

variable {n : ℕ} {N : Net (Fin n)} (S : N.toRot.RData) (hN : ∀ u, ∃ w, N.G.Adj u w)

theorem idEquiv_host (a : Fin (n * (n * 21))) :
    idEquiv (hostOf a, (idEquiv.symm a).2.1, (idEquiv.symm a).2.2) = a :=
  idEquiv.apply_symm_apply a

theorem real_iff (a : Fin (n * (n * 21))) :
    rawReal (N.rotList (hostOf a)) (S.dinfoAt (hostOf a)) (fun u => S.dinfoAt u (hostOf a)) (hostOf a)
        ((idEquiv.symm a).2.1, (idEquiv.symm a).2.2) = true ↔ ∃ y, (S.levelPad hN).ι y = a := by
  rw [S.rawReal_iff]
  constructor
  · rintro ⟨y, hy⟩
    exact ⟨y, by rw [S.levelPad_ι, hy, idEquiv_host]⟩
  · rintro ⟨y, rfl⟩
    refine ⟨y, ?_⟩
    rw [S.levelPad_ι]
    unfold hostOf
    rw [Equiv.symm_apply_apply]

/-- **The local test for copies.** -/
theorem isCopy_iff (a : Fin (n * (n * 21))) :
    isCopyL (N.rotList (hostOf a)) (S.dinfoAt (hostOf a)) (fun u => S.dinfoAt u (hostOf a)) (hostOf a)
        ((idEquiv.symm a).2.1, (idEquiv.symm a).2.2) = true ↔ ∃ u, a = (S.levelPad hN).ι (.inl u) := by
  unfold isCopyL
  rw [Bool.and_eq_true, S.real_iff hN, decide_eq_true_iff]
  constructor
  · rintro ⟨⟨y, rfl⟩, hk⟩
    rcases y with v | x
    · exact ⟨v, rfl⟩
    · exfalso
      have := S.nameD_kind x
      rw [S.levelPad_ι, Equiv.symm_apply_apply] at hk
      exact absurd hk (by show ¬ (S.nameD x).2.2.val < 5; omega)
  · rintro ⟨u, rfl⟩
    refine ⟨⟨_, rfl⟩, ?_⟩
    rw [S.levelPad_ι, Equiv.symm_apply_apply]
    exact N.nameC_kind _

/-- **The copy of an identifier, from local data.** -/
theorem cpId_spec (a : Fin (n * (n * 21))) :
    ∃ v, cpIdL (N.rotList (hostOf a)) (S.dinfoAt (hostOf a)) (fun u => S.dinfoAt u (hostOf a)) (hostOf a)
        ((idEquiv.symm a).2.1, (idEquiv.symm a).2.2) = (S.levelPad hN).ι (.inl v) ∧
      S.copyAt hN a = S.vcopy v := by
  unfold cpIdL
  by_cases hr : rawReal (N.rotList (hostOf a)) (S.dinfoAt (hostOf a)) (fun u => S.dinfoAt u (hostOf a))
      (hostOf a) ((idEquiv.symm a).2.1, (idEquiv.symm a).2.2) = true
  · rw [ite_eq_left hr]
    obtain ⟨y, hy⟩ := (S.real_iff hN a).1 hr
    rcases y with v | x
    · have hk : ((idEquiv.symm a).2.2).val < 5 := by
        rw [← hy, S.levelPad_ι, Equiv.symm_apply_apply]
        exact N.nameC_kind _
      rw [ite_eq_left hk, idEquiv_host]
      refine ⟨v, hy.symm, ?_⟩
      rw [← hy, S.copyAt_ι]
      rfl
    · have hk : ¬ ((idEquiv.symm a).2.2).val < 5 := by
        rw [← hy, S.levelPad_ι, Equiv.symm_apply_apply]
        have := S.nameD_kind x
        show ¬ (S.nameD x).2.2.val < 5
        omega
      rw [ite_eq_right hk, ← S.levelNet_rotList_raw hN a, ← hy, S.levelNet_rotList_dart]
      refine ⟨S.hRot.tail x, rfl, ?_⟩
      rw [S.copyAt_ι]
      rfl
  · rw [ite_eq_right hr]
    have hnr : ¬ (S.levelPad hN).IsReal a := fun h => hr ((S.real_iff hN a).2 ⟨_, h.symm⟩)
    refine ⟨S.starV hN (hostOf a), (S.starV_name hN _).symm, ?_⟩
    unfold copyAt
    rw [S.back_of_not_real hN hnr]
    rfl

theorem cast_erMin (F : S.hRot.Vertex → ℕ∞) (v : S.hRot.Vertex) :
    (⨅ u, ⨅ (_ : Relation.ReflTransGen S.ER (S.vcopy u) (S.vcopy v)), ((F u : ℕ∞) : ℝ≥0∞)) =
      ((⨅ u, ⨅ (_ : Relation.ReflTransGen S.ER (S.vcopy u) (S.vcopy v)), F u : ℕ∞) : ℝ≥0∞) := by
  rw [ENat.toENNReal_iInf]
  exact iInf_congr fun u => (ENat.toENNReal_iInf _).symm

variable (C : N.toRot.dual.CutPath) (M : ℕ) (out : Fin (n * (n * 21)) → ℕ∞)

/-- **The least index at each piece, `⊤` elsewhere.** If the capped output of the run on the pieces at
every copy is the capped least value over the copies joined to it of `copyVal` of the least value of
`φ` over the indices of the cut path at a corner, with `φ r ≤ m` and `m < M`, then `ixOf` of the
output at the host of each identifier is `⊤` away from copies, `⊤` or below `M`, and at a copy at which
a token ends the least value of `φ` over the indices at its piece. -/
theorem ixOf_spec (φ : ℕ → ℕ∞) (hφ : ∀ r, r ≤ C.m → φ r ≤ C.m) (hM : C.m < M)
    (hpc : ∀ v, min (out ((S.levelPad hN).ι (.inl v)) : ℝ≥0∞) M =
      min (⨅ u, ⨅ (_ : Relation.ReflTransGen S.ER (S.vcopy u) (S.vcopy v)),
        ((S.copyVal (fun z => ⨅ r ∈ cornerIdx C z, φ r) (S.vcopy u) : ℕ∞) : ℝ≥0∞)) M) :
    (∀ a, (∀ u, a ≠ (S.levelPad hN).ι (.inl u)) →
      ixOf M (isCopyL (N.rotList (hostOf a)) (S.dinfoAt (hostOf a)) (fun u => S.dinfoAt u (hostOf a))
        (hostOf a) ((idEquiv.symm a).2.1, (idEquiv.symm a).2.2)) (out a) = ⊤) ∧
    (∀ a, ixOf M (isCopyL (N.rotList (hostOf a)) (S.dinfoAt (hostOf a)) (fun u => S.dinfoAt u (hostOf a))
        (hostOf a) ((idEquiv.symm a).2.1, (idEquiv.symm a).2.2)) (out a) = ⊤ ∨
      ixOf M (isCopyL (N.rotList (hostOf a)) (S.dinfoAt (hostOf a)) (fun u => S.dinfoAt u (hostOf a))
        (hostOf a) ((idEquiv.symm a).2.1, (idEquiv.symm a).2.2)) (out a) < M) ∧
    (∀ u (hu : ∃ x : S.Tok, S.IsEnd x.1 (S.vcopy u)),
      ixOf M (isCopyL (N.rotList (hostOf ((S.levelPad hN).ι (.inl u))))
        (S.dinfoAt (hostOf ((S.levelPad hN).ι (.inl u))))
        (fun w => S.dinfoAt w (hostOf ((S.levelPad hN).ι (.inl u)))) (hostOf ((S.levelPad hN).ι (.inl u)))
        ((idEquiv.symm ((S.levelPad hN).ι (.inl u))).2.1, (idEquiv.symm ((S.levelPad hN).ι (.inl u))).2.2))
        (out ((S.levelPad hN).ι (.inl u))) = ⨅ r ∈ S.cutIdx C ⟨S.vcopy u, hu⟩, φ r) := by
  refine ⟨fun a ha => ?_, fun a => ?_, fun u hu => ?_⟩
  · unfold ixOf
    rw [ite_eq_right]
    rw [S.isCopy_iff hN a]
    rintro ⟨u, rfl⟩
    exact ha u rfl
  · unfold ixOf ENat.uncap
    split_ifs with h1 h2
    · exact .inl rfl
    · exact .inr (not_le.1 h2)
    · exact .inl rfl
  · unfold ixOf
    rw [ite_eq_left ((S.isCopy_iff hN _).2 ⟨u, rfl⟩)]
    refine ENat.uncap_eq ?_ (S.cutIdx_top_or_lt C ⟨S.vcopy u, hu⟩ φ hφ hM)
    rw [hpc u, S.cast_erMin, ← S.cutIdx_pieceMin C φ u hu]

/-- **Flags at the copy of each identifier.** For values `g` that are `0` exactly at the corners with
a property `p` and `⊤` elsewhere, and a run on the pieces with `1 ≤ M` whose capped output at every
copy is the capped least value of `copyVal g` over the copies joined to it, the output at the copy of
an identifier is `0` exactly when a token ends at that copy and a corner at its piece has the
property. -/
theorem pieceFlag_iff (g : N.G.Dart × Bool → ℕ∞) (p : N.G.Dart × Bool → Prop)
    (hg : ∀ z, g z = 0 ↔ p z) (hg' : ∀ z, g z = 0 ∨ g z = ⊤) (hM : 1 ≤ M)
    (hpc : ∀ v, min (out ((S.levelPad hN).ι (.inl v)) : ℝ≥0∞) M =
      min (⨅ u, ⨅ (_ : Relation.ReflTransGen S.ER (S.vcopy u) (S.vcopy v)),
        ((S.copyVal g (S.vcopy u) : ℕ∞) : ℝ≥0∞)) M) (a : Fin (n * (n * 21))) :
    out (cpIdL (N.rotList (hostOf a)) (S.dinfoAt (hostOf a)) (fun u => S.dinfoAt u (hostOf a)) (hostOf a)
        ((idEquiv.symm a).2.1, (idEquiv.symm a).2.2)) = 0 ↔
      ∃ hy : (∃ x : S.Tok, S.IsEnd x.1 (S.copyAt hN a)),
        ∃ z, S.pieceAt z = S.pieceOf ⟨S.copyAt hN a, hy⟩ ∧ p z := by
  obtain ⟨v, hv, hc⟩ := S.cpId_spec hN a
  rw [hv]
  have hM' : (0 : ℝ≥0∞) < M := by exact_mod_cast hM
  have h0 : ∀ x : ℕ∞, x = 0 ↔ min (x : ℝ≥0∞) M = 0 := fun x => by
    rw [min_eq_iff]
    constructor
    · intro h; exact .inl ⟨by rw [h]; simp, by rw [h]; simp⟩
    · rintro (⟨h, -⟩ | ⟨h, -⟩)
      · exact_mod_cast h
      · exact absurd h hM'.ne'
  rw [h0, hpc v, S.cast_erMin, ← h0]
  generalize S.copyAt hN a = c at hc ⊢
  subst hc
  by_cases he : ∃ x : S.Tok, S.IsEnd x.1 (S.vcopy v)
  · rw [← S.pieceMin_eq g ⟨S.vcopy v, he⟩]
    constructor
    · intro h
      refine ⟨he, ?_⟩
      by_contra hn
      have : (⨅ z, ⨅ (_ : S.pieceAt z = S.pieceOf ⟨S.vcopy v, he⟩), g z) = ⊤ :=
        iInf_eq_top.2 fun z => iInf_eq_top.2 fun hz =>
          (hg' z).resolve_left fun h0 => hn ⟨z, hz, (hg z).1 h0⟩
      rw [this] at h
      exact ENat.top_ne_zero h
    · rintro ⟨_hy, z, hz, hp⟩
      exact le_antisymm (iInf_le_of_le z (iInf_le_of_le hz (le_of_eq ((hg z).2 hp)))) zero_le
  · constructor
    · intro h
      have e := S.erMin_noEnd g v he
      rw [S.cast_erMin] at e
      rw [h] at e
      exact absurd e (by simp)
    · rintro ⟨hy, -⟩
      exact absurd hy he

end RData

end RotSystem

end SsspFlow
