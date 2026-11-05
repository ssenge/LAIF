import SsspFlow.NetAgg

/-!
# Names of bags by a flood over the darts

Each node holds a number for each of its darts. The corners of a level start with their codes, the other darts
with a large number. In a round each dart takes the least number on its sector and on the reverses of the darts
of its sector (`stF_succ`). After a number of rounds given by the diameter of the bags, each dart holds the least
code of a corner of its bag (`flood_spec`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace SsspFlow.Congest

open Cslib.Congest Cslib.Congest.Algorithm FourColor RotSystem RotSystem.RootedTree

variable {n : ℕ}

/-- The code of a dart at a node. -/
def cL (v : Fin n) (y : Fin n × Bool) : ℕ := codeRaw n v y.1 y.2

theorem cL_inj {v : Fin n} {y y' : Fin n × Bool} (h : cL v y = cL v y') : y = y' := by
  have h1 : nbrC n (cL v y) = y.1 := nbrC_codeRaw y.1.2 _
  have h2 : nbrC n (cL v y') = y'.1 := nbrC_codeRaw y'.1.2 _
  have h3 : (cL v y) % 2 = y.2.toNat := bit_codeRaw _ _ _ _
  have h4 : (cL v y') % 2 = y'.2.toNat := bit_codeRaw _ _ _ _
  refine Prod.ext (Fin.ext (by rw [← h1, ← h2, h])) ?_
  have h5 : y.2.toNat = y'.2.toNat := by rw [← h3, ← h4, h]
  rcases hx2 : y.2 with _ | _ <;> rcases hy2 : y'.2 with _ | _ <;> simp [hx2, hy2] at h5 ⊢

/-- The number of the reverse of a dart, from the pair received from its head. -/
def revOf (o : Option ℕ) (b : Bool) : ℕ :=
  if b then (Nat.unpair (o.getD 0)).1 else (Nat.unpair (o.getD 0)).2

open Classical in
/-- The flood at a node with corners `C`. -/
noncomputable def floodIn (W : ℕ) (v : Fin n) (rl : List (Fin n)) (C : Finset (Fin n × Bool)) :
    RelaxIn (Fin n) where
  init key := if ∃ y ∈ C, cL v y = key then key else W
  msg s w := Nat.pair (s (codeRaw n v w false)) (s (codeRaw n v w true))
  upd s rcv key := sInf {a | ∃ y y', cL v y = key ∧ y' ∈ ownL rl ∧
    secOf (rotV rl) C y = secOf (rotV rl) C y' ∧ (a = s (cL v y') ∨ a = revOf (rcv y'.1) y'.2)}

variable {N : Net (Fin n)} (B : ℕ) (W : ℕ) (Γd : Finset (N.G.Dart × Bool))

variable (N) in
/-- The inputs of all nodes. -/
noncomputable abbrev floodFam (W : ℕ) (Γd : Finset (N.G.Dart × Bool)) : Fin n → RelaxIn (Fin n) :=
  fun v => floodIn W v (N.rotList v) (N.cornersAt v Γd)

/-- The number of a dart in the flood. -/
noncomputable def stF (k : ℕ) (z : N.G.Dart × Bool) : ℕ :=
  relaxSt B N.G (floodFam N W Γd) k z.1.fst (N.codeN z)

theorem stF_zero (z : N.G.Dart × Bool) :
    stF B W Γd 0 z = if z ∈ Γd then N.codeN z else W := by
  classical
  show (if ∃ y ∈ N.cornersAt z.1.fst Γd, cL z.1.fst y = N.codeN z then N.codeN z else W) = _
  by_cases hz : z ∈ Γd
  · rw [if_pos hz, if_pos ⟨N.locN z, (N.mem_cornersAt rfl).2 hz, rfl⟩]
  · rw [if_neg hz, if_neg]
    rintro ⟨y, hy, he⟩
    obtain ⟨z', hz', rfl⟩ := Finset.mem_image.1 hy
    obtain ⟨h1, h2⟩ := Finset.mem_filter.1 hz'
    have h3 : N.codeN z' = N.codeN z := by
      unfold Net.codeN
      rw [h2]
      exact he
    exact hz (N.codeN_inj h3 ▸ h1)

theorem stF_eq {k : ℕ} {v : Fin n} {z : N.G.Dart × Bool} (hz : z.1.fst = v) :
    relaxSt B N.G (floodFam N W Γd) k v (cL v (N.locN z)) = stF B W Γd k z := by
  subst hz
  rfl

variable {B W Γd}

theorem rev_rcv {k : ℕ} (hfit : ∀ d : N.G.Dart, Nat.pair (stF B W Γd k (d, false)) (stF B W Γd k (d, true)) < 2 ^ B)
    {v : Fin n} {z : N.G.Dart × Bool} (hz : z.1.fst = v) :
    revOf ((fun u => if N.G.Adj u v then
      some (ofMsg (toMsg B ((floodFam N W Γd u).msg (relaxSt B N.G (floodFam N W Γd) k u) v))) else none)
        (N.locN z).1) (N.locN z).2 = stF B W Γd k (N.toRot.double.rev z) := by
  subst hz
  obtain ⟨d, b⟩ := z
  have hadj : N.G.Adj d.snd d.fst := d.adj.symm
  have hm : ofMsg (toMsg B ((floodFam N W Γd d.snd).msg (relaxSt B N.G (floodFam N W Γd) k d.snd) d.fst)) =
      Nat.pair (stF B W Γd k (d.symm, false)) (stF B W Γd k (d.symm, true)) :=
    ofMsg_toMsg (hfit d.symm)
  show revOf (if N.G.Adj d.snd d.fst then some (ofMsg (toMsg B ((floodFam N W Γd d.snd).msg
    (relaxSt B N.G (floodFam N W Γd) k d.snd) d.fst))) else none) b = _
  rw [if_pos hadj, hm]
  unfold revOf
  cases b
  · simp only [Option.getD_some, Bool.false_eq_true, if_false, Nat.unpair_pair]
    rfl
  · simp only [Option.getD_some, if_true, Nat.unpair_pair]
    rfl

variable (hG : N.G.Connected) (r : Fin n) (d₀ : N.G.Dart)

include hG r d₀ in
/-- **A round of the flood.** -/
theorem stF_succ {k : ℕ}
    (hfit : ∀ d : N.G.Dart, Nat.pair (stF B W Γd k (d, false)) (stF B W Γd k (d, true)) < 2 ^ B)
    (z : N.G.Dart × Bool) :
    stF B W Γd (k + 1) z = sInf {a | ∃ z' : N.G.Dart × Bool, z'.1.fst = z.1.fst ∧
      (N.toRot.double.split Γd).tail z = (N.toRot.double.split Γd).tail z' ∧
        (a = stF B W Γd k z' ∨ a = stF B W Γd k (N.toRot.double.rev z'))} := by
  have hsec := fun {x y : N.G.Dart × Bool} (hx : x.1.fst = z.1.fst) (hy : y.1.fst = z.1.fst) =>
    N.sec_iff (Γ := Γd) (N.treeN hG r d₀) (fun _ => rfl) hx hy
  show relaxSt B N.G (floodFam N W Γd) (k + 1) z.1.fst (N.codeN z) = _
  rw [relaxSt_succ]
  show sInf _ = _
  congr 1
  ext a
  simp only [Set.mem_setOf_eq]
  constructor
  · rintro ⟨y, y', hy, hy', hs, ha⟩
    obtain rfl : y = N.locN z := cL_inj hy
    obtain ⟨z', hz', rfl⟩ := exists_dart_of_own hy'
    refine ⟨z', hz', (hsec rfl hz').2 hs, ?_⟩
    rcases ha with rfl | rfl
    · exact Or.inl (stF_eq B W Γd hz')
    · exact Or.inr (rev_rcv hfit hz')
  · rintro ⟨z', hz', hs, ha⟩
    refine ⟨N.locN z, N.locN z', rfl, ?_, (hsec rfl hz').1 hs, ?_⟩
    · have := locN_mem_own z'
      rwa [hz'] at this
    · rcases ha with rfl | rfl
      · exact Or.inl (stF_eq B W Γd hz').symm
      · exact Or.inr (rev_rcv hfit hz').symm

variable {t : N.toRot.RootedTree (Fin n)} {w₀ : N.G.Dart × Bool} {Γ C : ℕ → Finset (N.G.Dart × Bool)}

theorem minCode_congr {D : Type*} [Fintype D] [DecidableEq D] {R : RotSystem D} {code : D × Bool → ℕ}
    {Γ : Finset (D × Bool)} {u u' : D × Bool} (h : R.Same Γ u u') :
    R.minCode code Γ u = R.minCode code Γ u' := by
  unfold minCode
  rw [portsOf_congr h]

include hG r d₀ in
/-- The bounds of a flood. -/
theorem stF_bounds (hW : ∀ z, N.codeN z < W) (hB : (W + 1) ^ 2 ≤ 2 ^ B)
    (hne : ∀ u, ∃ g ∈ Γd, N.toRot.Same Γd u g) (k : ℕ) (z : N.G.Dart × Bool) :
    N.toRot.minCode N.codeN Γd z ≤ stF B W Γd k z ∧ stF B W Γd k z ≤ W := by
  have hmc : ∀ z, N.toRot.minCode N.codeN Γd z ≤ W := fun z => by
    obtain ⟨g, hg, hs⟩ := hne z
    have h1 : N.toRot.minCode N.codeN Γd z ≤ N.codeN g :=
      Nat.sInf_le ⟨g, (mem_portsOf.2 ⟨hg, hs⟩), rfl⟩
    have := hW g
    omega
  induction k generalizing z with
  | zero =>
    rw [stF_zero]
    by_cases hz : z ∈ Γd
    · rw [if_pos hz]
      exact ⟨Nat.sInf_le ⟨z, mem_portsOf.2 ⟨hz, connect_refl _⟩, rfl⟩, (hW z).le⟩
    · rw [if_neg hz]
      exact ⟨hmc z, le_rfl⟩
  | succ k ih =>
    have hfit : ∀ d : N.G.Dart, Nat.pair (stF B W Γd k (d, false)) (stF B W Γd k (d, true)) < 2 ^ B :=
      fun d => by
        have h1 := Nat.pair_lt_max_add_one_sq (stF B W Γd k (d, false)) (stF B W Γd k (d, true))
        have h2 := (ih (d, false)).2
        have h3 := (ih (d, true)).2
        have h4 : (max (stF B W Γd k (d, false)) (stF B W Γd k (d, true)) + 1) ^ 2 ≤ (W + 1) ^ 2 :=
          Nat.pow_le_pow_left (by omega) 2
        omega
    rw [stF_succ hG r d₀ hfit z]
    have hmem : stF B W Γd k z ∈ {a | ∃ z' : N.G.Dart × Bool, z'.1.fst = z.1.fst ∧
        (N.toRot.double.split Γd).tail z = (N.toRot.double.split Γd).tail z' ∧
          (a = stF B W Γd k z' ∨ a = stF B W Γd k (N.toRot.double.rev z'))} :=
      ⟨z, rfl, rfl, Or.inl rfl⟩
    refine ⟨le_csInf ⟨_, hmem⟩ ?_, (Nat.sInf_le hmem).trans (ih z).2⟩
    rintro a ⟨z', -, hs, rfl | rfl⟩
    · rw [minCode_congr (same_of_dartLink (Or.inr hs))]
      exact (ih z').1
    · rw [minCode_congr (Same.trans (same_of_dartLink (Or.inr hs)) (same_rev Γd z'))]
      exact (ih _).1

section Steps

variable (hW : ∀ z, N.codeN z < W) (hB : (W + 1) ^ 2 ≤ 2 ^ B)
  (hne : ∀ u, ∃ g ∈ Γd, N.toRot.Same Γd u g)

include hG r d₀ hW hB hne in
theorem stF_fit (k : ℕ) (d : N.G.Dart) :
    Nat.pair (stF B W Γd k (d, false)) (stF B W Γd k (d, true)) < 2 ^ B := by
  have h1 := Nat.pair_lt_max_add_one_sq (stF B W Γd k (d, false)) (stF B W Γd k (d, true))
  have h2 := (stF_bounds hG r d₀ hW hB hne k (d, false)).2
  have h3 := (stF_bounds hG r d₀ hW hB hne k (d, true)).2
  have h4 : (max (stF B W Γd k (d, false)) (stF B W Γd k (d, true)) + 1) ^ 2 ≤ (W + 1) ^ 2 :=
    Nat.pow_le_pow_left (by omega) 2
  omega

include hG r d₀ hW hB hne in
theorem stF_step_le (k : ℕ) (z : N.G.Dart × Bool) : stF B W Γd (k + 1) z ≤ stF B W Γd k z := by
  rw [stF_succ hG r d₀ (stF_fit hG r d₀ hW hB hne k) z]
  exact Nat.sInf_le ⟨z, rfl, rfl, Or.inl rfl⟩

include hG r d₀ hW hB hne in
theorem stF_anti {k k' : ℕ} (h : k ≤ k') (z : N.G.Dart × Bool) : stF B W Γd k' z ≤ stF B W Γd k z := by
  induction k', h using Nat.le_induction with
  | base => exact le_rfl
  | succ k' _ ih => exact (stF_step_le hG r d₀ hW hB hne k' z).trans ih

include hG r d₀ hW hB hne in
theorem stF_link (k : ℕ) {x y : N.G.Dart × Bool} (h : N.toRot.dartLink Γd x y) :
    stF B W Γd (k + 1) x ≤ stF B W Γd k y := by
  rw [stF_succ hG r d₀ (stF_fit hG r d₀ hW hB hne k) x]
  rcases h with rfl | h
  · exact Nat.sInf_le ⟨x, rfl, rfl, Or.inr rfl⟩
  · have hv : y.1.fst = x.1.fst := (vertM_of_tail (t := N.treeN hG r d₀) h).symm
    exact Nat.sInf_le ⟨y, hv, h, Or.inl rfl⟩

include hG r d₀ hW hB hne in
theorem stF_walk {u a b : N.G.Dart × Bool} (p : Walk (N.toRot.bagLink Γd u) a b) (k : ℕ)
    (hk : p.support.length ≤ k + 1) : stF B W Γd k a ≤ stF B W Γd 0 b := by
  induction p generalizing k with
  | nil a => exact stF_anti hG r d₀ hW hB hne (Nat.zero_le k) a
  | cons e p ih =>
    have h1 : 0 < p.support.length := List.length_pos_of_mem p.start_mem
    simp only [Walk.support, List.length_cons] at hk
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    exact (stF_link hG r d₀ hW hB hne k' e.2).trans (ih k' (by omega))

end Steps

include hG r d₀ in
/-- **The flood gives the least code of a corner of the bag of each dart.** -/
theorem flood_spec (hD : t.Decomp w₀ Γ C) (hR : N.toRot.Planar) (hc : N.toRot.Connected) {h H d : ℕ}
    (hdep : ∀ v, t.dep v ≤ h) (hd : d ≤ H) (hW : ∀ z, N.codeN z < W) (hB : (W + 1) ^ 2 ≤ 2 ^ B) {Tr : ℕ}
    (hTr : (2 * H + 2) * (2 * (2 * h + 1 + 2 * (1 + H * (2 + 4 * h))) + 1) ≤ Tr) (z : N.G.Dart × Bool) :
    stF B W (Γ d) Tr z = N.toRot.minCode N.codeN (Γ d) z := by
  have hne := hD.exists_port hc d
  refine le_antisymm ?_ (stF_bounds hG r d₀ hW hB hne Tr z).1
  obtain ⟨g₁, hg₁, hs₁⟩ := hne z
  have hnon : (N.codeN '' (N.toRot.portsOf (Γ d) z : Set (N.G.Dart × Bool))).Nonempty :=
    ⟨_, g₁, mem_portsOf.2 ⟨hg₁, hs₁⟩, rfl⟩
  obtain ⟨g, hg, hgc⟩ := Nat.sInf_mem hnon
  obtain ⟨hgΓ, hs⟩ := mem_portsOf.1 hg
  obtain ⟨p, hp⟩ := hD.dart_span hR hc hdep hd (connect_refl _ : N.toRot.Same (Γ d) z z) hs
  calc stF B W (Γ d) Tr z ≤ stF B W (Γ d) _ z := stF_anti hG r d₀ hW hB hne hTr z
    _ ≤ stF B W (Γ d) 0 g := stF_walk hG r d₀ hW hB hne p _ hp
    _ = N.codeN g := by rw [stF_zero, if_pos hgΓ]
    _ = N.toRot.minCode N.codeN (Γ d) z := hgc

end SsspFlow.Congest
