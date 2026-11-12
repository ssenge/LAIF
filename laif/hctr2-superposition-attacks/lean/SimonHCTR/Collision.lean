import SimonHCTR.Shift

/-!
# Collisions of `g = Enc + id` (deterministic part of Propositions 7, 8, 9)

For each scheme, `g(x) = Enc(x) + x` is invariant under the hidden subgroup. Here we
show which equations on the block functions a collision of `g` outside the hidden
subgroup forces; the probability bounds of the notes count the solutions of these
equations.

* HCTR2 (Proposition 7): `g M N = G (S (M + H N))` with `S y = y + E y + L` and
  `G S = (S + L + lam (X S), X S)`. `G` is injective when the first keystream block
  is an injective function of `S`, and a collision with shift `(a, δ)` happens iff
  `E y + E (y + u) = u` for `y = M + H N`, `u = a + lam δ`.
* CHCTR (Proposition 8): `g` is a function `Φ` of the quotient coordinates
  `y = MM₁ = M + H₁ N` and `z = Λ N = lam₁ N + lam₂ N`, and a collision
  `Φ (y + u) (z + w) = Φ y z` forces one of three equations.
* HCTR++ (Proposition 9): a collision of the rest of `g` forces either a collision of
  the middle value `cc` with a nonzero change of the rekeying input, or a collision
  of the keystream function `KS`.
-/

namespace SimonHCTR

variable {K : Type*} [CommRing K] [CharP K 2] {l : ℕ}

/-- In characteristic two, `a = b` iff `a + b = 0`, so an equation can be moved across. -/
theorem eq_iff_of_add_eq {a b c d : K} (h : a + b = c + d) : a = b ↔ c = d := by
  rw [← CharTwo.add_eq_zero, h, CharTwo.add_eq_zero]

/-! ## HCTR2 -/

namespace HCTR2Key

variable (k : HCTR2Key K l)

omit [CharP K 2] in
theorem enc_fst (M : K) (N : Fin l → K) :
    (k.enc M N).1 = k.E (M + k.H N) + k.H (N + k.X (k.Sval (M + k.H N))) := rfl

omit [CharP K 2] in
theorem enc_snd (M : K) (N : Fin l → K) :
    (k.enc M N).2 = N + k.X (k.Sval (M + k.H N)) := rfl

/-- The function `g = Enc + id` whose period group is the hidden subgroup. -/
def g (M : K) (N : Fin l → K) : K × (Fin l → K) := k.enc M N + (M, N)

/-- `g` as a function of the middle value `S`: `G S = (S + L + lam (X S), X S)`. -/
def Gfun (S : K) : K × (Fin l → K) := (S + k.L + k.lam (k.X S), k.X S)

/-- `g M N = G (S (M + H N))`: `g` depends on `(M, N)` only through `S = MM + E MM + L`. -/
theorem g_eq (M : K) (N : Fin l → K) : k.g M N = k.Gfun (k.Sval (M + k.H N)) := by
  refine Prod.ext ?_ ?_
  · simp only [g, Prod.fst_add, enc_fst, Gfun, Sval, H, map_add]
    char2_lc
  · simp only [g, Prod.snd_add, enc_snd, Gfun]
    rw [add_comm N, add_assoc, vec_add_self, add_zero]

omit [CharP K 2] in
/-- If the first keystream block is an injective function of `S`, then `G` is injective. -/
theorem Gfun_injective [NeZero l] (hX : Function.Injective (fun S => k.X S 0)) :
    Function.Injective k.Gfun := by
  intro S S' h
  have h2 : k.X S = k.X S' := congrArg Prod.snd h
  exact hX (congrFun h2 0)

/-- Proposition 7, deterministic part: a collision of `g` under the shift `(a, δ)` happens
iff `E y + E (y + u) = u` with `y = M + H N` and `u = a + lam δ`, for an arbitrary block
function `E`, when the first keystream block is injective in `S`. -/
theorem g_collision_iff [NeZero l] (hX : Function.Injective (fun S => k.X S 0))
    (M a : K) (N δ : Fin l → K) :
    k.g (M + a) (N + δ) = k.g M N ↔
      k.E (M + k.H N) + k.E (M + k.H N + (a + k.lam δ)) = a + k.lam δ := by
  rw [g_eq, g_eq, (k.Gfun_injective hX).eq_iff]
  have hy : M + a + k.H (N + δ) = M + k.H N + (a + k.lam δ) := by
    rw [H_add]; abel
  rw [hy]
  apply eq_iff_of_add_eq
  simp only [Sval]
  char2_lc

end HCTR2Key

/-! ## CHCTR -/

section CHCTR

variable (k1 k2 : HCTR2Key K l)

/-- The layer-2 middle value `m = MM₂ = E₁ y + z + Λ (X₁ (S₁ y)) + c` in the quotient
coordinates `(y, z)`, with `Λ = lam₁ + lam₂` and `c = c₁ + c₂`. -/
def chctrMid (y z : K) : K :=
  k1.E y + z + (k1.lam + k2.lam) (k1.X (k1.Sval y)) + (k1.c + k2.c)

/-- The rest part `A = X₁ (S₁ y) + X₂ (S₂ m)` of `g` for CHCTR. -/
def chctrA (y z : K) : Fin l → K :=
  k1.X (k1.Sval y) + k2.X (k2.Sval (chctrMid k1 k2 y z))

/-- The function `Φ` of Proposition 8: `g` of CHCTR in the quotient coordinates,
`Φ y z = (E₂ m + y + z + lam₂ A + c, A)` with `m = chctrMid y z`, `A = chctrA y z`,
`c = c₁ + c₂`. -/
def chctrPhi (y z : K) : K × (Fin l → K) :=
  (k2.E (chctrMid k1 k2 y z) + y + z + k2.lam (chctrA k1 k2 y z) + (k1.c + k2.c),
    chctrA k1 k2 y z)

/-- `g = Enc + id` of CHCTR equals `Φ` of the quotient coordinates `y = M + H₁ N` and
`z = lam₁ N + lam₂ N`. -/
theorem chctr_g_eq (M : K) (N : Fin l → K) :
    chctrEnc k1 k2 M N + (M, N) = chctrPhi k1 k2 (M + k1.H N) (k1.lam N + k2.lam N) := by
  set y := M + k1.H N with hy
  set z := k1.lam N + k2.lam N with hz
  have hm : (k1.enc M N).1 + k2.H (k1.enc M N).2 = chctrMid k1 k2 y z := by
    rw [HCTR2Key.enc_fst, HCTR2Key.enc_snd, ← hy]
    simp only [chctrMid, HCTR2Key.H, map_add, AddMonoidHom.add_apply, hz]
    abel
  unfold chctrEnc
  refine Prod.ext ?_ ?_
  · rw [Prod.fst_add, HCTR2Key.enc_fst, hm, HCTR2Key.enc_snd, ← hy]
    simp only [chctrPhi, chctrA, HCTR2Key.H, map_add, hy, hz]
    char2_lc
  · rw [Prod.snd_add, HCTR2Key.enc_snd, hm, HCTR2Key.enc_snd, ← hy]
    simp only [chctrPhi, chctrA]
    funext i
    simp only [Pi.add_apply]
    char2_lc

/-- The difference `γ = S₂ m' + S₂ m` of the layer-2 middle values in the third case of
Proposition 8; it depends on `y` and `u` only (not on `z`, nor on `w`). -/
def chctrGamma (y u : K) : K :=
  k1.Sval y + k1.Sval (y + u) +
    (k1.lam + k2.lam) (k1.X (k1.Sval y) + k1.X (k1.Sval (y + u)))

theorem chctrMid_add (y z u w : K) :
    chctrMid k1 k2 (y + u) (z + w) + chctrMid k1 k2 y z =
      k1.E y + k1.E (y + u) + w +
        (k1.lam + k2.lam) (k1.X (k1.Sval y) + k1.X (k1.Sval (y + u))) := by
  simp only [chctrMid, map_add]
  char2_lc

/-- Proposition 8, deterministic part (CHCTR). Let `E₁, E₂` be injective and let the
first keystream block of each layer be `Xᵢ S 0 = Eᵢ (S + 1)` (XCTR). If
`Φ (y + u) (z + w) = Φ y z`, then with `m = chctrMid y z` one of the following holds:
* `u = 0` and `E₂ m + E₂ (m + w) = w` (a differential of `E₂`),
* `u ≠ 0` and `E₁ y + E₁ (y + u) = u` (a differential of `E₁`),
* `u ≠ 0` and, with `σ = S₂ m + 1`, `γ = chctrGamma y u ≠ 0` (independent of `z`) and
  `Δ = X₁ (S₁ y) 0 + X₁ (S₁ (y + u)) 0 ≠ 0`, `E₂ σ + E₂ (σ + γ) = Δ`. -/
theorem chctr_collision_cases [NeZero l]
    (hE1 : Function.Injective k1.E) (hE2 : Function.Injective k2.E)
    (hX1 : ∀ S, k1.X S 0 = k1.E (S + 1)) (hX2 : ∀ S, k2.X S 0 = k2.E (S + 1))
    (y z u w : K) (hcol : chctrPhi k1 k2 (y + u) (z + w) = chctrPhi k1 k2 y z) :
    (u = 0 ∧ k2.E (chctrMid k1 k2 y z) + k2.E (chctrMid k1 k2 y z + w) = w) ∨
    (u ≠ 0 ∧ k1.E y + k1.E (y + u) = u) ∨
    (u ≠ 0 ∧ chctrGamma k1 k2 y u ≠ 0 ∧
      k1.X (k1.Sval y) 0 + k1.X (k1.Sval (y + u)) 0 ≠ 0 ∧
      k2.E (k2.Sval (chctrMid k1 k2 y z) + 1) +
        k2.E (k2.Sval (chctrMid k1 k2 y z) + 1 + chctrGamma k1 k2 y u) =
      k1.X (k1.Sval y) 0 + k1.X (k1.Sval (y + u)) 0) := by
  -- injectivity of the first keystream blocks
  have hX1inj : ∀ S S', k1.X S 0 = k1.X S' 0 → S = S' := by
    intro S S' h; rw [hX1, hX1] at h; exact add_right_cancel (hE1 h)
  have hX2inj : ∀ S S', k2.X S 0 = k2.X S' 0 → S = S' := by
    intro S S' h; rw [hX2, hX2] at h; exact add_right_cancel (hE2 h)
  set m := chctrMid k1 k2 y z with hm
  set m' := chctrMid k1 k2 (y + u) (z + w) with hm'
  have hA : chctrA k1 k2 (y + u) (z + w) = chctrA k1 k2 y z := congrArg Prod.snd hcol
  have hfst := congrArg Prod.fst hcol
  simp only [chctrPhi, hA] at hfst
  -- the two layer-2 outputs differ by `u + w`
  have hE2diff : k2.E m' + k2.E m = u + w := by
    rw [← hm, ← hm'] at hfst
    char2_lc hfst
  have hA' : k1.X (k1.Sval (y + u)) + k2.X (k2.Sval m') =
      k1.X (k1.Sval y) + k2.X (k2.Sval m) := hA
  by_cases hu : u = 0
  · -- first case
    left
    refine ⟨hu, ?_⟩
    subst hu
    rw [add_zero] at hA'
    have hX : k2.X (k2.Sval m') = k2.X (k2.Sval m) := add_left_cancel hA'
    have hS : k2.Sval m' = k2.Sval m := hX2inj _ _ (congrFun hX 0)
    have hmw : m' = m + w := by
      simp only [hm, hm', chctrMid, add_zero]; abel
    rw [← hmw]
    have := (eq_iff_of_add_eq (a := k2.Sval m') (b := k2.Sval m)
      (c := k2.E m + k2.E m') (d := w) ?_).1 hS
    · exact this
    simp only [HCTR2Key.Sval, hmw]
    char2_lc
  · by_cases hS1 : k1.Sval y = k1.Sval (y + u)
    · -- second case
      right; left
      refine ⟨hu, ?_⟩
      refine (eq_iff_of_add_eq ?_).1 hS1
      simp only [HCTR2Key.Sval]
      char2_lc
    · -- third case
      right; right
      have hγ : k2.Sval m' = k2.Sval m + chctrGamma k1 k2 y u := by
        have h1 := chctrMid_add k1 k2 y z u w
        rw [← hm, ← hm'] at h1
        simp only [HCTR2Key.Sval, chctrGamma] at h1 ⊢
        char2_lc h1 + hE2diff
      have hΔ : k1.X (k1.Sval y) 0 + k1.X (k1.Sval (y + u)) 0 ≠ 0 := by
        intro h0
        exact hS1 (hX1inj _ _ (CharTwo.add_eq_zero.1 h0))
      refine ⟨hu, ?_, hΔ, ?_⟩
      · intro h0
        rw [h0, add_zero] at hγ
        rw [hγ] at hA'
        exact hS1 (hX1inj _ _ (congrFun (add_right_cancel hA') 0)).symm
      · have h0 := congrFun hA' 0
        simp only [Pi.add_apply, hγ, hX2] at h0
        rw [add_right_comm (k2.Sval m) (chctrGamma k1 k2 y u) 1] at h0
        char2_lc h0

end CHCTR

/-! ## HCTR++ -/

namespace HCTRppKey

variable (k : HCTRppKey K l)

/-- The rest part of `g = Enc + id` of HCTR++ is `KS cc` with `cc = F re pp1`, where
`pp1 = b1 + x1.1` and `re = x1.2` for `x1 = c1 + Λ1 R`. -/
theorem enc_rest_add (b1 : K) (R : Fin l → K × K) :
    (k.enc b1 R).2 + R =
      k.KS (k.F (k.c1 + k.Λ1 R).2 (b1 + (k.c1 + k.Λ1 R).1)) := by
  simp only [enc]
  rw [add_comm R, add_assoc, vec2_add_self, add_zero]

/-- Proposition 9, deterministic part (HCTR++): if `F r` is injective for every `r`, then
a collision `KS (F re pp1) = KS (F (re + β) (pp1 + α))` with `(α, β) ≠ 0` comes either
from a collision of the middle value `cc` with `β ≠ 0`, or from a collision
`KS c = KS c'` with `c ≠ c'`. -/
theorem collision_cases (hF : ∀ r, Function.Injective (k.F r)) (re pp1 α β : K)
    (hab : (α, β) ≠ 0) (h : k.KS (k.F re pp1) = k.KS (k.F (re + β) (pp1 + α))) :
    (k.F re pp1 = k.F (re + β) (pp1 + α) ∧ β ≠ 0) ∨
      ∃ c c', c ≠ c' ∧ k.KS c = k.KS c' := by
  by_cases hc : k.F re pp1 = k.F (re + β) (pp1 + α)
  · left
    refine ⟨hc, fun hβ => hab ?_⟩
    subst hβ
    rw [add_zero] at hc
    have hα : pp1 = pp1 + α := hF re hc
    have : α = 0 := by char2_lc hα
    simp [this]
  · exact Or.inr ⟨_, _, hc, h⟩

end HCTRppKey

end SimonHCTR
