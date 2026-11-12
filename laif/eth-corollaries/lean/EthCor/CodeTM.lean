import EthCor.CodeFormula
import EthCor.ConnIsoTM

/-! # The distance of a quantum CSS code in time C·2^{δn}, deterministic

The input is s in unary, then the code `SatFree.enc (codeCNF H₁ H₂)` of the checks (those of H₁ as
positive clauses, those of H₂ as negative ones). The machine counts twice with Anthropic's `SIZED`:
K = the satisfying assignments of `cssF … false` with 2n + 1 true variables, N = those of
`cssF … true` with s + 2n + 1 true variables, and writes 2N/K in binary. By `Code.numLog_eq` this is
the number of logical operators of weight s (`css_counts`). Run for s = 1, 2, … the first nonzero
output is the distance; the formulas have 5n + 2 variables for every number of checks. -/

namespace EthCor.CodeTM

open Groundwork Groundwork.Prog Groundwork.Stepped CountKSat GraphProblems Turing Finset EthCor.ConnI
  EthCor.ConnITM EthCor.Code

/-! ### The front end and the last step -/

/-- s: the unary number in front. -/
def sQ (x : List Bool) : ℕ := ones x

/-- n in unary and the clauses of the code. -/
def rQ (x : List Bool) : List Unit × Fml := FreeCode.readFree (rest x)

def nQ (x : List Bool) : ℕ := (rQ x).1.length

/-- The formula with e, its 5n + 2 variables and the target: 2n + 1 for e = false, s + 2n + 1 for
e = true. -/
def preQ (w : ℕ) (e : Bool) (x : List Bool) : List Unit × ℕ × Fml :=
  (List.replicate (nQ x + nQ x + (nQ x + 1) + (nQ x + (nQ x + 1))) (), cond e (sQ x) 0 + (nQ x + (nQ x + 1)),
    cssF w (nQ x) (rQ x).2 e)

/-- 2N/K in binary. -/
def postQ (p : (List Bool × ℕ) × ℕ) : List Bool := Nat.bits (2 * p.2 / p.1.2)

section Poly

variable {α : Type} [Enc α]

theorem rowsF_polyT (w : ℕ) {n : α → ℕ} {ψ : α → Fml} (hn : PolyT n) (hψ : PolyT ψ) :
    PolyT fun a => rowsF w (n a) (ψ a) := by
  unfold rowsF rowF pos; fun_prop

theorem chainF_polyT {n : α → ℕ} (hn : Unary n) (e : Bool) : PolyT fun a => chainF (n a) e := by
  have hr : PolyT fun a => List.range (n a) := PolyT.range hn
  have hn' := hn.poly
  unfold chainF xorC; fun_prop

theorem cssF_polyT (w : ℕ) {n : α → ℕ} {ψ : α → Fml} (hn : Unary n) (hψ : PolyT ψ) (e : Bool) :
    PolyT fun a => cssF w (n a) (ψ a) e := by
  unfold cssF
  exact PolyT.append (PolyT.append (rowsF_polyT w hn.poly hψ) (chainF_polyT hn e))
    (compF_polyT hn.poly (hn.add (hn.add (Unary.const 1))))

end Poly

theorem preQ_polyT (w : ℕ) (e : Bool) : PolyT (preQ w e) := by
  have hrs : PolyT fun x => rest x := by unfold rest; fun_prop
  have hr : PolyT rQ := FreeCode.readFree_polyT.comp hrs
  have hn : Unary nQ := Unary.of_length hr.fst
  have hs : PolyT sQ := by unfold sQ ones; fun_prop
  have h1 : PolyT fun x => List.replicate (nQ x + nQ x + (nQ x + 1) + (nQ x + (nQ x + 1))) () :=
    ((hn.add hn).add (hn.add (Unary.const 1))).add (hn.add (hn.add (Unary.const 1)))
  have h3 : PolyT fun x => nQ x + (nQ x + 1) := PolyT.add hn.poly (PolyT.add hn.poly (PolyT.const 1))
  have h2 : PolyT fun x => cond e (sQ x) 0 + (nQ x + (nQ x + 1)) := by
    cases e
    · exact PolyT.add (PolyT.const 0) h3
    · exact PolyT.add hs h3
  exact PolyT.prodMk h1 (PolyT.prodMk h2 (cssF_polyT w hn hr.snd e))

theorem postQ_polyT : PolyT postQ := by
  have := bits_polyT
  unfold postQ; fun_prop

/-- Count K, count N, write 2N/K. -/
def codeM (w ℓ τ : ℕ) : Stepped (List Bool) (List Bool) :=
  Stepped.bind (Stepped.mapIn (preQ w false) (FromPrinted.Consequences.SIZED (w + 4) ℓ τ))
    (Stepped.bind (Stepped.mapIn (fun p : List Bool × ℕ => preQ w true p.1)
      (FromPrinted.Consequences.SIZED (w + 4) ℓ τ)) (Stepped.ofFun postQ))

@[instance_reducible] def isPolyT_codeM (w ℓ τ : ℕ) [IsPolyT (FromPrinted.Consequences.SIZED (w + 4) ℓ τ)] :
    IsPolyT (codeM w ℓ τ) :=
  haveI := IsPolyT.mapIn (M := FromPrinted.Consequences.SIZED (w + 4) ℓ τ) (preQ_polyT w false)
  haveI := IsPolyT.mapIn (M := FromPrinted.Consequences.SIZED (w + 4) ℓ τ)
    ((preQ_polyT w true).comp (PolyT.fst PolyT.id' : PolyT fun p : List Bool × ℕ => p.1))
  haveI := IsPolyT.ofFun postQ_polyT
  haveI := IsPolyT.bind (M := Stepped.mapIn (fun p : List Bool × ℕ => preQ w true p.1)
    (FromPrinted.Consequences.SIZED (w + 4) ℓ τ)) (N := Stepped.ofFun postQ)
  IsPolyT.bind (M := Stepped.mapIn (preQ w false) (FromPrinted.Consequences.SIZED (w + 4) ℓ τ))
    (N := Stepped.bind (Stepped.mapIn (fun p : List Bool × ℕ => preQ w true p.1)
      (FromPrinted.Consequences.SIZED (w + 4) ℓ τ)) (Stepped.ofFun postQ))

theorem read_css {n : ℕ} (w : ℕ) (H₁ H₂ : List (List (Fin n))) (s : ℕ) (e : Bool) :
    preQ w e (unary s ++ SatFree.enc (codeCNF H₁ H₂)) = (List.replicate (n + n + (n + 1) + (n + (n + 1))) (),
      cond e s 0 + (n + (n + 1)), cssF w n (Decode.toN (codeCNF H₁ H₂)) e) := by
  rw [preQ, nQ, sQ, rQ, Read.ones_unary_append, Read.rest_unary_append, FreeCode.reads_readFree n (codeCNF H₁ H₂),
    List.length_replicate]

/-! ### Sizes -/

/-- The input has length below (2D(w+1) + 3)·(n+2)². -/
theorem length_input {w D n s : ℕ} {H₁ H₂ : List (List (Fin n))} (hs : s ≤ n) (hm : H₁.length + H₂.length ≤ D * n)
    (hw : ∀ r ∈ H₁ ++ H₂, r.length ≤ w) :
    (unary s ++ SatFree.enc (codeCNF H₁ H₂)).length + 1 ≤ (2 * D * (w + 1) + 3) * (n + 2) ^ 2 := by
  obtain ⟨X, hX⟩ : ∃ X, X = n + 2 := ⟨_, rfl⟩
  have hW : Nat.log2 (2 * n) + 2 ≤ 2 * X := by have := Nat.log2_le_self (2 * n); omega
  have hC : ∀ C ∈ codeCNF H₁ H₂, (SatFree.encClause C).length ≤ 2 * (w + 1) * X := by
    intro C hC
    have hlen : C.length ≤ w := by
      rw [codeCNF, List.mem_append, List.mem_map, List.mem_map] at hC
      rcases hC with ⟨r, hr, rfl⟩ | ⟨r, hr, rfl⟩
      · rw [List.length_map]; exact hw r (List.mem_append_left _ hr)
      · rw [List.length_map]; exact hw r (List.mem_append_right _ hr)
    have e : (SatFree.encClause C).length = 2 + C.length * (Nat.log2 (2 * n) + 2) := by
      simp [SatFree.encClause, SatFree.encLit, List.length_flatMap]; ring
    rw [e]
    calc 2 + C.length * (Nat.log2 (2 * n) + 2) ≤ 2 + w * (2 * X) := by gcongr
      _ ≤ 2 * (w + 1) * X := by rw [hX]; nlinarith
  have hlen : (codeCNF H₁ H₂).length ≤ D * n := by
    rw [codeCNF, List.length_append, List.length_map, List.length_map]; exact hm
  have hsum : ((codeCNF H₁ H₂).flatMap SatFree.encClause).length ≤ D * X * (2 * (w + 1) * X) := by
    rw [List.length_flatMap]
    calc ((codeCNF H₁ H₂).map fun C => (SatFree.encClause C).length).sum
          ≤ (codeCNF H₁ H₂).length * (2 * (w + 1) * X) := by
          have := List.sum_le_card_nsmul ((codeCNF H₁ H₂).map fun C => (SatFree.encClause C).length)
            (2 * (w + 1) * X) (by
              intro y hy
              obtain ⟨C, hC', rfl⟩ := List.mem_map.1 hy
              exact hC C hC')
          simpa using this
      _ ≤ D * X * (2 * (w + 1) * X) := Nat.mul_le_mul_right _ (hlen.trans (Nat.mul_le_mul_left _ (by omega)))
  have e : (unary s ++ SatFree.enc (codeCNF H₁ H₂)).length =
      s + 1 + (n + 1 + (((codeCNF H₁ H₂).flatMap SatFree.encClause).length + 1)) := by
    simp [unary, SatFree.enc]; ring
  rw [e, ← hX]
  have e2 : D * X * (2 * (w + 1) * X) = 2 * D * (w + 1) * X ^ 2 := by ring
  have e3 : (2 * D * (w + 1) + 3) * X ^ 2 = 2 * D * (w + 1) * X ^ 2 + 3 * X ^ 2 := by ring
  have h3 : 2 * X + 2 ≤ 3 * X ^ 2 := by nlinarith
  omega

theorem size_cnt (N s : ℕ) (ψ : Fml) : size (cntS N s ψ) ≤ N + 2 := by
  have hle : cntS N s ψ < 2 ^ (N + 1) := by
    unfold cntS
    refine lt_of_le_of_lt (card_le_univ _) ?_
    rw [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, pow_succ]
    have := Nat.one_le_two_pow (n := N)
    omega
  exact SplitCount.size_nat_le hle

open Classical in
theorem numLog_le {n : ℕ} (H₁ H₂ : List (List (Fin n))) (s : ℕ) : numLog H₁ H₂ s < 2 ^ (n + 1) := by
  have h1 : numLog H₁ H₂ s ≤ 2 ^ n := (card_le_univ _).trans (by simp)
  have h2 : 2 ^ n < 2 ^ (n + 1) := Nat.pow_lt_pow_right (by omega) (by omega)
  omega

/-! ### The theorem -/

/-- **The number of logical operators of weight s of a quantum CSS code, in time C·2^{δn},
deterministic.** For every w, D and δ > 0, one Turing machine with finite alphabets: given s ≤ n in
unary and the checks H₁, H₂ of a code on n ≥ 1 qubits, at most D·n checks of weight at most w, it
outputs in binary the number of x ∈ ker H₁ of weight s outside the row space of H₂, within
⌊C·2^{δn}⌋ steps. With H₁ = H_X, H₂ = H_Z these are the Z-type logical operators, with H₁ = H_Z,
H₂ = H_X the X-type ones; the least s with a nonzero count is the distance. -/
theorem css_counts (w D : ℕ) {δ : ℝ} (hδ : 0 < δ) : ∃ (M : TM2ComputableAux Bool Bool) (C : ℕ),
    (∀ i, Finite (M.tm.Γ i)) ∧
    ∀ (n s : ℕ) (H₁ H₂ : List (List (Fin n))), 1 ≤ n → s ≤ n → H₁.length + H₂.length ≤ D * n →
      (∀ r ∈ H₁ ++ H₂, r.length ≤ w) →
      Wrap.Outputs M (unary s ++ SatFree.enc (codeCNF H₁ H₂)) (Nat.bits (numLog H₁ H₂ s))
        ⌊(C : ℝ) * (2 : ℝ) ^ (δ * n)⌋₊ := by
  obtain ⟨ℓ₀, τ, ⟨hI⟩, c, hc⟩ := FromPrinted.Consequences.SIZED_counts (w + 4) (show 0 < δ / 14 by positivity)
  have := isPolyT_codeM w ℓ₀ τ
  obtain ⟨A, hA⟩ : ∃ A, A = D * 2 ^ (w + 1) + 17 := ⟨_, rfl⟩
  obtain ⟨K, hK⟩ : ∃ K, K = c * A ^ c + 8 * D * (w + 1) + 2 * c + 40 := ⟨_, rfl⟩
  let ι := Σ n : ℕ, {p : ℕ × List (List (Fin n)) × List (List (Fin n)) //
    1 ≤ n ∧ p.1 ≤ n ∧ p.2.1.length + p.2.2.length ≤ D * n ∧ ∀ r ∈ p.2.1 ++ p.2.2, r.length ≤ w}
  suffices hrun : ∀ x : ι, ∃ T : ℕ, (codeM w ℓ₀ τ).Runs (unary x.2.1.1 ++ SatFree.enc (codeCNF x.2.1.2.1 x.2.1.2.2))
      T (K * (x.1 + 2) ^ K) (Nat.bits (numLog x.2.1.2.1 x.2.1.2.2 x.2.1.1)) ∧
      (T : ℝ) ≤ (K : ℝ) * (2 : ℝ) ^ (δ / 2 * (x.1 : ℝ)) by
    obtain ⟨N, C', hfin, hN⟩ := tm_of_stepped (codeM w ℓ₀ τ) (ι := ι)
      (fun x => unary x.2.1.1 ++ SatFree.enc (codeCNF x.2.1.2.1 x.2.1.2.2))
      (fun x => Nat.bits (numLog x.2.1.2.1 x.2.1.2.2 x.2.1.1)) (fun x => x.1) hδ K (2 * D * (w + 1) + 3) 2
      (fun x => length_input x.2.2.2.1 x.2.2.2.2.1 x.2.2.2.2.2) hrun
    exact ⟨N, C', hfin, fun n s H₁ H₂ h1 h2 h3 h4 => hN ⟨n, (s, H₁, H₂), h1, h2, h3, h4⟩⟩
  rintro ⟨n, ⟨s, H₁, H₂⟩, hn, hs, hm, hw⟩
  dsimp only at hn hs hm hw ⊢
  obtain ⟨ψ, hψdef⟩ : ∃ ψ, ψ = Decode.toN (codeCNF H₁ H₂) := ⟨_, rfl⟩
  have hψ : ∀ C ∈ ψ, ∀ l ∈ C, l.1 < n := fun C hC => (Decode.mem_toN (hψdef ▸ hC)).2
  have hψl : ψ.length ≤ D * n := by
    rw [hψdef, toN_code, List.length_append, List.length_map, List.length_map]; exact hm
  obtain ⟨V, hV⟩ : ∃ V, V = n + n + (n + 1) + (n + (n + 1)) := ⟨_, rfl⟩
  obtain ⟨T₁, hT₁, hT₁le⟩ := hc V (n + (n + 1)) (cssF w n ψ false) (by omega) (hV ▸ shaped_cssF hψ false)
  obtain ⟨T₂, hT₂, hT₂le⟩ := hc V (s + (n + (n + 1))) (cssF w n ψ true) (by omega) (hV ▸ shaped_cssF hψ true)
  obtain ⟨x, hx⟩ : ∃ x, x = unary s ++ SatFree.enc (codeCNF H₁ H₂) := ⟨_, rfl⟩
  have hr1 := read_css w H₁ H₂ s false
  have hr2 := read_css w H₁ H₂ s true
  simp only [cond_false, cond_true, zero_add] at hr1 hr2
  rw [← hx, ← hψdef, ← hV] at hr1 hr2
  rw [← hr1] at hT₁
  obtain ⟨K₁, hK₁⟩ : ∃ K₁, K₁ = cntS V (n + (n + 1)) (cssF w n ψ false) := ⟨_, rfl⟩
  obtain ⟨K₂, hK₂⟩ : ∃ K₂, K₂ = cntS V (s + (n + (n + 1))) (cssF w n ψ true) := ⟨_, rfl⟩
  rw [← hK₁] at hT₁
  rw [← hK₂] at hT₂
  have r1 := Stepped.mapIn_runs (f := preQ w false) (a := x) hT₁
  have r2 := Stepped.mapIn_runs (f := fun p : List Bool × ℕ => preQ w true p.1) (a := (x, K₁))
    (by rw [hr2]; exact hT₂)
  have r3 := ofFun_runs postQ ((x, K₁), K₂)
  have hout := bind_runs r1 (bind_runs r2 r3)
  have hval : postQ ((x, K₁), K₂) = Nat.bits (numLog H₁ H₂ s) := by
    rw [postQ, hK₁, hK₂, hV, hψdef]
    exact congrArg Nat.bits (numLog_eq H₁ H₂ hw s)
  rw [hval] at hout
  rw [← hx]
  refine ⟨T₁ + 1 + (T₂ + 1 + 1), hout.mono le_rfl ?_, ?_⟩
  · -- the space
    obtain ⟨X, hX⟩ : ∃ X, X = n + 2 := ⟨_, rfl⟩
    have hX1 : 1 ≤ X := by omega
    have hP : ψ.length * 2 ^ (w + 1) ≤ D * n * 2 ^ (w + 1) := Nat.mul_le_mul_right _ hψl
    have hlen : ∀ e, V + (cssF w n ψ e).length + 2 ≤ A * X := fun e => by
      have := length_cssF w n ψ e
      have e1 : A * X = D * n * 2 ^ (w + 1) + 2 * (D * 2 ^ (w + 1)) + 17 * n + 34 := by rw [hA, hX]; ring
      omega
    have hS : ∀ e, c * (V + (cssF w n ψ e).length + 2) ^ c ≤ c * A ^ c * X ^ c := fun e => by
      calc c * (V + (cssF w n ψ e).length + 2) ^ c ≤ c * (A * X) ^ c := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (hlen e) _)
        _ = c * A ^ c * X ^ c := by rw [mul_pow, mul_assoc]
    have hin : size x ≤ 2 * ((2 * D * (w + 1) + 3) * X ^ 2) := by
      rw [size_bools, hx]
      have := length_input (w := w) hs hm hw
      rw [← hX] at this
      omega
    have hk1 : size K₁ ≤ V + 2 := hK₁ ▸ size_cnt _ _ _
    have hk2 : size K₂ ≤ V + 2 := hK₂ ▸ size_cnt _ _ _
    have hbits : size (Nat.bits (numLog H₁ H₂ s)) ≤ 2 * (n + 1) + 1 := by
      rw [size_bools, Nat.size_eq_bits_len]
      have := Nat.size_le.2 (numLog_le H₁ H₂ s)
      omega
    have hp1 : size (x, K₁) = size x + size K₁ := rfl
    have hp2 : size ((x, K₁), K₂) = size x + size K₁ + size K₂ := rfl
    rw [hp1, hp2]
    have q1 : X ^ 2 ≤ X ^ (c + 2) := Nat.pow_le_pow_right hX1 (by omega)
    have q2 : X ^ c ≤ X ^ (c + 2) := Nat.pow_le_pow_right hX1 (by omega)
    have q3 : X ≤ X ^ 2 := Nat.le_self_pow (by norm_num) X
    have q4 : (c * A ^ c + 8 * D * (w + 1) + 40) * X ^ (c + 2) ≤ K * X ^ K :=
      Nat.mul_le_mul (by omega) (Nat.pow_le_pow_right hX1 (by omega))
    have e1 : (c * A ^ c + 8 * D * (w + 1) + 40) * X ^ (c + 2) =
        c * A ^ c * X ^ (c + 2) + 8 * D * (w + 1) * X ^ (c + 2) + 40 * X ^ (c + 2) := by ring
    have e2 : 2 * ((2 * D * (w + 1) + 3) * X ^ 2) = 4 * D * (w + 1) * X ^ 2 + 6 * X ^ 2 := by ring
    have q5 : c * A ^ c * X ^ c ≤ c * A ^ c * X ^ (c + 2) := Nat.mul_le_mul_left _ q2
    have q6 : 4 * D * (w + 1) * X ^ 2 ≤ 8 * D * (w + 1) * X ^ (c + 2) := by
      have : 4 * D * (w + 1) ≤ 8 * D * (w + 1) := Nat.mul_le_mul_right _ (by omega)
      exact Nat.mul_le_mul this q1
    have hS1 := hS false
    have hS2 := hS true
    rw [← hX]
    omega
  · -- the time
    have hN : ((V : ℕ) : ℝ) ≤ 7 * n := by
      have : V ≤ 7 * n := by omega
      exact_mod_cast this
    have e : δ / 14 * (V : ℝ) ≤ δ / 2 * n := by
      calc δ / 14 * (V : ℝ) ≤ δ / 14 * (7 * n) := mul_le_mul_of_nonneg_left hN (by positivity)
        _ = δ / 2 * n := by ring
    have hE : (c : ℝ) * (2 : ℝ) ^ (δ / 14 * (V : ℝ)) ≤ c * (2 : ℝ) ^ (δ / 2 * n) :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le one_le_two e) (Nat.cast_nonneg _)
    have h1 : (1 : ℝ) ≤ (2 : ℝ) ^ (δ / 2 * n) := Real.one_le_rpow one_le_two (by positivity)
    have hK' : (2 * c + 3 : ℝ) ≤ K := by
      have : 2 * c + 3 ≤ K := by omega
      exact_mod_cast this
    push_cast
    calc (T₁ : ℝ) + 1 + (T₂ + 1 + 1) ≤ c * (2 : ℝ) ^ (δ / 2 * n) + c * (2 : ℝ) ^ (δ / 2 * n) +
          3 * (2 : ℝ) ^ (δ / 2 * n) := by linarith
      _ = (2 * c + 3) * (2 : ℝ) ^ (δ / 2 * n) := by ring
      _ ≤ K * (2 : ℝ) ^ (δ / 2 * n) := mul_le_mul_of_nonneg_right hK' (by positivity)

end EthCor.CodeTM
