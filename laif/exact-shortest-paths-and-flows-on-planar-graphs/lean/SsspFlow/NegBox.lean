import SsspFlow.NegWalk

/-!
# The low-diameter decomposition

`LDDBox`: the low-diameter decomposition of [6, Lemma 4, Cor. 27] with the order of its clusters of
[6, Lemma 5, Prop. 32, Cor. 33], in the form of Lemma 2 of `notes/NEGATIVE.md`, with the repairs of
Section 8 there. The steps of minor aggregation take `Õ(D)` rounds by [9, Cor. 4.6, Lemma 4.8].
Each node gets an index. Nodes with equal index are close in both directions, and an arc from a
larger index to a smaller one, a cut arc, is rare when it is short.
-/

set_option autoImplicit false

open scoped ENNReal
open Cslib.Congest

namespace SsspFlow.Congest

/-- The input of a node for the decomposition: its neighbours in rotation order, the lengths of its
arcs, with `⊤` for a removed arc, and the bound `d` on the diameter of the clusters. -/
structure LddIn (V : Type) where
  /-- The neighbours in rotation order. -/
  nbrs : List V
  /-- The length of the arc to a neighbour; `⊤` for other nodes. -/
  lenOut : V → ℕ∞
  /-- The length of the arc from a neighbour; `⊤` for other nodes. -/
  lenIn : V → ℕ∞
  /-- The bound on the diameter of the clusters. -/
  d : ℕ

/-- The input of the nodes of a network with lengths `ℓ` and bound `d`. -/
def Net.lddIn {V : Type} [Fintype V] [DecidableEq V] (N : Net V) (ℓ : V → V → ℕ∞) (d : ℕ) (v : V) :
    LddIn V where
  nbrs := N.rotList v
  lenOut u := if N.G.Adj v u then ℓ v u else ⊤
  lenIn u := if N.G.Adj v u then ℓ u v else ⊤
  d := d

/-- **The decomposition** [6, Lemma 4, Lemma 5], with the repairs of Section 8 of
`notes/NEGATIVE.md`. For lengths in `{0, …, (n + 2) ^ K, ∞}` and `1 ≤ d ≤ (n + 2) ^ K`, with an exact
oracle in `T` rounds, an algorithm with private strings gives every node an index below `(n + 2) ^ C`
in `C logᶜ⁰ n (T + Õ(D))` rounds. On all but a fraction `1 / (n + 1) ^ k` of the strings, two nodes
with equal index have distance at most `d` in both directions, in the whole network. An arc of
finite length `ℓ(a, b)` is cut with probability at most `C log² n ℓ(a, b) / d + 1 / (n + 1) ^ k`. The
exponent `c₀` does not depend on `K` and `k`. -/
def LDDBox : Prop :=
  ∃ c₀ : ℕ, ∀ K k : ℕ, ∃ C c : ℕ, ∀ n D T B : ℕ, 1 ≤ D →
    ∀ (σ : Type) (A : Algorithm (Fin n) (OracleIn (Fin n)) σ B) (out : Fin n → σ → ℕ∞),
    ExactOracleOK n ((n + 2) ^ C) D T A out →
    ∃ (ρ : Type) (_ : Fintype ρ) (_ : Nonempty ρ) (σ' : Type)
      (Q : Algorithm (Fin n) (LddIn (Fin n) × ρ) σ' (B + C * logN n ^ c))
      (idx : Fin n → σ' → ℕ),
      ∀ (N : Net (Fin n)) (ℓ : Fin n → Fin n → ℕ∞) (d : ℕ),
        N.toRot.Planar → N.DiamLE D →
        (∀ a b, N.G.Adj a b → ℓ a b = ⊤ ∨ ℓ a b ≤ ((n + 2) ^ K : ℕ)) → 1 ≤ d → d ≤ (n + 2) ^ K →
        let ix := fun (r : Fin n → ρ) (v : Fin n) => idx v (Q.run N.G (fun u => (N.lddIn ℓ d u, r u))
          (C * logN n ^ c₀ * (T + C * logN n ^ c * D)) v)
        (strCount (fun r : Fin n → ρ => ¬ ∀ u v, ix r u = ix r v →
            dist N.G.Adj (lenTop ℓ) Set.univ u v ≤ d ∧ dist N.G.Adj (lenTop ℓ) Set.univ v u ≤ d) *
          (n + 1) ^ k ≤ Fintype.card (Fin n → ρ)) ∧
        (∀ a b, N.G.Adj a b → ℓ a b ≠ ⊤ →
          strCount (fun r : Fin n → ρ => ix r b < ix r a) * (d * (n + 1) ^ k) ≤
            (C * logN n ^ 2 * (ℓ a b).toNat * (n + 1) ^ k + d) * Fintype.card (Fin n → ρ)) ∧
        ∀ r v, ix r v < (n + 2) ^ C

end SsspFlow.Congest
