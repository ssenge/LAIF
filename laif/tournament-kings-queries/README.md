# Is every vertex of a tournament a king? Quantum queries

Written 21 Nov 2026.

**Setting.** A tournament T on N vertices orients every pair of vertices, and a query returns the orientation of one pair. A vertex x is a *king* if every other vertex can be reached from x by a directed path of length at most two. ALL-KINGS_N asks whether every vertex of T is a king, that is, whether T has diameter at most two, or whether its uncovered set is the whole vertex set. OV_n is Orthogonal Vectors as defined in [1]: given n vectors in {0, 1}ⁿ, with a query returning one entry, decide whether two vectors at distinct positions have disjoint supports.

| | Problem | Previous best bound | This folder | Status |
|---|---|---|---|---|
| Thm 1 | ALL-KINGS_N | O(N^{3/2}), by a search over pairs with an inner search | Q(OV_⌈N/3⌉) ≤ Q(ALL-KINGS_N) ≤ Q(OV_{2N+2}) up to O(1) terms, hence Ω(N^{5/4}) and Õ(N^{17/12}), implied by [1] | Lean for Lemmas 1 and 2 and both encodings; checked by script |

So deciding whether every vertex is a king has the same quantum query complexity as Orthogonal Vectors, Boolean matrix product verification and diameter at most two of undirected graphs, up to constant factors in the instance size [1]. An improvement for any of these problems transfers to the others.

The decision problem differs from computing the uncovered set itself, the set of all kings, which takes Ω(N^{3/2}) and at most O(N²) quantum queries [2]. The two sets of bounds do not contradict each other: the output of the decision problem is one bit, while the uncovered set has N output bits.

## Kings and covering

For a vertex x, write N⁺(x) for the set of vertices that x beats.

**Lemma 1.** In a tournament, x is not a king exactly when some y ≠ x satisfies N⁺(x) ⊆ N⁺(y).

*Proof.* Suppose x reaches no y ≠ x within two steps. Then y beats x. Every z ∈ N⁺(x) differs from y and does not beat y, so y beats z. Hence N⁺(x) ⊆ N⁺(y). Conversely, suppose N⁺(x) ⊆ N⁺(y) with y ≠ x. If x beat y, then y would lie in N⁺(y), which is impossible, so y beats x. Every out-neighbour z of x is beaten by y, so no path x → z → y exists, and x does not reach y within two steps. ∎

## Theorem 1, upper reduction

Let a_x ∈ {0, 1}^V be the indicator vector of N⁺(x), and b_y the indicator vector of V ∖ N⁺(y). Then a_x and b_y are orthogonal exactly when N⁺(x) ⊆ N⁺(y). Pairs with x = y have to be excluded, and so do pairs inside one list. This is done with 2N + 2 vectors in dimension 2N + 2:

- U_x = (a_x, e_x, 1, 0) for every vertex x,
- W_y = (b_y, e_y, 0, 1) for every vertex y,
- two all-ones vectors.

Here e_x is the unit vector of x in a second copy of the coordinates. Two vectors U_x, U_x′ share the first extra coordinate, and two vectors W_y, W_y′ share the second. U_x and W_x share coordinate x of the second copy, and an all-ones vector meets every vector, since none is zero. For x ≠ y, U_x and W_y are orthogonal exactly when a_x and b_y are. By Lemma 1, T fails ALL-KINGS exactly when this instance of OV_{2N+2} has an orthogonal pair. Each entry is either fixed or answered by one query to T: the entry z of a_x is the orientation of xz, and the entry z of b_y is the negated orientation of yz (with a_x(x) = 0 and b_y(y) = 1).

## Theorem 1, lower reduction

Let X ∈ {0, 1}^{m×m} with m odd and m ≥ 3. An even m reduces to m + 1 by appending a zero column and an all-ones row, which leaves the answer unchanged for m ≥ 2. The tournament T_X has 3m + 4 vertices: three classes R = {r_i}, R′ = {r′_j} and W = {w_t}, each of size m, and four further vertices α, β, γ, δ.

- Inside each class, the rotational tournament: the vertex of index i beats the vertices of index i + 1, …, i + (m − 1)/2 modulo m. It has diameter two.
- R′ beats R.
- r_i beats w_t when X_it = 1, and otherwise w_t beats r_i.
- w_t beats r′_j when X_jt = 1, and otherwise r′_j beats w_t.
- α: R and R′ beat α, and α beats W. β: W beats β, and β beats R and R′. γ: R, R′ and W beat γ. δ: δ beats R, R′ and W.
- Among the four: α → β, γ → α, γ → β, α → δ, β → δ, γ → δ.

Each orientation is either fixed or equal to one entry of X.

**Lemma 2.** T_X is ALL-KINGS exactly when supp(X_i) ∩ supp(X_j) ≠ ∅ for all i, j, including i = j.

*Proof.* Consider r_i and r′_j. A path r_i → z → r′_j cannot pass through R or R′, since R′ beats R. It cannot pass through α or γ, since both lose to every vertex of R′. It cannot pass through β or δ, since both beat r_i. A vertex w_t of W lies on such a path exactly when X_it = X_jt = 1. So r_i reaches r′_j within two steps exactly when rows i and j of X meet. Every other arc v → u has a witness z with u → z → v that does not depend on X:

| v → u | witness z |
|---|---|
| inside one class | inside the class (rotational tournament) |
| w_t → r_i, or w_t → r′_j | α |
| r_i → w_t, or r′_j → w_t | β |
| r_i → α, r′_j → α | β |
| α → w_t | γ |
| β → r_i, β → r′_j | α |
| w_t → β | δ |
| α → β | any r_i |
| r_i → γ, r′_j → γ | β |
| w_t → γ | α |
| γ → α | any w_t |
| γ → β | any r_i |
| δ → r_i, δ → r′_j | α |
| δ → w_t | β |
| α → δ | any r_i |
| β → δ | any w_t |
| γ → δ | any w_t |

∎

Since m ≥ 2, a zero row of X is orthogonal to every other row. So T_X is ALL-KINGS exactly when X has no orthogonal pair. Hence Q(OV_m) ≤ Q(ALL-KINGS_{3m+4}) for odd m. Together with the upper reduction and the bounds Q(OV_n) = Ω(n^{5/4}) and Q(OV_n) = Õ(n^{17/12}) of [1], this gives Theorem 1.

## Scripts

`sim/check_reductions.py` checks Lemma 1 and the upper reduction on every tournament with at most 5 vertices and on 300 random tournaments with 6 to 14 vertices. It checks Lemma 2 on all 3 × 3 matrices and on 800 random 5 × 5 and 7 × 7 matrices.

## Lean

The library `Kings` in `lean/` (Lean 4, Mathlib at the revision pinned in `lean/lakefile.toml`) proves, with only the standard axioms (`lean/axioms.txt`):

- `Kings.not_king_iff` (Lemma 1): in a tournament, x is not a king exactly when some y ≠ x beats every vertex that x beats;
- `Kings.hasOV_vec_iff` (upper reduction): the list of vectors U_x, W_y and two all-ones vectors, with positions and coordinates V ⊕ V ⊕ Bool, has an orthogonal pair at distinct positions exactly when some vertex is not a king;
- `Kings.rot_asymm`, `Kings.rot_total`, `Kings.rot_two`: the rotational tournament on 2h + 1 vertices is a tournament of diameter two for h ≥ 1;
- `Kings.isTournament_arc`: T_X is a tournament;
- `Kings.allKings_arc_iff` (Lemma 2): every vertex of T_X is a king exactly when every two rows of X, equal or not, share a one;
- `Kings.allKings_arc_iff_not_hasOV` (lower reduction): for m = 2h + 1 ≥ 3, every vertex of T_X is a king exactly when X has no orthogonal pair of distinct rows.

**Not formalized:** the transfer of query costs (each entry or orientation is fixed or one query), the padding of an even m, and the bounds of [1] on Orthogonal Vectors.

## Use of AI

Claude Opus 5.5 (Anthropic) was used throughout this research: to explore approaches, to develop and check proofs, to write the Lean files and the check scripts, and to draft the text.

## References

1. Improved quantum query bounds for Boolean matrix product verification. arXiv:2609.40180, 2026.
2. Quantum query complexity of tournament solutions. arXiv:2610.39702, 2026.
