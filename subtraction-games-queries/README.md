# Quantum query lower bound for subtraction games

Written 12 Nov 2026.

**Setting.** A subtraction game with n stones is given by a triangular binary matrix Γ: with j stones left, a player may take j − i stones, leaving i, iff Γ_{j,i} = 1 (0 ≤ i < j ≤ n). Players alternate, and a player who cannot move loses. Position j *wins* if some move reaches a losing position, so position 0 loses and Win(Γ, j) = 1 iff Γ_{j,i} = 1 and Win(Γ, i) = 0 for some i < j. The task is to compute Win(Γ) = Win(Γ, n), and a query returns one entry of Γ. The same recursion solves every game on a directed acyclic graph given by its adjacency matrix in a topological order.

| | Problem | Previous best bound | This folder | Status |
|---|---|---|---|---|
| Thm 1 | Win(Γ) for subtraction games with n stones | O(n^{3/2} log n) quantum queries [1, 3]; classically Θ(n²) [1] | Ω(n^{3/2}) quantum queries, so Θ̃(n^{3/2}) | Lean (the embedding and the adversary counts); assuming the adversary bound [2] |
| Cor 2 | Is the last vertex in the lexicographically first maximal independent set? Adjacency matrix of a graph on n + 1 vertices | | Θ̃(n^{3/2}) quantum queries | Lean (as Thm 1, and the identity with the losing positions) |

The upper bound of [1] computes the positions in increasing order, each with a search for a losing position among its moves. Theorem 1 shows that this is optimal up to the factor log n.

## 1. A parity of ORs inside a game

A position whose moves all lead to winning positions loses, so the value of a position is the NAND of the values of the positions it can move to, with the NAND of nothing equal to 0. Fixed moves therefore build any circuit of NAND gates, and a position with free moves into a pool of losing positions computes an OR.

**Lemma 1.** Let k, s ≥ 1 and n = s + 5k. For every x ∈ {0,1}^{k×s} there is a game Γ_x with n stones, in which each entry is 0, 1 or an entry of x, such that Win(Γ_x) = 1 iff an odd number of the rows x_0, …, x_{k−1} contain a 1.

*Proof.* The positions 0, …, s − 1 form the pool and have no moves, so they lose, and so does u₀ = s. Stage t, for t = 0, …, k − 1, uses the positions b_t, N_t, A_t, B_t, u_{t+1} at s + 5t + 1, …, s + 5t + 5. Position b_t can move to the pool position i iff x_{t,i} = 1, so Win(b_t) = OR_i x_{t,i}. The other four positions have the fixed moves

- N_t to u_t and b_t,
- A_t to u_t and N_t,
- B_t to b_t and N_t,
- u_{t+1} to A_t and B_t,

so with w = Win(u_t), g = Win(b_t) and h = NAND(w, g), Win(u_{t+1}) = NAND(NAND(w, h), NAND(g, h)) = w ⊕ g. By induction, Win(u_t) is the parity of the number of nonempty rows among the first t, and u_k is position n. Every move goes from a higher to a lower position. ∎

## 2. The lower bound

**Theorem 1.** Every quantum algorithm that computes Win(Γ) for all subtraction games with n stones, with error at most 1/3, makes Ω(n^{3/2}) queries.

*Proof.* Let k = ⌊n/10⌋ and s = n − 5k ≥ n/2, and restrict to the inputs x of Lemma 1 in which every row has at most one 1. Let a = ⌊k/2⌋, let X be the inputs with exactly a nonempty rows and Y those with a + 1, and relate x ∈ X to y ∈ Y if y arises from x by setting one entry of an empty row to 1. By Lemma 1, Win(Γ_x) differs on X and Y. Each x ∈ X has (k − a)s ≥ ks/2 related inputs, each y ∈ Y has a + 1 ≥ k/2, and for each x and each entry there is at most one related y that differs from x there, and in the same way for each y. The adversary bound [2] gives Ω(√((ks/2)(k/2))) = Ω(k√s) queries to x. A query to Γ_x reads at most one entry of x, and the other entries are constants, so it is simulated by one controlled query to x. For n ≥ 20, k ≥ n/20 and s ≥ n/2, so this is Ω(n^{3/2}); smaller n only change the constant. ∎

**Corollary 2.** Let G be a graph on the vertices 0, …, n, given by its adjacency matrix, and let L be its lexicographically first maximal independent set: vertex j belongs to L iff no neighbour i < j does. Deciding whether n ∈ L takes Θ̃(n^{3/2}) quantum queries.

*Proof.* For the game with Γ_{j,i} = 1 iff {i, j} is an edge, the losing positions are exactly L: position j loses iff no move leads to a losing position, that is, iff no neighbour i < j lies in L. So n ∈ L iff Win(Γ) = 0, and both bounds carry over. ∎

## Lean

The library `GameLB` in `lean/` (Lean 4, Mathlib at the revision pinned in `lean/lakefile.toml`) proves, with only the standard axioms (`lean/axioms.txt`):

- `win_iff`, `win_two`: the recursion for the value of a position, and that a position with exactly two moves is the NAND of their values.
- `emb_lt`, `win_top`: Lemma 1. Every move of the game of Lemma 1 goes down, and its position s + 5t wins iff an odd number of the first t rows contain a 1.
- `inL_eq`: the greedy set of Corollary 2 is the set of losing positions.
- `win_weight`, with `row_toMat` and `par_toMat`: on the inputs with at most one 1 per row, read as a matrix, the top position of the game of Lemma 1 wins iff the number of nonempty rows is odd, which is the function used in Theorem 1.
- `weight_add`, `card_adds`, `card_removes`, `bit_add`, `add_inj`, `add_remove`, `remove_inj`: the counts of the relation in the proof of Theorem 1. Adding a 1 to an empty row raises the number of nonempty rows by one; an input with w nonempty rows has (k − w)s related inputs and arises from w inputs; and a related input differs exactly in the added entry (`bit_add`), and distinct related inputs add distinct entries (`add_inj`, and `add_remove`, `remove_inj` for the other side), so for each entry at most one related input differs there.

Not formalized: the adversary bound [2], which is used as stated, the simulation of a query to Γ_x by a query to x, the step from k and s to n in Theorem 1, and the upper bound of [1].

## Scripts

`sim/check_embedding.py` builds the game of Lemma 1 and computes its value by the recursion. It agrees with the parity of the ORs on all inputs with k, s ≤ 3 and on 3000 random inputs with k, s ≤ 30.

## Use of AI

Claude Opus 5.5 (Anthropic) was used throughout this research: to explore approaches, to develop and check proofs, to write the Lean files and the check script, and to draft the text.

## References

1. K. Khadiev, D. Kravchenko. On the complexity of solving subtraction games. arXiv:1808.03494, 2018.
2. A. Ambainis. Quantum lower bounds by quantum arguments. J. Comput. Syst. Sci. 64(4), 750–767, 2002. arXiv:quant-ph/0002066.
3. D. Kravchenko, K. Khadiev, D. Serov, R. Kapralov. Quantum-over-classical advantage in solving multiplayer games. arXiv:2006.06965, 2020.
