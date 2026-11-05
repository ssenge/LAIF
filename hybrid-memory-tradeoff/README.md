# Qubits against classical memory on the hypergraph translation task

Written 5 Nov 2026.

## Setting

Take the qubit variant of the (ℓ, n, k)-hypergraph stabilizer measurement translation task of [1, Appendix B.1], and write N = (n choose k). An input is processed in five phases:

1. Each of n qubits starts in |0⟩, and a token asks for phase estimation of exp(2iυ_i X_i). If υ_i is a multiple of π/2, this operator is ±I, so the outcome is fixed and the qubit stays in |0⟩. Otherwise the qubit is projected onto |+⟩ or |−⟩, with probability 1/2 each.
2. N tokens, one for each k-set v of vertices, apply exp(−iγ_v |1⟩⟨1|_v), and the output is 0.
3. n tokens ask for the outputs of phase 1 again.
4. n − k tokens measure Z_b on the qubits b of a set B.
5. The remaining tokens perform phase estimation of unitaries G_C(ϕ, θ) on the k qubits of C = [n] \ B.

Some conventions:

- Phase estimation is ideal, as in Sec. 3.1 of [1], and the output is its outcome. That outcome is an eigenphase, which [1] also writes as ±1. Everything below holds for either encoding.
- Ancillas for phase estimation are not counted, as in [1].
- We read Eq. (17) of [1] with the projector |1⟩⟨1|_v of Eq. (19). If |0⟩⟨0|_v is used instead, everything below holds after replacing the condition "z = 1 on u ∩ B" by "z = 0 on u ∩ B".

A k-HRNN on n qubits samples the output distribution exactly, provided its first n outputs are kept in extra memory [1, Appendix B.1]. Classical latent models need latent dimension at least N − 1 under the regularity assumptions of Theorem B.3 of [1]. The classical simulation of [1] stores O(N) numbers.

A *hybrid model* has latent state (λ, ρ): a vector λ ∈ R^c and a density matrix ρ on q qubits. At each token, it applies to ρ a quantum instrument chosen by λ and the token, and uses a random vector r fixed in advance. Its output and its new λ are functions of the instrument outcome, λ, the token and r. So, for fixed r, the law of the outputs after any prefix of the input depends only on (λ, ρ) and the later tokens.

## Results

**Theorem 1 (construction).** Let 0 ≤ t ≤ n, and let Q be a set of t vertices. A hybrid model with max(t, k) qubits and c = N − (t choose k) + 2n classical coordinates samples the output distribution of the task exactly, for every input. For k ≤ q ≤ n qubits, take t = q. Then

c = N − (q choose k) + 2n.

At t = n, this is the k-HRNN with its outputs stored in 2n classical coordinates.

**Theorem 2 (lower bound).** Let D_q° be the open set of full-rank density matrices on q qubits, of real dimension 4^q − 1.

- Fix r, and fix a record ω of instrument outcomes during the first N + n tokens.
- Let F_{r,ω} map an input to the latent point (λ, ρ) reached with that record.
- Take the latent manifold L = R^c × D_q°, or any C² contractible Finsler manifold L ⊆ R^c × H_q that contains the image. Here H_q is the space of trace-one Hermitian matrices.
- Suppose that, with this L, F_{r,ω} meets the regularity assumptions of Theorem B.3 of [1] on a contractible open set U ⊆ K: it is C², it is a strong submersion, and it meets the boundary condition.

If the model reaches a finite backward cross entropy on the task of that theorem, then dim U < dim L + 2. Hence

c ≥ N − 4^q.

**Corollary.** Let k ≥ 2, k ≤ q ≤ n and 0 < δ < 1.

- With q qubits, every model in the class of Theorem 2 has c ≥ N − 4^q. The model of Theorem 1 has c = N − (q choose k) + 2n.
- Counting one real coordinate per stored number, the model of Theorem 1 keeps (q choose k) fewer weights classically than the classical simulation. No model in the class of Theorem 2 saves more than 4^q coordinates against N.
- The two bounds concern different model classes. The model of Theorem 1 is not in the class of Theorem 2, since its quantum states are pure and some of its coordinates are discrete.
- To bring the classical memory down to (1 − δ)N, a model in the class of Theorem 2 needs q ≥ log₄(δN) qubits. For fixed k and δ, q = (δ^{1/k} + o(1)) n qubits suffice for the model of Theorem 1.
- k ≥ 2 is needed, since for k = 1 the 2n stored outputs and labels already exceed N.

## Proof of Theorem 1

Write |s_v⟩ ∈ {|0⟩, |+⟩, |−⟩} for the state of qubit v after phase 1, and a(x) = ∏_v ⟨x_v|s_v⟩ for x ∈ {0, 1}^n. After phase 2, the n-qubit state is

Σ_x a(x) e^{−iΦ(x)} |x⟩, with Φ(x) = Σ_u γ_u [x = 1 on all of u],

summed over the k-sets u.

All gates of phase 2 are diagonal. So the Z outcomes z on B have probability |a_B(z)|² = ∏_{b ∈ B} |⟨z_b|s_b⟩|², a product over the qubits. Given z, the state on C is, up to a global phase,

Σ_{y ∈ {0,1}^C} a_C(y) e^{−iΦ(z, y)} |y⟩, with Φ(z, y) = Σ_u γ_u [z = 1 on u ∩ B] [y = 1 on u ∩ C].

The hybrid keeps the qubits of Q in its register. It proceeds as follows.

- **Phase 1.** For v ∈ Q, it runs the measurement on the register. For v ∉ Q, it samples the output classically with the same law, using r. It stores the n outputs. For each vertex it keeps one coordinate with the label of |s_v⟩.
- **Phase 2.** It applies the gates with u ⊆ Q to the register, and stores γ_u for the other N − (t choose k) sets.
- **Phase 3.** After answering a repeat token, it overwrites the stored output with a marker value. Each repeat token is answered with the first unmarked output. Marker values for unset weights and unmeasured vertices also tell the phases apart.
- **Phase 4.** For b ∈ Q, it measures Z_b on the register. For b ∉ Q, it samples z_b from |⟨z_b|s_b⟩|². It overwrites the coordinate of b with the outcome, using two further values, so that b is marked as measured. Its outcomes therefore have the law |a_B(z)|².

After phase 4, the register holds the qubits of Q ∩ C in the state Σ_y a_{Q∩C}(y) e^{−iΦ_Q(z, y)} |y⟩, where Φ_Q is the part of Φ with u ⊆ Q. The qubits of Q ∩ B are in |z_b⟩ and are no longer needed. Before phase 5, the model does three things:

- It resets the measured register qubits and prepares |s_v⟩ on them for each v ∈ C \ Q. These are |Q ∩ B| = t − |Q ∩ C| qubits, and k − |Q ∩ C| of them are needed. If t < k, it also uses k − t further qubits.
- For each stored u with z = 1 on u ∩ B and u ∩ C nonempty, it applies exp(−iγ_u |1⟩⟨1|_{u ∩ C}) to the qubits of u ∩ C.
- It ignores the remaining part of Φ, from the sets with u ∩ C empty, which is a global phase.

The k qubits of C now hold the same state as in the n-qubit model, up to a global phase. Phase 5 acts on these k qubits alone, so the hybrid applies the same unitaries and measurements. This holds for any number of tokens in phase 5. So every output of every phase has the same joint law as in the n-qubit model.

The classical memory holds:

- N − (t choose k) weights;
- the n outputs of phase 1;
- one coordinate per vertex for its label or Z outcome.

That is c = N − (t choose k) + 2n. ∎

The script [sim/hybrid_check.py](sim/hybrid_check.py) compares the two models branch by branch for n ≤ 6 and k ∈ {2, 3}. It checks that the branch probabilities and the states on C, up to a global phase, agree to 1e-12. Equal states on C give equal laws for phase 5.

## Proof of Theorem 2

The proof of Theorem B.3 of [1] uses two facts about the model.

1. **The latent map.** The map to L meets the regularity assumptions on an open set U ⊆ K, where K is the N-dimensional set of inputs fixed in that theorem. From the global implicit function theorem, this gives fibers η(H × {λ}) of dimension dim U − dim L.
2. **Same latent, same later outputs.** For a classical model and fixed r, two inputs with the same latent point and the same later tokens give the same later outputs.

For a hybrid model, (1) is the hypothesis, applied to F_{r,ω}. Fact (2) becomes: for fixed r, two inputs that reach the same latent point (λ, ρ), followed by the same later tokens, give the same conditional law of the later outputs.

The proof then goes through, with this law in place of the deterministic output:

- **Phase 1 outputs.** At the trivial point h₀ of the fiber, the outputs of phase 3 must equal the trivial outcomes with probability 1. Their law depends only on the common latent point, so the same holds at the other two points h′ and h″ of the fiber. Hence the phase 1 outputs under ω must match there.
- **The completion.** The three inputs of one fiber have one common output law on their completions by the measurement sequence of Lemma B.1 of [1]. Finite backward cross entropy puts its support inside the intersection of the three true supports, which is empty.

The other steps use the structure of K, Lemma B.1, the repeat tokens and dim H ≥ 2. These are facts about the task, not about the model.

So a model with finite backward cross entropy has dim U < dim L + 2. As U is open in K, dim U = N, so dim L ≥ N − 1. Here dim L ≤ c + 4^q − 1, so c ≥ N − 4^q. ∎

## Proof of the corollary

The two bounds are Theorems 1 and 2. If c ≤ (1 − δ)N, then Theorem 2 gives 4^q ≥ δN.

For the other direction, (m choose k)/N = ∏_{j<k} (m − j)/(n − j) ≥ ((m − k)/n)^k for k ≤ m ≤ n. So (q choose k) ≥ δN + 2n holds once q − k ≥ (δ + 2n/N)^{1/k} n. For fixed k ≥ 2 and δ, 2n/N → 0, so this is (δ^{1/k} + o(1)) n.

## Scope

- **Qubits only.** For qumodes the state space has infinite dimension, so Theorem 2 gives nothing there.
- **Inherited form.** Theorem 2 inherits the regularity assumptions of Theorem B.3 of [1]. It also inherits the step from a fixed random vector r to the model over its randomness, which is taken over unchanged.
- **Pure states.** Suppose every instrument has one Kraus operator per outcome, as for unitaries and ideal projective measurements. Then the states stay pure, and such models are outside the class of Theorem 2, whose states have full rank. If the pure states stay in one affine chart of the projective space, and the map to R^c × (chart) meets the same assumptions, the same argument gives c ≥ N − 2^{q+1} + 1.
- **What a coordinate counts.** Without regularity, counting real coordinates is no measure of memory: one real number can hold any finite prefix. The count of Theorem 1 is one real number per stored quantity, as for the classical simulation of [1].
- **The gap.** The true saving per qubit register, somewhere between (q choose k) and 4^q, is not determined here. Theorem 1 keeps a block of vertices quantum. Whether some other use of the register keeps more is not known.
- **Related tradeoffs.**
  - Memory bounds for models with both classical and quantum memory are known for parity learning [3].
  - In communication complexity, protocols that send c classical bits and then q qubits obey tradeoffs of the form c + q² = Ω(·) [4].
  - For classical streaming models in general, [2] bounds the number of latent states by a contextuality measure.

## References

1. E. R. Anschuetz, X. Gao. Arbitrary Polynomial Separations in Trainable Quantum Machine Learning. Quantum (2026), arXiv:2402.08606, Theorem B.3, Lemma B.1 and Appendix B.1.
2. M. H. Teo, W. Yang, J. Sud, T. Tomesh, F. T. Chong, E. R. Anschuetz. k-Contextuality as a Heuristic for Memory Separations in Learning. arXiv:2507.11604.
3. Q. Liu, R. Raz, W. Zhan. Memory-Sample Lower Bounds for Learning with Classical-Quantum Hybrid Memory. STOC 2023, arXiv:2303.00209.
4. X. Wu, G. Yang, P. Yao. A Lifting Theorem for Hybrid Classical-Quantum Communication Complexity. arXiv:2511.17227.
