# Qubits against classical memory on the hypergraph translation task

Written 5 Nov 2026.

## Setting

Take the qubit variant of the (ℓ, n, k)-hypergraph stabilizer measurement translation task of [1, Appendix B.1], and write N = (n choose k). An input of the task is processed in five phases:

1. Each of n qubits starts in |0⟩, and a token asks for phase estimation of exp(2iυ_i X_i). The output is the measured eigenphase. If υ_i is a multiple of π/2, this operator is ±I, so the output is fixed and the qubit stays in |0⟩. Otherwise the qubit is projected onto |+⟩ or |−⟩, with probability 1/2 each.
2. N tokens, one for each k-set v of vertices, apply exp(−iγ_v |1⟩⟨1|_v), and the output is 0.
3. n tokens ask for the outputs of phase 1 again.
4. n − k tokens measure Z_b on the qubits b of a set B.
5. The remaining tokens perform phase estimation of unitaries G_C(ϕ, θ) on the k qubits of C = [n] \ B.

A k-HRNN on n qubits samples the output distribution exactly [1]. Classical latent models need latent dimension at least N − 1, under the assumptions of Theorem B.3 of [1]. The classical simulation of [1] uses O(N) memory.

A *hybrid model* has latent state (λ, ρ): a vector λ ∈ R^c and a density matrix ρ on q qubits. At each token it applies a quantum instrument to ρ, chosen by λ and the token. It also uses a random vector r fixed in advance. It outputs a function of the instrument's outcome, λ, the token and r, and updates λ the same way. So the outputs after any prefix of the input depend only on (λ, ρ), r and the later tokens. The models of [1] are the cases q = 0 and c = 0.

## Results

**Theorem 1 (construction).** Let 0 ≤ t ≤ n, and let Q be a set of t vertices. A hybrid model with t + min(k, n − t) qubits and c = N − (t choose k) + 2n classical latent coordinates samples the output distribution of the task exactly, for every input.

For q ≥ k qubits, take t = q − k. Then

c = N − (q − k choose k) + 2n.

At t = n, this is the k-HRNN with its outputs stored in 2n classical coordinates.

**Theorem 2 (lower bound).** Let H_q be the affine space of trace-one Hermitian 2^q × 2^q matrices, of real dimension 4^q − 1. Suppose a hybrid model's map from the first N + n tokens to (λ, ρ) ∈ R^c × H_q meets the assumptions of Theorem B.3 of [1], with latent manifold L = R^c × H_q. If the model reaches a finite backward cross entropy on the task of that theorem, then

c ≥ N − 4^q.

**Corollary.** Let k ≥ 2 and k ≤ q ≤ n. With q qubits:

- every hybrid model in the class of Theorem 2 has c ≥ N − 4^q;
- the model of Theorem 1 has c = N − (q − k choose k) + 2n.

So q qubits replace at least (q − k choose k) and at most 4^q classical latent coordinates. To bring the classical memory down to (1 − δ)N, a model in the class of Theorem 2 needs q ≥ log₄(δN) qubits. For fixed k and δ, q = (δ^{1/k} + o(1)) n qubits suffice for the model of Theorem 1.

## Proof of Theorem 1

Write |s_v⟩ ∈ {|0⟩, |+⟩, |−⟩} for the state of qubit v after phase 1, and a(x) = ∏_v ⟨x_v|s_v⟩ for x ∈ {0, 1}^n. After phase 2, the n-qubit state is

Σ_x a(x) e^{−iΦ(x)} |x⟩, with Φ(x) = Σ_u γ_u [x_u = 1 on all of u],

summed over the k-sets u. All gates of phase 2 are diagonal. So the Z outcomes z on B have probability |a_B(z)|² = ∏_{b ∈ B} |⟨z_b|s_b⟩|², a product over the qubits. Given z, the state on C is

Σ_{y ∈ {0,1}^C} a_C(y) e^{−iΦ(z, y)} |y⟩, with Φ(z, y) = Σ_u γ_u [z = 1 on u ∩ B] [y = 1 on u ∩ C],

up to a global phase.

The hybrid works as follows:

- It keeps the qubits of Q in its register.
- In phase 1, it runs the measurements for v ∈ Q on the register. For v ∉ Q, it samples the output classically, with the same law, using r.
- In phase 2, it applies the gates with u ⊆ Q to the register and stores γ_u for the other N − (t choose k) sets.
- It stores the n outputs of phase 1, which answer phase 3. For each vertex it also keeps one coordinate with the label of |s_v⟩ ∈ {|0⟩, |+⟩, |−⟩}.
- In phase 4, it measures Z_b on the register for b ∈ Q, and samples z_b for b ∉ Q from |⟨z_b|s_b⟩|². It overwrites the coordinate of b with the outcome, using two further values, so that it marks b as measured. Its outcomes therefore have the law |a_B(z)|².

After phase 4, the register holds the qubits of Q ∩ C in the state

Σ_y a_{Q∩C}(y) e^{−iΦ_Q(z, y)} |y⟩,

where Φ_Q is the part of Φ with u ⊆ Q. The model then:

- prepares a spare qubit in |s_v⟩ for each v ∈ C \ Q, using at most min(k, n − t) spares;
- for each stored u with z = 1 on u ∩ B and u ∩ C nonempty, applies exp(−iγ_u |1⟩⟨1|_{u ∩ C}) to the k qubits of C.

The remaining part of Φ, from the sets with u ∩ C empty, is a global phase.

The k qubits of C now hold the same state as in the n-qubit model, up to a global phase. Phase 5 acts on these k qubits alone, so the hybrid applies the same unitaries and measurements. Every output of every phase thus has the same joint law as in the n-qubit model.

The classical memory holds:

- N − (t choose k) weights;
- the n outputs of phase 1;
- one coordinate per vertex for its label or Z outcome.

That is c = N − (t choose k) + 2n. ∎

The script [sim/hybrid_check.py](sim/hybrid_check.py) compares the two models branch by branch for n ≤ 6 and k ∈ {2, 3}. It checks that the branch probabilities agree to 1e-12, and that the states on C agree up to a global phase to 1e-12.

## Proof of Theorem 2

The proof of Theorem B.3 of [1] uses two facts about the model.

1. **The latent map.** The map from the first N + n tokens to the latent manifold L meets the stated assumptions: C², a strong submersion on an open set U ⊆ K with dim U ≥ dim L + 2, and the condition at ∂U. Here K is the N-dimensional set of inputs fixed in that theorem.
2. **Same latent, same outputs.** For a fixed random vector r, two inputs with the same latent point and the same later tokens give the same later outputs.

For a hybrid model, (1) is the hypothesis, with L = R^c × H_q, and (2) holds by the definition of the model. The rest of that proof then applies word for word. It finds three inputs in one fiber whose completions by the measurement sequence of Lemma B.1 of [1] have output supports with empty common intersection. So a hybrid with finite backward cross entropy has no such open set U, which means dim L ≥ N − 1. Here dim L = c + 4^q − 1, so c ≥ N − 4^q. ∎

## Proof of the corollary

The two bounds are Theorems 1 and 2. If c ≤ (1 − δ)N, then Theorem 2 gives 4^q ≥ δN. For the other direction, (m choose k)/N = ∏_{j<k} (m − j)/(n − j) ≥ ((m − k)/n)^k for m ≥ k. So (q − k choose k) ≥ δN + 2n holds once q − 2k ≥ (δ + 2n/N)^{1/k} n. For fixed k ≥ 2 and δ, 2n/N → 0, so this is (δ^{1/k} + o(1)) n.

## Scope

- Only the qubit variant is covered. For qumodes the state space has infinite dimension, so Theorem 2 gives nothing there.
- Theorem 2 needs the assumptions of Theorem B.3 of [1] for the joint map to (λ, ρ), and it inherits the form of that theorem. With unitary steps only, the states are pure. If they also stay in one affine chart of the projective space, the same argument gives c ≥ N − 2^{q+1} + 1.
- Between (q − k choose k) and 4^q the true number of classical coordinates a qubit register can replace is not determined here. Theorem 1 keeps a block of vertices quantum. It is not known whether some other use of the register replaces more.
- Other work on memory with both classical and quantum parts treats parity learning [3]. For classical streaming models in general, [2] bounds the number of latent states by a contextuality measure.

## References

1. E. R. Anschuetz, X. Gao. Arbitrary Polynomial Separations in Trainable Quantum Machine Learning. arXiv:2402.08606, Theorem B.3, Lemma B.1 and Appendix B.1.
2. M. H. Teo, W. Yang, J. Sud, T. Tomesh, F. T. Chong, E. R. Anschuetz. k-Contextuality as a Heuristic for Memory Separations in Learning. arXiv:2507.11604.
3. Q. Liu, R. Raz, W. Zhan. Memory-Sample Lower Bounds for Learning with Classical-Quantum Hybrid Memory. STOC 2023, arXiv:2303.00209.
