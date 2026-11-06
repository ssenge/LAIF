# Gradients of quantum neural networks from quantum data with few-copy measurements

Written 6 Nov 2026.

## Setting

A quantum neural network in the sense of [1, Definition 8] acts on an output qubit 0 and n data qubits:

U(θ) = e^{iθ_M P_M} U_M ⋯ e^{iθ_1 P_1} U_1,  QNN_θ(ρ) = tr(Z_0 U(θ) (|0⟩⟨0| ⊗ ρ) U(θ)†),

with fixed (n + 1)-qubit Pauli operators P_j, fixed circuits U_j and an unknown input state ρ on the data qubits. The task is to output b_1, …, b_M with |b_j − ∂_{θ_j} QNN_θ(ρ)| ≤ ε for all j, with probability at least 2/3 for every input state ρ, from copies of ρ. The circuit is known.

We count copies and use the protocol classes of [2]:

- a *c-copy protocol* measures c fresh copies of ρ jointly in each round, with any POVM chosen adaptively from earlier outcomes [2, Definition 3];
- a *c-copy protocol with k qubits of memory* does the same, but inside a round it takes the copies one at a time and keeps only a k-qubit quantum memory between them [2, Definition 4]. Here k counts every qubit kept between copies, including an output qubit or ancillas of the network. Ancillas used and measured within one step are free.

Known bounds:

| | Copies | Source |
|---|---|---|
| One value QNN_θ(ρ) to ±ε | O(1/ε²), single copies | sampling Z_0 |
| All M gradients, single copies | O(M log M/ε²) by the parameter shift rule; Ω(2^n/ε²) lower bound | [1, Proposition 3], for the model of [1, Definition 2] |
| All M gradients, joint measurements, pure inputs | O(n log²M/ε⁴), batches of O(log²M/ε²) copies measured jointly | [1, Theorem 9] |

[1, Definition 1] asks for backpropagation scaling: a gradient at O(log M) times the time and memory of one function value. [1, Section 4] asks whether this is possible with multiple copies. The results below quantify, in copies, how many must be measured jointly for that.

## Results

Let a ∈ (0, 1] be the minimum of 1 and the absolute constants in [2, Theorems 16 and 17].

**Theorem 1.** For every n there is a quantum neural network with M = 4^n − 1 parameters on n data qubits such that, for every 0 < ε ≤ 2/3:

1. every c-copy protocol that estimates all gradients at θ = 0 to ±ε uses at least
   a · min{ √(M+1)/(cε²), e^{−3cε}/(c³ε⁴) } copies;
2. every c-copy protocol with k ≤ n qubits of memory that does so uses at least
   a · min{ √(M+1)/(cε²), 2^{n−k} e^{−3cε}/(c³ε⁴) } copies;
3. on this network, a 2-copy protocol with k ≤ n qubits of memory estimates all gradients at θ = 0 with O(n · min{2^n/ε², 2^{n−k}/ε⁴}) copies [2, Theorems 6, 13, 14]. So parts 1 and 2 are tight up to a factor n = O(log M) for c = 2.

For c = O(1) and ε ≥ M^{−1/4}, part 1 reads Ω(1/ε⁴), against O(1/ε²) copies for one function value.

**Corollary 2.** Let B ≥ 1 and 0 < ε ≤ 2/3, and suppose a protocol estimates all gradients of the network of Theorem 1 at θ = 0 to ±ε with at most B/ε² copies, that is, at B times the cost of one function value.

1. If it is a c-copy protocol, then
   c ≥ min{ a√(M+1)/B, (a/(e³B))^{1/3} ε^{−2/3} }.
2. If it is a c-copy protocol with k ≤ n qubits of memory and cε ≤ 1, then c ≥ a√(M+1)/B or
   k ≥ n − log₂(c) − log₂(B) − log₂(e³/a).

So gradients at polylog(M) times the cost of one function value need joint measurements on Ω̃(min{√M, ε^{−2/3}}) copies. With cε ≤ 1 and c < a√(M+1)/B, they also need all but O(log(cB)) qubits of memory. At constant ε the corollary gives only constant bounds. The protocol of [1, Theorem 9], stated for pure inputs, measures batches of O(log²M/ε²) copies jointly.

## Proof

The network is the one behind [1, Proposition 3], with an output qubit added.

**Lemma 1.** Let Q_1, …, Q_M be the non-identity Pauli operators on the data qubits, U_1 = H_0 ⊗ I, U_j = I for j ≥ 2, and P_j = Y_0 ⊗ Q_j. Then for every state ρ,

∂_{θ_j} QNN_θ(ρ) |_{θ=0} = 2 tr(Q_j ρ).

*Proof.* At θ = 0 every rotation is the identity, and H_0 is applied first, so

∂_j QNN|_{θ=0} = tr(Z_0 · i[Y_0 ⊗ Q_j, σ]) with σ = |+⟩⟨+| ⊗ ρ.

This does not depend on the order of the rotations. By cyclicity it equals i · tr([Z_0, Y_0 ⊗ Q_j] σ), and [Z, Y] = −2iX, so it equals 2 tr((X_0 ⊗ Q_j) σ) = 2⟨+|X|+⟩ tr(Q_j ρ) = 2 tr(Q_j ρ). □

*Proof of Theorem 1.* Take the network of Lemma 1. Gradients to ±ε at θ = 0 give tr(Q_j ρ) to ±ε/2 for all non-identity Q_j, and tr(Iρ) = 1 is known. So any gradient protocol is a protocol for Pauli shadow tomography of all n-qubit Pauli strings at precision ε/2, with the same measurements and the same number of copies, so in the same class.

- **Part 1.** By [2, Theorem 17] at precision ε/2, such a protocol uses at least a′ · min{4 · 2^n/(cε²), 16e^{−3cε}/(c³ε⁴)} copies, where a′ ≥ a is the constant there. With 2^n = √(M+1), this is at least the bound of part 1.
- **Part 2.** The same argument with [2, Theorem 16], which carries the factor 2^{n−k}.
- **Part 3.** Conversely, estimates of tr(Q_j ρ) to ±ε/2 give the gradients to ±ε. [2, Theorem 14] estimates all tr(Q_j ρ), with signs, from O(n2^{n−k}/ε⁴) copies with 2-copy measurements and k qubits of memory. Single-copy classical shadows with random Clifford measurements need O(n2^n/ε²) copies [2, Section 2.2.1].

In parts 1 and 2 the hard instances of [2] are the states (I + 3(ε/2)P)/2^n, which are states for ε ≤ 2/3, and the reduction only rescales ε. □

*Proof of Corollary 2.*

- **Part 1.** If cε > 1, then c > 1/ε ≥ ε^{−2/3}, which exceeds the second term since a ≤ 1 ≤ e³B. Otherwise e^{−3cε} ≥ e^{−3}. By Theorem 1, B/ε² is at least the minimum there. If the first term is the smaller one, then a√(M+1)/(cε²) ≤ B/ε², so c ≥ a√(M+1)/B. If the second term is the smaller one, then ae^{−3}/(c³ε⁴) ≤ B/ε², so c³ ≥ a/(e³Bε²).
- **Part 2.** If the first term of Theorem 1, part 2, is the smaller one, then c ≥ a√(M+1)/B as in part 1. Otherwise, since cε ≤ 1 gives e^{−3cε} ≥ e^{−3}, we get a2^{n−k}e^{−3}/(c³ε⁴) ≤ B/ε², so 2^{n−k} ≤ e³Bc³ε²/a ≤ e³Bc/a, using c²ε² ≤ 1. □

## Remarks

1. **Other numbers of parameters.** For 3 ≤ M < 4^n − 1, put the network of Lemma 1 on m = ⌊log₄(M + 1)⌋ data qubits, add M − 4^m + 1 generators Y_0 ⊗ I, whose derivatives at θ = 0 equal 2, and feed in ρ′ ⊗ |0⟩⟨0| on the other n − m qubits. A protocol for this network gives one for ρ′ with the same copies, since |0⟩⟨0| can be prepared. Part 1 of Theorem 1 then holds with √(M+1) replaced by 2^m ≥ √(M+1)/2, and part 2 likewise, with 2^{m−k} for k ≤ m.
2. **Mixed inputs.** The hard states (I + 3(ε/2)P)/2^n are close to maximally mixed. [1, Section 4] notes that its single-copy separation does not carry over to pure states. [1, Theorem 9] is stated for pure inputs, and the bounds above are for mixed ones.
3. **Range of c.** [2] discusses c up to poly(n). Its Theorems 16 and 17 hold for every c, and so does Theorem 1, but the factor e^{−3cε} makes them weak once cε is large, as for the batches of [1, Theorem 9].

## Check

`sim/gradient_check.py` builds the network of Lemma 1 for n = 1, 2, 3 (M = 3, 15, 63) with a random mixed ρ. It compares central finite differences with 2 tr(Q_j ρ), and repeats one entry with the rotations in random order.

```
n = 1: M = 3 parameters, max |dQNN/dtheta_k - 2 tr(P_k rho)| = 6.9e-11
n = 2: M = 15 parameters, max |dQNN/dtheta_k - 2 tr(P_k rho)| = 5.5e-11
n = 3: M = 63 parameters, max |dQNN/dtheta_k - 2 tr(P_k rho)| = 4.2e-11
gradient identity of Lemma 1 holds
```

In the script, P_k denotes the data-qubit Pauli Q_k.

## References

1. A. Abbas, R. King, H.-Y. Huang, W. J. Huggins, R. Movassagh, D. Gilboa, J. R. McClean. On quantum backpropagation, information reuse, and cheating measurement collapse. NeurIPS 2023, arXiv:2305.13362.
2. S. Chen, W. Gong, Q. Ye. Optimal tradeoffs for estimating Pauli observables. arXiv:2404.19105.
