# Random Fourier feature dequantization of hybrid models with classical encoders

Written 6 Nov 2026.

## Setting

A parametrized quantum circuit with a fixed data encoding computes functions f(z) = Σ_ω c_ω e^{i⟨ω, z⟩} of its input z ∈ R^d, with frequencies ω in a finite set Ω fixed by the encoding [1]. For a probability vector p on Ω, symmetric under ω ↦ −ω and nonzero on Ω, the re-weighted kernel of [1, Eq. (49)] is

K(z, z′) = p_0 + Σ_{i ≥ 1} p_i cos⟨ω_i, z − z′⟩,  K(z, z) = 1,

where p_0 is the weight of ω = 0 and ω_1, ω_2, … are the nonzero frequencies up to sign, with p_i the total weight of ±ω_i. All circuit functions lie in its reproducing kernel Hilbert space H_K.

[1, Theorem 1] then gives a classical procedure, random Fourier feature (RFF) ridge regression, whose risk is within ε of the best circuit function. It uses n data points and M frequencies sampled from p. Both counts are polynomial if:

- the best circuit function has RKHS norm C = poly(d);
- the labels are bounded by b;
- the operator norm ‖T_K‖ of the kernel integral operator on L²(P_X) is at least 1/poly(d).

[1, Lemma 1] computes ‖T_K‖ = max_i p_i/2 under two assumptions: the input law P_X is uniform, and the frequencies are integers. [2] uses this lemma in the same way. A hybrid model puts a classical encoder g in front of the circuit, x ↦ f(g(x)). The circuit then sees the law g#P_X of g(x), which is not uniform in general, so the operator-norm step does not cover hybrids as stated.

## Results

**Lemma 1 (operator norm for every input law).** For every probability measure P on R^d, with T_K acting on L²(P),

max{ p_0, max_{i ≥ 1} p_i/2 } ≤ ‖T_K‖ ≤ 1.

For integer frequencies and P uniform on [0, 2π)^d, the lower bound is an equality.

So in [1, Theorem 1] the constant c_0, which grows with 1/‖T_K‖, can be bounded with ‖T_K‖ ≥ p_max/2 for every input law, where p_max = max_ω p(ω). The constant n_0, which grows with ‖T_K‖, can be bounded with ‖T_K‖ ≤ 1. The conclusion of [1, Theorem 1] then holds for every regression problem with |y| ≤ b, under the same conditions on C and p_max, with no assumption on P_X and none on the frequencies. The same applies where [2, Appendix E] uses [1, Lemma 1].

**Theorem 2 (fixed encoder).** Let g: X′ → R^d be any measurable map, for example a classical network with fixed weights. Let (x, y) ∼ P on X′ × [−b, b], and let f*_g minimize the risk R(f ∘ g) over the circuit class, with ‖f*_g‖_K ≤ C. Run RFF ridge regression as in [1, Theorem 1] on the features ψ(g(x), ν), with ν sampled from p, using the n and M of [1, Theorem 1] with ‖T_K‖ replaced by p_max/2 in c_0. Then, with probability at least 1 − δ,

R(f̂) ≤ R(f*_g ∘ g) + ε.

So a classical encoder in front of the circuit, whatever it is and whatever the data law, does not affect the RFF dequantization of [1]. The conditions are those for the circuit alone: the norm C, the peak p_max, and efficient sampling from p.

**Theorem 3 (finite class of encoders).** Let G be a finite set of encoders with ‖f*_g‖_K ≤ C for all g ∈ G. Sample the M frequencies once. Then:

1. for each g ∈ G, fit RFF ridge regression on n points as in Theorem 2, at confidence δ/(2|G|), and clip the output to [−b, b];
2. pick the g with the smallest squared error on n_v ≥ 32 b⁴ log(4|G|/δ)/ε² further points.

With probability at least 1 − δ, the chosen model ĥ satisfies

R(ĥ) ≤ min_{g ∈ G} R(f*_g ∘ g) + 2ε.

The number n depends on |G| only through log⁴(2|G|/δ), and the time is |G| times that of one regression.

## Proofs

*Proof of Lemma 1.* Write c_i(z) = cos⟨ω_i, z⟩ and s_i(z) = sin⟨ω_i, z⟩. By cos(a − b) = cos a cos b + sin a sin b,

T_K = p_0 |1⟩⟨1| + Σ_{i ≥ 1} p_i (|c_i⟩⟨c_i| + |s_i⟩⟨s_i|)

as operators on L²(P), a sum of positive semidefinite terms. Hence ‖T_K‖ is at least the norm of each term.

- The term p_0|1⟩⟨1| has norm p_0‖1‖² = p_0.
- The nonzero eigenvalues of |c_i⟩⟨c_i| + |s_i⟩⟨s_i| are those of the Gram matrix of (c_i, s_i) in L²(P). Its trace is E_P[cos² + sin²] = 1, so its largest eigenvalue is at least 1/2, and the term has norm at least p_i/2.

For the upper bound, ‖T_K‖ ≤ tr T_K = ∫ K(z, z) dP(z) = 1.

For P uniform on the torus and integer frequencies, the functions 1, c_i, s_i are orthogonal with squared norms 1, 1/2, 1/2. So they are eigenfunctions with eigenvalues p_0 and p_i/2, and T_K vanishes on their orthogonal complement. □

*Proof of Theorem 2.* Let P_g be the law of (g(x), y). For every function f, R_P(f ∘ g) = R_{P_g}(f). So f*_g is the best circuit function for P_g, and the output of RFF ridge regression on the features ψ(g(x), ν) is the output of [1, Theorem 1] on samples of P_g. The input law of P_g is g#P_X, and Lemma 1 bounds ‖T_K‖ on L²(g#P_X). [1, Theorem 1] rests on the random feature bound of [3, Theorem 1], which needs no condition on the input law beyond bounded features and |y| ≤ b. □

*Proof of Theorem 3.*

- **Fitting.** By Theorem 2 and a union bound over G, with probability at least 1 − δ/2 every fitted model ĥ_g has R(ĥ_g) ≤ R(f*_g ∘ g) + ε. This also holds after clipping, since clipping to [−b, b] does not increase the squared loss when |y| ≤ b.
- **Selection.** The clipped models have losses in [0, 4b²]. By Hoeffding's inequality and a union bound, with probability at least 1 − δ/2 every validation error is within 4b²√(log(4|G|/δ)/(2n_v)) ≤ ε/2 of its risk. The chosen model is therefore within ε of the best ĥ_g. □

## Remarks

1. **Trainable encoders.** Theorem 2 covers any encoder once its weights are fixed, including one obtained by training the hybrid. In that case the quantum part can be replaced by RFF features on top of the same encoder at no loss beyond ε. Theorem 3 covers training over a finite set of encoders, such as a grid of weights. For networks whose outputs are Lipschitz in the weights, a grid of spacing η has |G| = (1/η)^{O(#weights)}, so the sample cost stays polynomial while the time grows with |G|. Efficient joint training of encoder and features is not covered.
2. **Zero frequency.** In [1, Lemma 1] the constant function has eigenvalue p_0 under the uniform law, not p_0/2. This only increases ‖T_K‖ when p_0 is the largest weight, so the conclusions of [1] are unaffected.
3. **Lower bounds.** Lemma 1 concerns the sufficient conditions of [1]. The lower bounds of [1, Section 4.7] are not treated here.

## Check

`sim/operator_norm_check.py` evaluates ‖T_K‖ exactly on empirical laws of 400 points, as the top eigenvalue of K/m. It uses integer and real frequencies, flat and peaked weights, and five laws:

- uniform;
- two points;
- a narrow Gaussian;
- the output of a random two-layer tanh encoder;
- the same encoder on nearly constant inputs.

It also confirms equality on the uniform grid of the torus.

```
lower bound max(p0, pmax/2) <= ||T_K|| <= 1 on 100 cases; smallest ratio ||T_K|| / bound = 1.0018
uniform law on the torus, integer frequencies: ||T_K|| = max(p0, pmax/2) exactly
Lemma 1 checks pass
```

## References

1. R. Sweke, E. Recio-Armengol, S. Jerbi, E. Gil-Fuster, B. Fuller, J. Eisert, J. J. Meyer. Potential and limitations of random Fourier features for dequantizing quantum machine learning. Quantum 9, 1640 (2025), arXiv:2309.11647.
2. M. Sahebi, A. Barthe, Y. Suzuki, Z. Holmes, M. Grossi. On Dequantization of Supervised Quantum Machine Learning via Random Fourier Features. arXiv:2505.15902.
3. A. Rudi, L. Rosasco. Generalization properties of learning with random features. NeurIPS 2017, arXiv:1602.04474.
