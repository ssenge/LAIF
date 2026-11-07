# Random frequency feature dequantization of hybrid models with classical encoders

Written 6 Nov 2026.

## Setting

A parametrized quantum circuit with a fixed data encoding computes functions f(z) = Σ_ω c_ω e^{i⟨ω, z⟩} of its input z ∈ R^d, with frequencies ω in a finite set Ω fixed by the encoding [1].

**Kernel.** Take a probability vector p on Ω that is symmetric under ω ↦ −ω and nonzero on Ω. The re-weighted kernel of [1, Eq. (49)] is

K(z, z′) = Σ_{ω ∈ Ω} p(ω) e^{i⟨ω, z − z′⟩} = p_0 + Σ_{i ≥ 1} p_i cos⟨ω_i, z − z′⟩,  K(z, z) = 1.

Here p_0 = p(0), the ω_i are the nonzero frequencies up to sign, and p_i = 2p(ω_i). Write

q = max_{ω ∈ Ω} p(ω) = max{ p_0, max_{i ≥ 1} p_i/2 }

for the largest frequency probability. In the notation of [1, Eq. (70)], q ≥ p_max/2. All circuit functions lie in the reproducing kernel space H_K, with ‖f‖²_K = Σ_ω |c_ω|²/p(ω).

**Known guarantee.** [1, Theorem 1], built on [3, Theorem 1], gives a classical procedure, random frequency feature (RFF) ridge regression. Its risk is within ε of the best function, using n data points and M frequencies sampled from p. Both counts are polynomial if three quantities are polynomially bounded:

- the RKHS norm C of the risk minimizer;
- the label bound b;
- 1/‖T_K‖, where T_K is the kernel integral operator on L²(P_X).

**The gap for hybrids.** [1, Lemma 1] computes ‖T_K‖ under two assumptions: the input law P_X is uniform on the torus, and the frequencies are integers. [2] uses this lemma in the same way. A hybrid model puts a classical encoder g in front of the circuit, x ↦ f(g(x)). The circuit then sees the law g#P_X of g(x), which is not uniform in general. So the operator-norm step does not cover hybrids as stated.

## Results

**Lemma 1 (operator norm for every input law).** For every probability measure P on R^d, with T_K acting on L²(P),

q ≤ ‖T_K‖ ≤ 1.

For integer frequencies and P uniform on [0, 2π)^d, the lower bound is an equality.

**Corollary 2.**

1. In [1, Theorem 1] the input law enters the constants only through ‖T_K‖. The constant c_0 grows like 1/‖T_K‖ and n_0 like 1/‖T_K‖² [3]. Both are therefore bounded for every input law by putting ‖T_K‖ = q, with no assumption on P_X or on the frequencies.
2. Replace p by p′ = (p + δ_0)/2. Then q′ ≥ 1/2 for every input law, while ‖f‖_{K′} ≤ √2 ‖f‖_K for every f, since p′ ≥ p/2, and sampling from p′ is as easy as from p. So the operator-norm condition can always be met at a factor √2 in the norm. The conditions that remain are the norm C and efficient sampling from p.

**Norm hypothesis.** [3, Theorem 1] compares with f_H, the minimum-norm minimizer of the risk over H_K, assumed to exist. Its constants grow with ‖f_H‖_K. Since the circuit class lies in H_K, R(f_H) is at most the risk of every circuit function. We state the hypothesis in this form, for the law the circuit actually sees.

**Theorem 3 (fixed encoder).** Let g: X′ → R^d be any measurable map, for example a classical network with fixed weights, and let (x, y) ∼ P on X′ × [−b, b]. Let P_g be the law of (g(x), y). Assume the risk under P_g has a minimizer over H_K, and that its minimum-norm minimizer f_H satisfies ‖f_H‖_K ≤ C.

Run RFF ridge regression on the features ψ(g(x), ν), with ν sampled from p. Use the n and M of [1, Theorem 1], with ‖T_K‖ replaced by q. Then, with probability at least 1 − δ,

R(f̂) ≤ R(f_H ∘ g) + ε ≤ min_θ R(f_θ ∘ g) + ε.

So for any classical encoder and any data law, the RFF dequantization of [1] applies to the hybrid. The circuit's conditions apply unchanged: the norm C and efficient sampling from p. The norm hypothesis is now on f_H under P_g, which depends on g#P_X.

**Theorem 4 (finite class of encoders).** Let G be a finite set of encoders, each meeting the hypothesis of Theorem 3. Sample the M frequencies once, then:

1. for each g ∈ G, fit RFF ridge regression on n points as in Theorem 3, at confidence δ/(2|G|), and clip the output to [−b, b];
2. pick the g with the smallest squared error on n_v ≥ 32 b⁴ log(4|G|/δ)/ε² further points.

With probability at least 1 − δ, the chosen model ĥ satisfies

R(ĥ) ≤ min_{g ∈ G} min_θ R(f_θ ∘ g) + 2ε.

The number n depends on |G| only through a factor log⁴(O(|G|/δ)), and the time is |G| times that of one regression.

## Proofs

*Proof of Lemma 1.* Write c_i(z) = cos⟨ω_i, z⟩ and s_i(z) = sin⟨ω_i, z⟩. By cos(a − b) = cos a cos b + sin a sin b,

T_K = p_0 |1⟩⟨1| + Σ_{i ≥ 1} p_i (|c_i⟩⟨c_i| + |s_i⟩⟨s_i|)

as operators on L²(P), a sum of positive semidefinite terms. Hence ‖T_K‖ is at least the norm of each term.

- The term p_0|1⟩⟨1| has norm p_0‖1‖² = p_0.
- The nonzero eigenvalues of |c_i⟩⟨c_i| + |s_i⟩⟨s_i| are those of the matrix of inner products of (c_i, s_i) in L²(P). Its trace is E_P[cos² + sin²] = 1, so its largest eigenvalue is at least 1/2, and the term has norm at least p_i/2.

For the upper bound, ‖T_K‖ ≤ tr T_K = ∫ K(z, z) dP(z) = 1.

For P uniform on the torus and integer frequencies, the functions 1, c_i, s_i are orthogonal with squared norms 1, 1/2, 1/2. So they are eigenfunctions with eigenvalues p_0 and p_i/2, and T_K vanishes on their orthogonal complement. □

*Proof of Corollary 2.* Part 1 is Lemma 1. For part 2, p′(0) ≥ 1/2, so q′ ≥ 1/2 by Lemma 1. Also p′(ω) ≥ p(ω)/2 for all ω, so ‖f‖²_{K′} = Σ_ω |c_ω|²/p′(ω) ≤ 2‖f‖²_K. □

*Proof of Theorem 3.* For every function f, R_P(f ∘ g) = R_{P_g}(f). The output of RFF ridge regression on the features ψ(g(x), ν) is the output of the procedure of [1, Theorem 1] on samples of P_g. The input law of P_g is g#P_X.

[3, Theorem 1] needs only a Polish input space, bounded continuous features and |y| ≤ b. It then bounds the excess risk over R(f_H) under P_g, with the constants above. Lemma 1 bounds ‖T_K‖ on L²(g#P_X) from below by q. The last inequality holds because every f_θ lies in H_K. □

*Proof of Theorem 4.*

- **Fitting.** By Theorem 3 and a union bound over G, with probability at least 1 − δ/2 every fitted model ĥ_g has R(ĥ_g) ≤ min_θ R(f_θ ∘ g) + ε. The frequencies may be shared, since each event concerns one g. This also holds after clipping, since clipping to [−b, b] does not increase the squared loss when |y| ≤ b.
- **Selection.** The clipped models have losses in [0, 4b²]. By the tail bound for bounded independent variables and a union bound, with probability at least 1 − δ/2 every validation error is within 4b²√(log(4|G|/δ)/(2n_v)) ≤ ε/2 of its risk. The chosen model is therefore within ε of the best ĥ_g. □

## Remarks

1. **Trainable encoders.** Theorem 3 covers any encoder once its weights are fixed, including one obtained by training the hybrid. The frequencies and the regression data must then be independent of the data used to train the encoder. Under that condition, the quantum part can be replaced by RFF features on top of the same encoder at no loss beyond ε. Theorem 4 covers training over a finite set of encoders, for instance a grid of weights. Its time grows with |G|, so efficient joint training of encoder and features is not covered.
2. **Zero frequency.** Under the uniform law, the constant function has eigenvalue p_0, not p_0/2 as in [1, Lemma 1]. This increases ‖T_K‖ whenever p_0 > max_{i ≥ 1} p_i/2, so the conclusions of [1] are unaffected.
3. **Form of the norm hypothesis.** [1, Theorem 1] states its norm hypothesis for the best circuit function. The bound of [3] is relative to the minimum-norm risk minimizer over H_K, whose norm can be larger. Theorems 3 and 4 use the form of [3].
4. **Related work.** [4] gives conditions on the weight vectors of quantum models, in terms of their norms, that are necessary to avoid classical approximation by random features. Lemma 1 concerns the sufficient conditions of [1]. The lower bounds of [1, Section 4.7] are not treated here.

## Check

`sim/operator_norm_check.py` evaluates ‖T_K‖ exactly on empirical laws of 400 points, as the top eigenvalue of K/m. It uses distinct integer frequencies (no repeats up to sign) and real frequencies, flat and peaked weights, and five laws:

- uniform;
- two points;
- a narrow normal density;
- the output of a random two-layer tanh encoder;
- the same encoder on nearly constant inputs.

It also confirms equality on the uniform grid of the torus, and that mixing with the zero frequency gives ‖T_K‖ ≥ 1/2 on every law.

```
q = max(p0, max p_i/2) <= ||T_K|| <= 1 on 100 cases; smallest ratio ||T_K|| / q = 1.0159
mixing with the zero frequency: min ||T_K|| over 20 laws = 0.5140 >= 1/2
uniform law on the torus, integer frequencies: ||T_K|| = q exactly
Lemma 1 checks pass
```

## References

1. R. Sweke, E. Recio-Armengol, S. Jerbi, E. Gil-Fuster, B. Fuller, J. Eisert, J. J. Meyer. Potential and limitations of random Fourier features for dequantizing quantum machine learning. Quantum 9, 1640 (2025), arXiv:2309.11647.
2. M. Sahebi, A. Barthe, Y. Suzuki, Z. Holmes, M. Grossi. On Dequantization of Supervised Quantum Machine Learning via Random Fourier Features. arXiv:2505.15902.
3. A. Rudi, L. Rosasco. Generalization properties of learning with random features. NeurIPS 2017, arXiv:1602.04474.
4. S. Thabet, L. Monbroussou, E. Z. Mamon, J. Landman. When Quantum and Classical Models Disagree: Learning Beyond Minimum Norm Least Square. npj Quantum Information 12, 81 (2026), arXiv:2411.04940.
