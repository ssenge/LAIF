# Online learning of quantum states with logarithmic loss: regret Θ(d² log T)

Written 7 Nov 2026.

## Problem

In the game of [1] (introduced in [2, 3]), at each round t = 1, …, T a learner announces a d × d density matrix ρ_t, then an opponent announces a nonzero positive semidefinite A_t with eigenvalues in [0, 1], and the learner suffers −log tr(A_t ρ_t). The regret is measured against the best fixed density matrix in hindsight. Exponential weights with the uniform prior has regret at most log C(T + k, k) ≤ k log(e(T + k)/k), with k = d² − 1 [1, Theorem 4.5]. For lower bounds, [1, Theorem 1.1] shows that no algorithm has regret O(d^γ log T) with γ < 2 once T ≫ d² log d, and the classical special case gives Ω(d log T). [1, Remark 3.4] notes that these do not yet give a matching Ω(d² log T) bound and leaves the minimax regret open.

## Result

Write k = d² − 1, V_d for the volume of the set of d × d density matrices in the trace-inner-product metric on its affine hull [4],

V_d = √d (2π)^{d(d−1)/2} Γ(1)Γ(2)⋯Γ(d) / Γ(d²),

and c_d = (k/2) log(2πe(d + 1)/d) − log V_d.

**Theorem 1.** For every d ≥ 2, every T ≥ 1 and every learner, possibly randomized, there is an opponent whose matrices A_t are rank-one projectors such that the expected regret is at least

(k/2) log T − c_d.

**Corollary 2.** Write c_d = (k/2) log(C_d d³). Then C_d = e^{1/2}(1 + 1/d + O(log d/d²)), and C_d decreases over 2 ≤ d ≤ 10^5 from C_2 < 2.47. So for these d the regret is at least

((d² − 1)/2) log(T/(2.47 d³)),

and for larger d the same holds with 2.47 replaced by e^{1/2}(1 + o(1)). In particular, for every δ > 0, 2 ≤ d ≤ 10^5 and T ≥ (2.47 d³)^{1+δ} the minimax regret lies between ((d² − 1)/2)(δ/(1 + δ)) log T and (d² − 1) log(e(T + d²)/(d² − 1)). This gives the order Θ(d² log T) asked for in [1, Remark 3.4]. The leading constants per real dimension are 1/2 and 1.

The opponent of Theorem 1 is oblivious and stochastic: it draws a state at random and reports the outcomes of a fixed measurement on independent copies. So the bound also holds for the statistical version of the game, the online form of maximum-likelihood tomography that motivates [2].

## Proof

**Opponent.** Let μ be the uniform probability measure on the unit sphere of C^d. Draw ρ from the flat (volume) measure on the density matrices, then v_1, …, v_T independently with density p_ρ(v) = d⟨v|ρ|v⟩ with respect to μ, and play A_t = |v_t⟩⟨v_t|. This is a measurement with outcome density p_ρ, since ∫ d|v⟩⟨v| dμ = I. Learners are measurable maps from past outcomes to states. The proof only uses the first two moments of μ, so any finite weighted 2-design can replace μ, which gives an opponent with finitely many matrices.

**Regret is at least the mutual information.** The learner's choice ρ_t depends on v_1, …, v_{t−1} (and its own randomness; by concavity of the logarithm, replacing ρ_t by its conditional mean does not increase the loss, so assume ρ_t deterministic). It defines a density q_t(v) = d⟨v|ρ_t|v⟩, so q(v_1, …, v_T) = Π_t q_t(v_t) is a probability density on sequences. The best state in hindsight does at least as well as ρ, so

Regret ≥ Σ_t log(⟨v_t|ρ|v_t⟩/⟨v_t|ρ_t|v_t⟩) = log(P_ρ(v^T)/q(v^T)),

where P_ρ is the product density. Its expectation is E_ρ D(P_ρ ‖ q) (relative entropy), which equals I(ρ; v^T) + D(P̄ ‖ q) ≥ I(ρ; v^T), with P̄ the average of P_ρ over the prior.

**Mutual information.** Identify the traceless self-adjoint matrices, with the trace inner product, with R^k. Let ρ̂ = (1/T) Σ_t ((d + 1)|v_t⟩⟨v_t| − I). Since ∫ d⟨v|ρ|v⟩ |v⟩⟨v| dμ = (ρ + I)/(d + 1), each term has mean ρ, and tr ρ̂ = 1, so ρ − ρ̂ is traceless. Each term has squared norm ‖(d + 1)|v⟩⟨v| − I‖² = d² + d − 1, so

E‖ρ − ρ̂‖² = (d² + d − 1 − E tr ρ²)/T ≤ (d² + d − 1 − 1/d)/T = (d + 1)k/(dT).

By data processing and since the normal law maximises the differential entropy at a given second moment,

I(ρ; v^T) ≥ I(ρ; ρ̂) = h(ρ) − h(ρ − ρ̂ | ρ̂) ≥ h(ρ) − h(ρ − ρ̂) ≥ log V_d − (k/2) log(2πe(d + 1)/(dT)),

because h(ρ) = log V_d for the flat prior. This is (k/2) log T − c_d. Averaging over the random opponent, some fixed sequence of rank-one projectors attains at least this expected regret.

**Corollary 2.** From log Γ(n) = (n − ½) log n − n + ½ log 2π + O(1/n) and log Π_{j≤d} Γ(j) = (d²/2) log d − 3d²/4 + (d/2) log 2π + O(log d),

log V_d = −(3/2)d² log d + d²(½ log 2π + ¼) + O(log d),

so 2c_d/k = 3 log d + ½ + log((d + 1)/d) + O(log d/d²) = 3 log d + ½ + 1/d + O(log d/d²). The values of C_d for every d ≤ 10^5 are evaluated directly. For T ≥ (2.47d³)^{1+δ}, log(T/(2.47d³)) ≥ (δ/(1 + δ)) log T. The upper bound is log C(T + k, k) from [1, Theorem 4.5].

## Remarks

- The proof is the parametric redundancy bound for universal coding [6, 7], applied with the measurement that maps every learner to a sequential probability assignment; the only quantum inputs are the volume formula of [4] and linear inversion with a uniform rank-one measurement.
- The threshold d³ matches the single-copy tomography scale: with the volume radius of order d^{−1/2} and a per-round error of order d² in squared trace-inner-product norm, the information per real dimension starts to grow at T of order d³. The bound of [1, Theorem 1.1] covers the range from d² log d.
- The same argument with real unit vectors (density d⟨v|ρ|v⟩, linear inversion ((d + 2)vv^T − I)/2) and the uniform prior on the ball of radius 1/d around I/d, which lies inside the real density matrices, gives (d(d + 1)/2 − 1)/2 · log T − O(d² log d) for the real version [1, Corollary 3.5]. With this smaller prior the threshold is T of order d⁴.
- The leading constants differ by a factor 2. In the classical case the minimax constant is 1/2 per dimension [5]. The order d² log T was expected in [8]. For universal compression of quantum sources, where the coder acts on many copies at once, the redundancy is also ((d² − 1)/2) log n to leading order [9]; that setting differs from the one-outcome-at-a-time predictions here.

## Check

`sim/check.py` (about 20 s) checks:
- the volume formula against the ball of qubit states (radius 1/√2) for d = 2 and a sampled volume for d = 3;
- that linear inversion is unbiased with the stated second moment, for d = 2, 3, 5;
- the constants c_d and C_d for every d ≤ 10^5;
- a plug-in learner (projected linear inversion mixed with I/d) on d = 2 against the best state in hindsight, whose mean regret over the random opponent stays above the bound of Theorem 1 (T = 100, 1000, 5000);
- the uniform-prior mixture on d = 2 (by quadrature) below log C(T + 3, 3) on random, basis and state-generated sequences.

The output is in `sim/out.txt`.

## References

1. Y.-H. Li, W.-F. Tseng. Regret Lower Bound for Online Learning of Quantum States with Logarithmic Loss, with Applications to Quantum State Tomography and Confidence Sequences for Matrix Means. arXiv:2610.21273 (2026).
2. C.-M. Lin, Y.-M. Hsu, Y.-H. Li. An online algorithm for maximum-likelihood quantum state tomography. 24th Annual Conference on Quantum Information Processing (2021), arXiv:2012.15498.
3. J. Zimmert, N. Agarwal, S. Kale. Pushing the efficiency-regret Pareto frontier for online learning of portfolios and quantum states. Proc. 35th Conference on Learning Theory, 182-226 (2022).
4. K. Życzkowski, H.-J. Sommers. Hilbert-Schmidt volume of the set of mixed quantum states. J. Phys. A 36, 10115 (2003), arXiv:quant-ph/0302197.
5. E. Ordentlich, T. M. Cover. The cost of achieving the best portfolio in hindsight. Mathematics of Operations Research 23, 960-982 (1998).
6. J. Rissanen. Universal coding, information, prediction, and estimation. IEEE Transactions on Information Theory 30, 629-636 (1984).
7. B. S. Clarke, A. R. Barron. Information-theoretic asymptotics of Bayes methods. IEEE Transactions on Information Theory 36, 453-471 (1990).
8. W.-F. Tseng, K.-C. Chen, Z.-H. Xiao, Y.-H. Li. Online learning of quantum states with logarithmic loss via VB-FTRL. Proc. 36th International Conference on Algorithmic Learning Theory, 1285-1312 (2025), arXiv:2311.04237.
9. C. Krattenthaler, P. B. Slater. Asymptotic redundancies for universal quantum coding. IEEE Transactions on Information Theory 46, 801-819 (2000), arXiv:quant-ph/9612043.
