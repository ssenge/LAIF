# What a JEPA world model keeps: an exactly solvable linear world

Written 24 Nov 2026.

A JEPA world model such as LeWM [1] trains an encoder and a predictor with two terms: the error of predicting the next latent from the current latent and the action, and a regularizer (SIGReg [2]) that pushes the latents towards the standard normal law. Planning then searches for actions whose predicted latent is close to the latent of a goal. Several recent studies report that such models can lose what planning needs: latents that follow static content of the scene [3], latents that barely respond to the action [4], and lost controllable modes [5]; the remedies add an inverse-dynamics term that reads the action from consecutive latents [4, 5, 6, 7, 8].

This folder solves the objective exactly in a linear world with normal noise, for a latent dimension K below the state dimension. The solution says which directions of the state the prediction objective keeps (Theorem 1), shows that actuator noise makes every near-minimizer blind to the action (Theorem 2), shows that an inverse-dynamics term can be met by a latent whose response to the action is arbitrarily small (Theorem 3), and gives a term, the covariance between future latents and past actions, whose optimum is the top eigenspace of a controllability Gramian and which has no such loophole (Theorem 4).

## Setting

**World.** The state s_t ∈ ℝ^d follows s_{t+1} = A s_t + B a_t + w_t with actions a_t ∼ N(0, I_m), noise w_t ∼ N(0, Q), all independent of each other and of s_t, and s_t stationary with covariance Σ ≻ 0, so Σ = AΣAᵀ + BBᵀ + Q. Static content is included: a coordinate with s_{t+1} = s_t that varies between episodes is a mode with eigenvalue 1, no action and no noise. The observation is x_t = C s_t with C injective, so a linear encoder z = Wx is z = Es with an arbitrary K × d matrix E = WC, and C plays no further role.

**Objective.** The latents are normal, so the regularizer vanishes exactly when EΣEᵀ = I_K. The prediction loss of an encoder is L(E) = min E|z_{t+1} − f(z_t, a_t)|² over all predictors f.

**Whitened coordinates.** Let Ã = Σ^{−1/2}AΣ^{1/2}, B̃ = Σ^{−1/2}B and Q̃ = Σ^{−1/2}QΣ^{−1/2}. Then ÃÃᵀ + B̃B̃ᵀ + Q̃ = I, and the encoders with EΣEᵀ = I are exactly E = UᵀΣ^{−1/2} with UᵀU = I_K. Write M = UᵀÃU and G = UᵀB̃. The matrix G is the action response of the latent: z_{t+1} = M z_t + G a_t + η_t.

## Results

**Theorem 1 (what the prediction loss measures).** For E = UᵀΣ^{−1/2},

    L(E) = tr(UᵀQ̃U) + ‖(I − UUᵀ)ÃᵀU‖²_F = K − ‖UᵀÃU‖²_F − ‖UᵀB̃‖²_F,

attained by the linear predictor f(z, a) = Mz + Ga. The first term is the share of the latent variance that is fresh noise, the second is what leaks in from the discarded directions. Consequences:

- L(E) is at least the sum of the K smallest eigenvalues of Q̃, with equality when the span of the corresponding eigenvectors is invariant under Ãᵀ.
- For decoupled modes (A, Q and Σ diagonal) the minimizers keep the K modes with the smallest noise share qᵢ = Qᵢᵢ/Σᵢᵢ. Neither the gain of a mode in the observation nor its response to the action enters: the variance that an action explains and the variance that the past explains count the same.
- L(E) = 0 exactly when EQ = 0 and EA = PE for some P, that is, when the latent is a noise-free autonomous function of the state.

**Theorem 2 (action-blind minimizers).** Assume the actuators are noisy, Q ⪰ σ²BBᵀ with σ > 0. Then every encoder with EΣEᵀ = I satisfies

    ‖G‖²_F ≤ L(E)/σ².

So the action response of an encoder is bounded by its prediction loss. If in addition K noise-free autonomous directions exist (a K-dimensional subspace 𝒱 with Aᵀ𝒱 ⊆ 𝒱 and Q𝒱 = 0, for example K static modes), the minimum of L is 0, and every minimizer has G = 0 and z_{t+1} = Pz_t with P orthogonal: the predicted latent after any sequence of actions is P^H z_t, and the cost of a planner does not depend on the actions.

**Theorem 3 (inverse dynamics asks for decodability, not for response).** Let L_inv(E) = min E|a_t − h(z_t, z_{t+1})|² over all readouts h.
(a) If I − MMᵀ is invertible, L_inv(E) = m − tr(Gᵀ(I − MMᵀ)^{−1}G).
(b) Let u be a static direction (unit, Ãᵀu = u) and v a unit vector orthogonal to u. The one-dimensional latent along u_ε = (u + εv)/√(1 + ε²) has prediction loss O(ε²) and action response ‖G‖² = ε²|B̃ᵀv|²/(1 + ε²), yet the readout explains the share

    |B̃ᵀv|² / ((1 + M_ε)(1 − vᵀÃv)) → |B̃ᵀv|² / (2(1 − vᵀÃv))   (ε → 0)

of the action variance, for every ε > 0. A readout of the difference z_{t+1} − z_t does the same.
(c) For static modes and decoupled scalar modes with (αᵢ, bᵢ², qᵢ), αᵢ² + bᵢ² + qᵢ = 1, where bᵢ² is the share of the variance of mode i due to its action, the infimum of L + λL_inv keeps mode i at full scale only when

    λ > λᵢ = 2(1 + αᵢ) qᵢ/bᵢ²,

and below λᵢ it is approached by latents whose action response tends to 0.

**Theorem 4 (the action-covariance term).** For a horizon H ≥ 1 let

    T_H(E) = Σ_{h=1}^{H} ‖Cov(z_{t+h}, a_t)‖²_F.

(a) T_H(E) = tr(UᵀW̃_H U) with W̃_H = Σ_{h=0}^{H−1} Ã^h B̃B̃ᵀ(Ã^h)ᵀ = Σ^{−1/2}W_HΣ^{−1/2}, where W_H is the H-step controllability Gramian, and 0 ⪯ W̃_H ⪯ I. For a unit vector u, uᵀW̃_H u is the share of the variance of the direction u that the last H actions caused.
(b) Over all encoders with EΣEᵀ = I, T_H is maximal exactly on the span of eigenvectors for the K largest eigenvalues of W̃_H, with value their sum.
(c) The latent displacements that action sequences of total energy 1 reach in H steps form the ellipsoid with matrix UᵀW̃_H U. So the maximizers of T_H are the latents in which goals are cheapest to reach.
(d) T_H is quadratic in the scale of an action-dependent component: the latent of Theorem 3(b) has T_H = ε² vᵀW̃_H v/(1 + ε²). In the world of Theorem 3(c) the minimizers of L − μT_H keep mode i exactly when μ > qᵢ/wᵢ with wᵢ = bᵢ²(1 − αᵢ^{2H})/(1 − αᵢ²), which is at most qᵢ/bᵢ², a factor 2(1 + αᵢ) or more below λᵢ.

Taken together: the prediction objective ranks directions by how little fresh noise they carry and treats static content as ideal; with noisy actuators it removes the action from the latent; reading the action back restores it only as an arbitrarily small component; a term that measures how much of the latent variance the actions cause selects the controllable directions with a finite, explicit weight.

## Proofs

**Theorem 1.** Let s̃ = Σ^{−1/2}s, which has covariance I, and split s̃_t = Uz_t + s̃⊥ with s̃⊥ = (I − UUᵀ)s̃_t, uncorrelated with z_t. Then z_{t+1} = Uᵀ(Ãs̃_t + B̃a_t + w̃_t) = Mz_t + Ga_t + η_t with η_t = UᵀÃs̃⊥ + Uᵀw̃_t. All variables are jointly normal and η_t is uncorrelated with (z_t, a_t), so Mz + Ga is the conditional mean and L(E) = E|η_t|² = tr(UᵀÃ(I − UUᵀ)ÃᵀU) + tr(UᵀQ̃U). The second form follows from Uᵀ(ÃÃᵀ + B̃B̃ᵀ + Q̃)U = I_K. The bound is the extremal property of the trace for the K smallest eigenvalues. For decoupled modes Ã and Q̃ are diagonal and the coordinate subspace of the K smallest qᵢ attains the bound. L(E) = 0 means UᵀQ̃U = 0, that is EQEᵀ = 0 and hence EQ = 0, and (I − UUᵀ)ÃᵀU = 0, which says that the row space Σ^{−1/2} span(U) of E is invariant under Aᵀ.

**Theorem 2.** From BBᵀ ⪯ Q/σ², ‖G‖²_F = tr(UᵀB̃B̃ᵀU) ≤ tr(UᵀQ̃U)/σ² ≤ L(E)/σ². A basis of 𝒱, normalized so that EΣEᵀ = I, gives L(E) = 0 by the last item of Theorem 1. For a minimizer G = 0 and η = 0, so z_{t+1} = Mz_t, and I = Cov(z_{t+1}) = MMᵀ.

**Theorem 3.** (a) Since a_t is uncorrelated with z_t, the best readout uses r = z_{t+1} − Mz_t = Ga_t + η_t, with Cov(r) = I − MMᵀ from Cov(z_{t+1}) = I, and explains tr(Gᵀ Cov(r)^{−1} G). (b) From uᵀ(ÃÃᵀ + B̃B̃ᵀ + Q̃)u = 1 and |Ãᵀu| = 1, B̃ᵀu = 0 and Q̃u = 0. Since ÃÃᵀ ⪯ I, |Ãu − u|² = |Ãu|² − 2uᵀÃu + 1 ≤ 0, so Ãu = u. Hence uᵀÃv = vᵀÃu = 0, M_ε = (1 + ε²vᵀÃv)/(1 + ε²) and 1 − M_ε = ε²(1 − vᵀÃv)/(1 + ε²), G_ε = εB̃ᵀv/√(1 + ε²), and the explained share is |G_ε|²/(1 − M_ε²). The loss is 1 − M_ε² − |G_ε|² = O(ε²). For the difference, z_{t+1} − z_t = (M_ε − 1)z_t + G_εa_t + η_t has the same ratio of the action part to the rest up to the term (M_ε − 1)z_t of variance O(ε⁴). (c) For a scalar mode v = eᵢ, vᵀÃv = αᵢ, |B̃ᵀv|² = bᵢ² and 2(1 − αᵢ) = bᵢ² + qᵢ + (1 − αᵢ)². Carrying mode i on a static latent costs λ(1 − bᵢ²/(bᵢ² + qᵢ + (1 − αᵢ)²)) in the limit; keeping it at full scale costs qᵢ + λ(1 − bᵢ²/(bᵢ² + qᵢ)). With bᵢ² + qᵢ = (1 − αᵢ)(1 + αᵢ) the difference of the two shares is bᵢ²/(2(1 + αᵢ)).

**Theorem 4.** (a) s̃_{t+h} = Ã^{h−1}B̃a_t plus terms uncorrelated with a_t, so Cov(z_{t+h}, a_t) = UᵀÃ^{h−1}B̃. Iterating I = ÃÃᵀ + B̃B̃ᵀ + Q̃ gives I = Ã^H(Ã^H)ᵀ + Σ_{h<H} Ã^h(B̃B̃ᵀ + Q̃)(Ã^h)ᵀ ⪰ W̃_H. (b) is the extremal property of the trace. (c) The displacement is Σ_h UᵀÃ^{H−1−h}B̃a_h, a linear image of the unit ball whose matrix is UᵀW̃_H U. (d) u_εᵀW̃_H u_ε = ε²vᵀW̃_H v/(1 + ε²) since W̃_H u = 0 for a static u; for scalar modes the objective is a sum over the kept modes of qᵢ − μwᵢ, and wᵢ ≥ bᵢ².

## Scope and status

| Result | Scope | Status | Posted |
|---|---|---|---|
| Theorem 1 | Linear world with normal noise, white normal actions independent of the state, injective linear observation, linear encoder with EΣEᵀ = I, any predictor of z_{t+1} from (z_t, a_t) | Claim; checked numerically | 2026-11-24 |
| Theorem 2 | As Theorem 1, with Q ⪰ σ²BBᵀ | Claim; checked numerically | 2026-11-24 |
| Theorem 3 | As Theorem 1; (b) for K = 1 and a static direction; (c) for static and decoupled scalar modes | Claim; checked numerically | 2026-11-24 |
| Theorem 4 | As Theorem 1; (d) for the world of Theorem 3(c) | Claim; checked numerically | 2026-11-24 |

Not covered: nonlinear worlds and encoders, actions chosen by a policy that depends on the state, predictors that see a window of past latents, finite samples and the dynamics of training, and experiments from pixels. With a policy that depends on the state, the covariance in T_H is to be taken after removing from a_t its regression on z_t.

Relation to other work, to our knowledge: linear results with the controllability Gramian for an inverse-dynamics term are in [5], conditions under which the full state and transition are identified at full latent dimension in [9, 10], and a split of the latent into controllable and uncontrollable parts in [11]. The formulas of Theorems 1 to 4 for K below the state dimension, the bound of Theorem 2, the small-component solution of Theorem 3 and the term T_H are, to our knowledge, not in these works.

## Simulations

Scripts in [`sim/`](sim/), run with NumPy, SciPy and PyTorch, with asserts, on one core.

- `population.py`: Theorem 1 on a random world with d = 8, K = 3: the loss of an explicit regression on 400000 simulated steps against both closed forms (within 2 %), and gradient descent on an unconstrained encoder and predictor with a whitening penalty against the maximum of ‖UᵀÃU‖² + ‖UᵀB̃‖² over orthonormal U (0.111 against 0.114).
- `action_blind.py`: Theorem 3(a) against a regression (within 2 %). Three static modes and two scalar modes with actuator noise σ = 0.5: at λ = 0 the minimizer has loss and action response 0 (Theorem 2); for λ on both sides of the thresholds λᵢ = 0.75 and 0.95, the infimum and the action response against Theorem 3(c) (to 3·10⁻⁴).
- `action_covariance.py`: Theorem 4(a) on simulated data (within 3 %), (b) against a numerical maximization (to 10⁻⁵), and (d) on the same world as above with H = 4: thresholds μᵢ = 0.083 and 0.188, value and action response on both sides (to 10⁻⁴).

## References

1. L. Maes, Q. Le Lidec, D. Scieur, Y. LeCun, R. Balestriero. LeWorldModel: stable end-to-end joint-embedding predictive architecture from pixels. arXiv:2603.19312, 2026.
2. R. Balestriero, Y. LeCun. LeJEPA: provable and scalable self-supervised learning without the heuristics. arXiv:2511.08544, 2025.
3. Y. Chen, Q. Hou, J. Jeong, Y. Zhu, H. Jiang, A. Said. Motion-guided contrastive regularization for latent world models. arXiv:2611.06901, 2026.
4. F. Strohm, P. Wagner, J. Schwab, M. Huber. Keeping JEPA world models plannable when little of the frame moves. arXiv:2610.03137, 2026.
5. L. F. Toso, Y. LeCun, J. Anderson, O. Bounou. Preserving unstable modes through inverse dynamics in JEPA world models. arXiv:2610.07540, 2026.
6. P. Ivashkov, R. Balestriero, B. Schölkopf. Sensorimotor world models: perception for action via inverse dynamics. arXiv:2606.20104, 2026.
7. Z. Zhang, Y. Wang, Z. Guan, Y. Yang, B. Shi, T. Zong, H. Yi, G. Chao, X. Chen, T. Yang, C. Bao, T. Yu, J. Zhou, J. Xu. Delta-JEPA: learning action-sensitive world models via latent difference decoding. arXiv:2606.31232, 2026.
8. J. Boylan, C. Hokamp. No Gaussian required: contrastive inverse dynamics for JEPA world models. arXiv:2608.17542, 2026.
9. D. Klindt, Y. LeCun, R. Balestriero. When does LeJEPA learn a world model? arXiv:2605.26379, 2026.
10. X. Zhang, Y. Guan, B. Zhang, H. Li, Y.-Q. Zhang, S. E. Li. On the identifiability of controlled world models. arXiv:2607.22430, 2026.
11. M. Byrd, R. Wright, S. Ha. CF-JEPA: improving robustness of JEPA world models via controllability factorization. arXiv:2610.00727, 2026.

## Use of AI

Claude Fable 5.2 and Claude Opus 5.5 (Anthropic) were used throughout this research: to explore approaches, to develop and check the derivations, to write the simulation scripts, and to draft the text.
