# What a JEPA world model keeps: an exactly solvable linear world

Written 24 Nov 2026.

A JEPA world model such as LeWM [1] trains an encoder and a predictor with two terms: the error of predicting the next latent from the current latent and the action, and a regularizer (SIGReg [2]) that pushes the latents towards the standard normal law. Planning then searches for actions whose predicted latent is close to the latent of a goal. Several recent studies report that such models can lose what planning needs: latents that follow static content of the scene [3], latents that barely respond to the action [4], and lost controllable modes [5]; the remedies add an inverse-dynamics term that reads the action from consecutive latents [4, 5, 6, 7, 8].

This folder solves the objective exactly in a linear world with normal noise, for a latent dimension K below the state dimension. The solution says which directions of the state the prediction objective keeps (Theorem 1), shows that actuator noise makes every near-minimizer blind to the action (Theorem 2), shows that an inverse-dynamics term can be met by a latent whose response to the action is arbitrarily small (Theorem 3), and gives a term, the covariance between future latents and past actions, whose optimum is the top eigenspace of a controllability matrix and which has no such loophole (Theorem 4). This term, like every term with zero derivative at zero action covariance, has zero gradient at an action-blind latent, so gradient descent can stay at such a latent although the minimizer is elsewhere; the unsquared norm of the covariances has no such stationary points (Theorem 5). A small pixel test shows the same three effects with a convolutional encoder, and shows that the inverse-dynamics term together with T_H gives latents that carry the agent. With the code and the TwoRoom task of [1] and a static distractor added to the frames, the two terms together raise the planning success from 31 % to 73 % (mean of three training seeds).

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

(a) T_H(E) = tr(UᵀW̃_H U) with W̃_H = Σ_{h=0}^{H−1} Ã^h B̃B̃ᵀ(Ã^h)ᵀ = Σ^{−1/2}W_HΣ^{−1/2}, where W_H is the H-step controllability matrix, and 0 ⪯ W̃_H ⪯ I. For a unit vector u, uᵀW̃_H u is the share of the variance of the direction u that the last H actions caused.
(b) Over all encoders with EΣEᵀ = I, T_H is maximal exactly on the span of eigenvectors for the K largest eigenvalues of W̃_H, with value their sum.
(c) The latent displacements that action sequences of total energy 1 reach in H steps form the ellipsoid with matrix UᵀW̃_H U. So the maximizers of T_H are the latents in which goals are cheapest to reach.
(d) T_H is quadratic in the scale of an action-dependent component: the latent of Theorem 3(b) has T_H = ε² vᵀW̃_H v/(1 + ε²). In the world of Theorem 3(c) the minimizers of L − μT_H keep mode i exactly when μ > qᵢ/wᵢ with wᵢ = bᵢ²(1 − αᵢ^{2H})/(1 − αᵢ²), which is at most qᵢ/bᵢ², a factor 2(1 + αᵢ) or more below λᵢ.

**Theorem 5 (action-blind latents are stationary).** Call a latent action-blind when Cov(z_{t+h}, a_t) = 0 for h = 1, …, H; by Theorem 4(a) this means W̃_H U = 0.
(a) Let φ be a function of the covariances C_h = Cov(z_{t+h}, a_t), h = 1, …, H, that is differentiable at 0 with zero derivative there, such as T_H. For any encoder that depends differentiably on its parameters, φ has zero gradient at every action-blind encoder. So every action-blind stationary point of L, in particular every minimizer in Theorem 2, is a stationary point of L − μφ for every μ.
(b) In the world of Theorem 3(c), let one column of a static latent turn towards mode i by the angle ε. Then

    L − μT_H = ε²(qᵢ + (1 − αᵢ)² − μwᵢ) + O(ε⁴),

and the second variation under any small perturbation is the sum of such terms over the columns and modes. If μ < (qⱼ + (1 − αⱼ)²)/wⱼ for every mode j, the static latents are local minima of L − μT_H. If in addition μ > qᵢ/wᵢ for some i, they are not global minima (Theorem 4(d)).
(c) Let N_H(E) = Σ_{h=1}^{H} ‖Cov(z_{t+h}, a_t)‖_F, the sum of unsquared norms. If W̃_H ≠ 0, then for every μ > 0 no action-blind encoder is a local minimizer of L − μN_H. With one scalar mode, along the rotation of (b) the objective is f(s) = (qᵢ + (1 − αᵢ)²)s − (1 − αᵢ)²s² − μSᵢ√s, where s = sin²ε and Sᵢ = bᵢ Σ_{h<H} |αᵢ|^h, so its minimizer s* is positive for every μ > 0.

Taken together: the prediction objective ranks directions by how little fresh noise they carry and treats static content as ideal; with noisy actuators it removes the action from the latent; reading the action back restores it only as an arbitrarily small component; a term that measures how much of the latent variance the actions cause selects the controllable directions with a finite, explicit weight; in its squared form it gives no gradient at a latent that is already blind to the action, while the unsquared form does.

## Pixel test

A small world from pixels tests Theorems 1, 3 and 5 beyond the linear setting (script `sim/pixel_toy.py`, CPU).

- **World.** Images of 32 × 32 pixels. The agent is a bump of width 0.05 at a position p ∈ [0, 1]² that moves by p′ = clip(p + 0.08(a + 0.5e)) with a, e ∼ N(0, I₂), so the actuators are noisy. The background is a sum of 6 fixed cosine patterns of total amplitude 0.5, with coefficients drawn once per episode from the uniform law with unit variance, so it is static content within an episode.
- **Model.** A convolutional encoder (three stride-2 layers and two linear layers) to K = 4 latents and an MLP predictor of z_{t+1} from (z_t, a_t). The loss is the squared prediction error plus SIGReg with weight 0.1 (64 slices, 17 knots on [0, 3], the statistic scaled by the batch size as in the code of [1]). Training runs 3000 steps of Adam (learning rate 10⁻³) on batches of 64 episodes of 6 steps.
- **Variants.** LeWM (prediction and SIGReg); inverse dynamics (plus the squared error of an MLP that reads a_t from (z_t, z_{t+1}), weight 1); inverse dynamics and T_H (plus −μT_H with μ = 10 and H = 3, computed on batch-whitened latents so that Cov(z) = I as in Theorem 4); and, as a reference, a supervised linear readout of p from z with weight 10, which shows what a latent that carries the agent gives.
- **Measures.** R² of a linear probe of the agent position and of the background coefficients from z (2000 frames, half for fitting). The action response, the variance over 64 random actions of the predicted next latent, summed over coordinates. Goal reaching by random-shooting control: 256 candidate sequences of 5 actions, replanned at each of 25 steps, with the squared latent distance to the image of the goal (same background) as cost. The mean start distance is 0.53, and an episode succeeds when the final distance is below 0.1 (100 episodes).

Three seeds, mean ± standard deviation:

| Variant | Position R² | Background R² | Action response | Success | Final distance |
|---|---|---|---|---|---|
| LeWM | 0.00 ± 0.00 | 0.60 ± 0.08 | 0.001 ± 0.000 | 1.3 ± 1.5 % | 0.60 ± 0.06 |
| Inverse dynamics | 0.01 ± 0.01 | 0.58 ± 0.11 | 0.002 ± 0.001 | 5.0 ± 1.0 % | 0.48 ± 0.05 |
| Inverse dynamics and T_H | 0.57 ± 0.42 | 0.41 ± 0.18 | 0.096 ± 0.075 | 17.0 ± 3.6 % | 0.30 ± 0.10 |
| Position readout (reference) | 0.98 ± 0.01 | 0.31 ± 0.01 | 0.114 ± 0.014 | 22.7 ± 6.7 % | 0.18 ± 0.01 |

LeWM keeps the background and ignores the agent, as Theorems 1 and 2 predict for static content and noisy actuators. Inverse dynamics raises the action response only to 0.002, against 0.11 for a latent that carries the agent: the small-component solution of Theorem 3. With T_H added, the agent position becomes linearly readable in two of the three seeds (R² 0.78 and 0.84, and 0.08 in the third) and goal reaching rises from 5 % to 17 %. With the term T_H alone (μ = 1 and μ = 10, seed 0) the latent stays action-blind (action response 0.001), in line with Theorem 5(a): the inverse-dynamics term supplies a small action component, and T_H, whose gradient grows with that component, enlarges it.

## Test with the code of [1]

The two terms were added to the training code released with [1] (commit 8edfeb3, imported unchanged by the wrapper in [`lewm/`](lewm/)) and tested on its TwoRoom task, with a static distractor added to the frames.

- **Task and evaluation.** TwoRoom with the dataset of [1] (10000 episodes, 920809 frames) and the planning evaluation of [1]: the cross-entropy method with 300 samples and 30 iterations, horizon 5, receding horizon 5, a budget of 50 steps, and 50 episodes that start from dataset states with the goal 25 steps ahead (evaluation seed 42, so the episodes are the same for every variant).
- **Distractor.** Every frame of an episode gets the same smooth colour pattern, added after the normalization of the images: 6 fixed cosine patterns, with coefficients per colour channel drawn once per episode from the uniform law with unit variance (18 static factors), scaled to amplitude 1 in normalized pixel units, which gives a standard deviation of about 0.8 per pixel (`lewm/distract.py`). Training and evaluation episodes draw their patterns from the same law with disjoint seeds, and the goal image of an episode carries the pattern of that episode.
- **Scale.** Images of 64 × 64 pixels (patch size 8), batch 64, 4000 training steps, training seeds 3072 (the default of [1]), 1 and 2, on one laptop GPU. All other settings are those of [1]: a ViT-tiny encoder, latent dimension 192, history 3, SIGReg with weight 0.09 and 1024 slices, AdamW with learning rate 5·10⁻⁵ and the warmup and cosine schedule.
- **Variants.** LeWM; inverse dynamics (an MLP reads the action block a_t from (z_t, z_{t+1}), squared error, weight 1); inverse dynamics and T, with weight μ = 0.1. Here T = Σ_{h=1}^{3} tr(C_hᵀ(Σ_z + λI)⁻¹C_h), with C_h = Cov(z_{t+h}, a_t) and Σ_z = Cov(z) estimated on the batch, and λ the mean latent variance, held fixed in the gradient. This ridge form departs from the exact whitening of Theorem 4: with 192 latent coordinates and a few hundred frames per batch, exact whitening fits chance correlations. At Cov(z) = I the ridge form equals T_H/2. The weight μ = 0.1 was set before any evaluation, from the size of T against the prediction loss, and was not tuned.

Planning success on the 50 evaluation episodes, per training seed, and over the three seeds the mean ± standard deviation and the 95 % score interval for a binomial proportion on the pooled 150 episodes (rounded outwards):

| Variant | Seed 3072 | Seed 1 | Seed 2 | Mean ± sd | Pooled interval | TwoRoom without distractor |
|---|---|---|---|---|---|---|
| LeWM | 34 % | 26 % | 34 % | 31.3 ± 4.6 % | 24 to 40 % | 100 % (seed 3072) |
| Inverse dynamics | 40 % | | | | | |
| Inverse dynamics and T | 74 % | 70 % | 74 % | 72.7 ± 2.3 % | 65 to 80 % | |

The clean task is solved by LeWM at this scale, and the distractor lowers its success to about 31 %. Its prediction loss at the end of training is about 0.004 with the distractor against 0.024 without it, in line with Theorem 1: the static pattern is the easiest content to predict. Inverse dynamics alone gives 40 % (seed 3072), and its readout explains only about 2 % of the action variance (squared error 0.98 for normalized actions), the small-component solution of Theorem 3. Inverse dynamics and T give about 73 %, and the lowest seed of this variant (70 %) lies above the highest seed of LeWM (34 %). The three seeds share the same evaluation episodes, so the pooled interval treats the 150 runs as independent and is narrower than an interval over new episodes would be.

## Proofs

**Theorem 1.** Let s̃ = Σ^{−1/2}s, which has covariance I, and split s̃_t = Uz_t + s̃⊥ with s̃⊥ = (I − UUᵀ)s̃_t, uncorrelated with z_t. Then z_{t+1} = Uᵀ(Ãs̃_t + B̃a_t + w̃_t) = Mz_t + Ga_t + η_t with η_t = UᵀÃs̃⊥ + Uᵀw̃_t. All variables are jointly normal and η_t is uncorrelated with (z_t, a_t), so Mz + Ga is the conditional mean and L(E) = E|η_t|² = tr(UᵀÃ(I − UUᵀ)ÃᵀU) + tr(UᵀQ̃U). The second form follows from Uᵀ(ÃÃᵀ + B̃B̃ᵀ + Q̃)U = I_K. The bound is the extremal property of the trace for the K smallest eigenvalues. For decoupled modes Ã and Q̃ are diagonal and the coordinate subspace of the K smallest qᵢ attains the bound. L(E) = 0 means UᵀQ̃U = 0, that is EQEᵀ = 0 and hence EQ = 0, and (I − UUᵀ)ÃᵀU = 0, which says that the row space Σ^{−1/2} span(U) of E is invariant under Aᵀ.

**Theorem 2.** From BBᵀ ⪯ Q/σ², ‖G‖²_F = tr(UᵀB̃B̃ᵀU) ≤ tr(UᵀQ̃U)/σ² ≤ L(E)/σ². A basis of 𝒱, normalized so that EΣEᵀ = I, gives L(E) = 0 by the last item of Theorem 1. For a minimizer G = 0 and η = 0, so z_{t+1} = Mz_t, and I = Cov(z_{t+1}) = MMᵀ.

**Theorem 3.** (a) Since a_t is uncorrelated with z_t, the best readout uses r = z_{t+1} − Mz_t = Ga_t + η_t, with Cov(r) = I − MMᵀ from Cov(z_{t+1}) = I, and explains tr(Gᵀ Cov(r)^{−1} G). (b) From uᵀ(ÃÃᵀ + B̃B̃ᵀ + Q̃)u = 1 and |Ãᵀu| = 1, B̃ᵀu = 0 and Q̃u = 0. Since ÃÃᵀ ⪯ I, |Ãu − u|² = |Ãu|² − 2uᵀÃu + 1 ≤ 0, so Ãu = u. Hence uᵀÃv = vᵀÃu = 0, M_ε = (1 + ε²vᵀÃv)/(1 + ε²) and 1 − M_ε = ε²(1 − vᵀÃv)/(1 + ε²), G_ε = εB̃ᵀv/√(1 + ε²), and the explained share is |G_ε|²/(1 − M_ε²). The loss is 1 − M_ε² − |G_ε|² = O(ε²). For the difference, z_{t+1} − z_t = (M_ε − 1)z_t + G_εa_t + η_t has the same ratio of the action part to the rest up to the term (M_ε − 1)z_t of variance O(ε⁴). (c) For a scalar mode v = eᵢ, vᵀÃv = αᵢ, |B̃ᵀv|² = bᵢ² and 2(1 − αᵢ) = bᵢ² + qᵢ + (1 − αᵢ)². Carrying mode i on a static latent costs λ(1 − bᵢ²/(bᵢ² + qᵢ + (1 − αᵢ)²)) in the limit; keeping it at full scale costs qᵢ + λ(1 − bᵢ²/(bᵢ² + qᵢ)). With bᵢ² + qᵢ = (1 − αᵢ)(1 + αᵢ) the difference of the two shares is bᵢ²/(2(1 + αᵢ)).

**Theorem 4.** (a) s̃_{t+h} = Ã^{h−1}B̃a_t plus terms uncorrelated with a_t, so Cov(z_{t+h}, a_t) = UᵀÃ^{h−1}B̃. Iterating I = ÃÃᵀ + B̃B̃ᵀ + Q̃ gives I = Ã^H(Ã^H)ᵀ + Σ_{h<H} Ã^h(B̃B̃ᵀ + Q̃)(Ã^h)ᵀ ⪰ W̃_H. (b) is the extremal property of the trace. (c) The displacement is Σ_h UᵀÃ^{H−1−h}B̃a_h, a linear image of the unit ball whose matrix is UᵀW̃_H U. (d) u_εᵀW̃_H u_ε = ε²vᵀW̃_H v/(1 + ε²) since W̃_H u = 0 for a static u; for scalar modes the objective is a sum over the kept modes of qᵢ − μwᵢ, and wᵢ ≥ bᵢ².

**Theorem 5.** (a) The gradient of φ(C(θ)) is Dφ(C(θ)) applied to the derivative of C(θ), and Dφ(0) = 0. (b) With the column u = cos ε v + sin ε eᵢ, the matching diagonal entry of M is cos²ε + αᵢ sin²ε and the matching row of G is sin ε bᵢ, so with s = sin²ε, L = 2(1 − αᵢ)s − (1 − αᵢ)²s² − bᵢ²s and T_H = wᵢs, and 2(1 − αᵢ) − bᵢ² = qᵢ + (1 − αᵢ)². Under a general small perturbation X of the columns the off-diagonal entries of M and G change at order |X|², so they enter L at order |X|⁴. (c) For v ≠ 0 in the range of W̃_H, W̃_H U = 0 gives v ⟂ span(U). Turning one column of U towards v/|v| by ε makes C_h = sin ε · eₖ(v/|v|)ᵀÃ^{h−1}B̃, and these rows do not all vanish since vᵀW̃_H v > 0. So the objective is L(U) + εℓ − μ|ε|n + O(ε²) with n > 0, and one sign of ε lowers it. The formula for f follows from the computation in (b), with Σ_h ‖C_h‖_F = √s Sᵢ.

## Scope and status

| Result | Scope | Status | Posted |
|---|---|---|---|
| Theorem 1 | Linear world with normal noise, white normal actions independent of the state, injective linear observation, linear encoder with EΣEᵀ = I, any predictor of z_{t+1} from (z_t, a_t) | Claim; checked numerically | 2026-11-24 |
| Theorem 2 | As Theorem 1, with Q ⪰ σ²BBᵀ | Claim; checked numerically | 2026-11-24 |
| Theorem 3 | As Theorem 1; (b) for K = 1 and a static direction; (c) for static and decoupled scalar modes | Claim; checked numerically | 2026-11-24 |
| Theorem 4 | As Theorem 1; (d) for the world of Theorem 3(c) | Claim; checked numerically | 2026-11-24 |
| Theorem 5 | (a) any differentiable encoder, population or batch covariances; (b) the world of Theorem 3(c); (c) as Theorem 1, the formula for one scalar mode | Claim; checked numerically | 2026-11-24 |
| Pixel test | The world above, K = 4, 3 seeds, 3000 steps; not the architecture or the tasks of [1] | Numerical only | 2026-11-25 |
| Test with the code of [1] | TwoRoom of [1] with the static distractor above, 64 × 64 pixels, 4000 steps, three training seeds, 50 evaluation episodes | Numerical only | 2026-11-25 |

Not covered: nonlinear worlds and encoders, actions chosen by a policy that depends on the state, predictors that see a window of past latents, finite samples and the dynamics of training, and experiments beyond the two tests above, in particular other tasks of [1], other distractors and full image size. With a policy that depends on the state, the covariance in T_H is to be taken after removing from a_t its regression on z_t.

Relation to other work, to our knowledge: linear results with the controllability matrix for an inverse-dynamics term are in [5], conditions under which the full state and transition are identified at full latent dimension in [9, 10], and a split of the latent into controllable and uncontrollable parts in [11]. The formulas of Theorems 1 to 4 for K below the state dimension, the bound of Theorem 2, the small-component solution of Theorem 3, the term T_H and the stationarity of Theorem 5 are, to our knowledge, not in these works.

## Simulations

Scripts in [`sim/`](sim/), run with NumPy, SciPy and PyTorch, with asserts, on one core; the folder [`lewm/`](lewm/) runs with the code of [1] and stable-worldmodel 0.1.1 on a laptop GPU.

- `population.py`: Theorem 1 on a random world with d = 8, K = 3: the loss of an explicit regression on 400000 simulated steps against both closed forms (within 2 %), and gradient descent on an unconstrained encoder and predictor with a whitening penalty against the maximum of ‖UᵀÃU‖² + ‖UᵀB̃‖² over orthonormal U (0.111 against 0.114).
- `action_blind.py`: Theorem 3(a) against a regression (within 2 %). Three static modes and two scalar modes with actuator noise σ = 0.5: at λ = 0 the minimizer has loss and action response 0 (Theorem 2); for λ on both sides of the thresholds λᵢ = 0.75 and 0.95, the infimum and the action response against Theorem 3(c) (to 3·10⁻⁴).
- `action_covariance.py`: Theorem 4(a) on simulated data (within 3 %), (b) against a numerical maximization (to 10⁻⁵), and (d) on the same world as above with H = 4: thresholds μᵢ = 0.083 and 0.188, value and action response on both sides (to 10⁻⁴).
- `saddle.py`: Theorem 5 on the same world: the gradient on the manifold of orthonormal frames at the static latent is 0 for μ = 0.1, 1 and 10; the second variation along each mode matches qᵢ + (1 − αᵢ)² − μwᵢ (local thresholds 0.105 and 0.502); at μ = 0.094, between the global and the local threshold of mode 0, 300 random small perturbations of the static latent raise the objective, while keeping mode 0 lowers it below 0. For the unsquared term with one scalar mode the minimum over frames matches min f and the action response b²s* for μ = 0.002, 0.01, 0.05 and 0.5 (s* = 0.0008, 0.020, 1, 1).
- [`lewm/`](lewm/): the test with the code of [1]. `train_b2.py` adds the two terms to the training code of [1] (options `+b2.lam_inv` and `+b2.mu`), `distract.py` adds the distractor in training and evaluation (`B2_DISTRACT=1.0`), `eval_b2.py` runs the planning evaluation of [1], `run.sh` trains and evaluates one variant (about 45 minutes on a laptop GPU), and `results.jsonl` holds the success counts of the table.
- `pixel_toy.py`, `run_pixel.sh`, `pixel_table.py`, `pixel_runs.jsonl`: the pixel test. `run_pixel.sh` runs the 12 runs of the table and the 2 runs with T_H alone (about 4 minutes each on 2 CPU threads), and `pixel_table.py` prints the table from the results.

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
