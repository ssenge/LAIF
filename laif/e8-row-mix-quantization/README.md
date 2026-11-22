# Lattice and scalar codes per output row under one Fisher slope, 2-bit weights of Qwen2.5-0.5B, Qwen2.5-1.5B and TinyLlama-1.1B

_21 November 2026_

Post-training quantization of the decoder weights of Qwen2.5-0.5B and Qwen2.5-1.5B [9] to 2.0 to 2.5 bits per weight, without fine-tuning. Each output row of every linear layer takes either the E8P lattice code of [2] at 2 bits per weight or a scalar GPTQ code [1] at 2, 3 or 4 bits, and one global slope trades the Fisher-weighted error against the bits of the row.

## Result

On WikiText-2 [10] (test split, 2048-token windows, all windows), the mix reaches perplexity 20.31 at 2.17 bits per weight and 18.16 at 2.36. GPTQ and AutoRound [3], both run here with the same protocol and the same bit count, reach 34.12 and 29.71 at 2.25 bits per weight and 27.04 and 24.94 at 2.50.

| Method | Bits per weight | Perplexity |
|---|---|---|
| 16-bit weights | 16 | 13.07 |
| GPTQ, 2 bits, groups of 128 [1] | 2.253 | 34.12 |
| GPTQ, 2 bits, groups of 64 [1] | 2.504 | 27.04 |
| AutoRound, 2 bits, groups of 128 [3] | 2.250 | 29.71 |
| AutoRound, 2 bits, groups of 64 [3] | 2.500 | 24.94 |
| E8P rows only, our reimplementation of the code of [2] without fine-tuning, one scale per row, input rotation only | 2.014 | 30.10 |
| Same slope, scalar options only (2 to 4 bits, per-layer level grid) | 2.472 | 19.53 |
| **Mix of E8P and scalar rows** | **2.041** | **26.23** |
| **Mix of E8P and scalar rows** | **2.173** | **20.31** |
| **Mix of E8P and scalar rows** | **2.362** | **18.16** |

At 2.17 bits per weight the mix is 32% below AutoRound at 2.25 in perplexity, and at 2.36 it is 27% below AutoRound at 2.50.

On Qwen2.5-1.5B, with the same protocol and sequential calibration (the H of each layer is taken from the outputs of the layers already quantized):

| Method | Bits per weight | Perplexity |
|---|---|---|
| 16-bit weights | 16 | 9.26 |
| GPTQ, 2 bits, groups of 128 [1] | 2.252 | 18.98 |
| GPTQ, 2 bits, groups of 64 [1] | 2.503 | 16.41 |
| AutoRound, 2 bits, groups of 64 [3] | 2.500 | 15.45 |
| Same slope, scalar options only (2 to 4 bits) | 2.466 | 13.84 |
| **Mix of E8P and scalar rows** | **2.014** | **15.67** |
| **Mix of E8P and scalar rows** | **2.227** | **12.91** |
| **Mix of E8P and scalar rows** | **2.459** | **11.93** |

At 2.23 bits per weight the mix is 32% below GPTQ at 2.25, and at 2.46 it is 27% below GPTQ at 2.50, 23% below AutoRound at 2.50 and 14% below the scalar-only allocation at 2.47.

On TinyLlama-1.1B-Chat [12], with the same protocol, next to the released 2-bit AQLM checkpoint of this model [11] (one codebook of 2^16 entries per layer for groups of 8 inputs, with fine-tuning). AQLM takes 2.0 bits per weight for the codes and 3.34 including the per-layer codebooks, which weigh more at 1.1B parameters. Its decoded weights are evaluated on our perplexity path.

| Method | Bits per weight | Perplexity |
|---|---|---|
| 16-bit weights | 16 | 7.97 |
| GPTQ, 2 bits, groups of 128 [1] | 2.252 | 14.44 |
| GPTQ, 2 bits, groups of 64 [1] | 2.502 | 12.98 |
| GPTQ, 3 bits, groups of 128 [1] | 3.252 | 8.71 |
| AQLM, released checkpoint [11] | 2.0 (codes), 3.34 (with codebooks) | 10.74 |
| **Mix of E8P and scalar rows** | **2.011** | **12.53** |
| **Mix of E8P and scalar rows** | **2.226** | **10.72** |
| **Mix of E8P and scalar rows** | **2.484** | **9.78** |
| **Mix of E8P and scalar rows** | **3.297** | **8.49** |
| **Mix of E8P and scalar rows** | **3.498** | **8.36** |
| **Mix of E8P and scalar rows** | **3.774** | **8.23** |

## Method

For a linear layer with weight W (o rows, i inputs), input second moment H from calibration and diagonal empirical Fisher F of the language-model loss:

- All options share one input rotation, a block Hadamard transform with random signs, which costs no stored bits. There is no output rotation, so the rows stay independent.
- Scalar options: GPTQ with activation order, a clipped scale search and a least-squares refit of the group scales and zero points after rounding (as in [7], [8]), at 2, 3 and 4 bits, with a 16-bit scale and zero point per group of 128 inputs.
- Lattice option: the rows are divided by their root mean square, rounded to the E8P codebook of [2] (2^16 points of E8 + 1/4, 2 bits per weight) by block LDL rounding of 8 columns with error feedback through H, and stored with one 16-bit scale per row.
- Allocation: row r takes the option q that minimizes Σ_j F_rj (W_rj − Q_rj)² + λ · bits_q, with one λ for the whole model. A per-layer form of mixed quantizers is in [4], Fisher-based bit allocation inside vector quantization in [5], and global mixed precision over output features in [6]; here the options of one row are lattice and scalar codes together.

All bits of the decoder linear layers are counted: codes, scales, zero points, the per-row option tag (2 bits) and, where used, the per-layer level grids. The embedding and the tied output head stay at 16 bits and are not part of the count, for every row of the table.

Calibration: 32 windows of 512 tokens from the WikiText-2 training split for H and F. The rows of the first token in each window get weight 3 in the H of the value projections. AutoRound uses its default settings (200 iterations, 128 windows of 2048 tokens from the same split, asymmetric, version 0.16.1), with the same bit count as GPTQ: 2 bits plus a 16-bit scale and zero point per group.

Scope:

- Three models, Qwen2.5-0.5B, Qwen2.5-1.5B and TinyLlama-1.1B-Chat; perplexity on WikiText-2 only. AutoRound is run with groups of 128 and 64 on Qwen2.5-0.5B and with groups of 64 on Qwen2.5-1.5B.
- Without fine-tuning. Among methods that fine-tune after quantization, only the released AQLM checkpoint of TinyLlama-1.1B-Chat is part of the comparison.
- λ is set from a sample of 5 decoder layers, so the reached bits per weight lie somewhat below the targets 2.25 and 2.5.

## Files

- `nnc/compress.py`: `gmix` (the allocation; `e8=1` adds the lattice option), `gptq`, `quip` (E8P code with block LDL rounding), `e8p_nearest` (exact nearest E8P point).
- `nnc/pipeline.py`, `nnc/models.py`, `nnc/fisher.py`: calibration, Fisher diagonal, perplexity.
- `sim/test_gmix_e8.py`: asserts that every row takes the Lagrangian optimum, that the bits are counted exactly, and that the mix is never worse in the Lagrangian than the scalar-only mix.
- `sim/test_quip.py`: asserts on the E8P codebook and its nearest-point search against brute force.
- `sim/lam_pilot.py`: λ for a target bits per weight.
- `sim/autoround_run.py`: the AutoRound baseline on the same protocol.
- `sim/aqlm_eval.py`: decodes the released AQLM checkpoint (safetensors) to dense weights, with an assert against the aqlm kernel, and counts its bits.
- `results/qwen05_2048.jsonl`, `results/qwen15_2048.jsonl`, `results/tinyllama_2048.jsonl`: the rows of the tables.

Run: `python -m nnc.fisher qwen05`, then `python -m nnc.pipeline --model qwen05 --evlen 2048 --sink 3.0 0.0 --out out.jsonl --specs gmix:lam=2.291e-05,refit=1,e8=1`.

## References

1. E. Frantar, S. Ashkboos, T. Hoefler, D. Alistarh. GPTQ: Accurate post-training quantization for generative pre-trained transformers. ICLR 2023. arXiv:2210.17323.
2. A. Tseng, J. Chee, Q. Sun, V. Kuleshov, C. De Sa. QuIP#: Even better LLM quantization with Hadamard incoherence and lattice codebooks. ICML 2024. arXiv:2402.04396.
3. W. Cheng, W. Zhang, H. Shen, Y. Cai, X. He, K. Lv, Y. Liu. Optimize weight rounding via signed gradient descent for the quantization of LLMs. arXiv:2309.05516.
4. D. Lee, H. O. Song. Q-Palette: Fractional-bit quantizers toward optimal bit allocation for efficient LLM deployment. arXiv:2509.20214.
5. Z. Xu, X. Hu, Q. Wu, D. Yang. RSAVQ: Riemannian sensitivity-aware vector quantization for large language models. arXiv:2510.01240.
6. Z. Zheng, X. Song, C. Liu. MixLLM: LLM quantization with global mixed-precision between output-features and highly-efficient system design. arXiv:2412.14590.
7. X. Wang, S. Lyu, X.-W. Chang. JARQ: Joint alternating refinement for quantization. arXiv:2609.38599.
8. G. Lee, S. Son, Y. Lee, B. Kim, J. H. Ahn. SchurQuant: Groupwise discrete optimization for layer-wise LLM quantization. arXiv:2608.15567.
9. Qwen Team. Qwen2.5 technical report. arXiv:2412.15115.
10. S. Merity, C. Xiong, J. Bradbury, R. Socher. Pointer sentinel mixture models. ICLR 2017. arXiv:1609.07843.
11. V. Egiazarian, A. Panferov, D. Kuznedelev, E. Frantar, A. Babenko, D. Alistarh. Extreme compression of large language models via additive quantization. ICML 2024. arXiv:2401.06118.
12. P. Zhang, G. Zeng, T. Wang, W. Lu. TinyLlama: An open-source small language model. arXiv:2401.02385.
