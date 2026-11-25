# Weight-space programming of spiking networks: working-memory benchmarks without training

Written 24 Nov 2026.

## Result

Weight-space programming writes the weights of a network directly, as a readable circuit, instead of training
them [2]. This folder applies it to recurrent networks of spiking neurons. The benchmarks are the three
working-memory tasks of [1]: one-dimensional STORE-RECALL, 20-dimensional STORE-RECALL and 12AX. Tasks, neuron
model and readout are ported from the reference code of [1] and kept as they are there: leaky integrate-and-fire
(LIF) neurons with a 20 ms membrane time constant, a 1 ms time step, 1 ms synaptic delay, a refractory period,
no self-connections, Poisson input spikes and a linear readout.

All circuits below use plain LIF neurons, with no spike-frequency adaptation and no training. Each row is
measured on sequences from seeds that were not used to choose the weights.

| Task | Previous best result [1] | Trained plain LIF [1] | Programmed plain-LIF circuit |
|---|---|---|---|
| 12AX, episodes of 90 symbols solved without any wrong output | 97.79 % ± 0.42, 200 neurons (100 with adaptation), 10,000 training iterations | 0.39 %, 200 neurons | 10,000 of 10,000 episodes, 25 neurons |
| 20-dimensional STORE-RECALL, recalls with all 20 bits right | 99.09 % ± 0.17, 500 neurons with adaptation, about 3,600 training iterations | 0 %, 500 neurons | 6,817 of 6,817 recalls, 81 neurons |
| One-dimensional STORE-RECALL, nominal delay 16 s | 97.1 %, 60 neurons with adaptation, 400 training iterations | 51 %, 60 neurons | 11,903 of 11,903 recalls, 5 neurons |

The one-dimensional task at all five delay settings of Table 1 of [1]:

| Nominal delay | 200 ms | 2 s | 4 s | 8 s | 16 s |
|---|---|---|---|---|---|
| Trained LIF, 60 neurons [1] | 96.7 | 51 | 50 | 49 | 51 |
| Best trained network with adaptation, 60 neurons [1] | 99.92 | 99.9 | 99.7 | 97.8 | 97.1 |
| Programmed circuit, 5 LIF neurons | 99.97 | 100 | 100 | 100 | 100 |
| Wrong recalls / recalls, programmed circuit | 4 / 12,315 | 0 / 11,965 | 0 / 12,603 | 0 / 13,001 | 0 / 11,903 |

A two-neuron solution of the one-dimensional task with hand-set weights and adaptive neurons is shown in
[1, Figure 1D, E]. The circuits here use neurons without adaptation, and cover the two larger tasks.

## The circuits

Weights are given in units of the firing threshold. Every circuit is built from four parts.

- **Detector with veto.** A neuron driven by one input group and inhibited more strongly by another fires only
  when the first group is active and the second is silent. With the complementary value groups of the tasks
  this gives "STORE and value 1" and "STORE and value 0" without relying on a narrow threshold between one and
  two noisy inputs.
- **Latch.** Two neurons that excite each other keep firing in alternation once one of them is started, for any
  length of time, and stop when both are inhibited. This is the memory. It replaces the slow adaptation variable
  of [1], and it needs no self-connection.
- **Gate.** A neuron that receives two regular spike trains with a weight below threshold for one train and
  above threshold for both fires only when both are present.
- **Timer.** A chain of latches in which each stage charges the next one slowly, about 60 ms per stage.

**One-dimensional STORE-RECALL, 5 neurons** (`sim/sr_circuit.py`). A set detector (STORE without value 0) switches
the latch on, a reset detector (STORE without value 1) switches it off, and a fifth neuron fires at RECALL when
the latch is off. The readout takes the latch as "1" and the fifth neuron as "0". Five weight values.

**20-dimensional STORE-RECALL, 81 neurons** (`sim/sr20.py`). The same set detector, reset detector and latch for
each of the 20 bits, and one relay neuron for RECALL that serves as the reference level of the bias-free readout.

**12AX, 25 neurons** (`sim/twelve_ax.py`). The target of the task is a small state machine: answer R at an X
that follows 1 ... A ..., or at a Y that follows 2 ... B ..., where a digit clears the letter and an X or Y
clears it as well.
- Six relay neurons, one per relevant symbol, turn the Poisson input into regular spike trains and ignore the
  2 Hz background.
- Two latches hold the context (last digit 1 or 2).
- Two latches are armed by a gate: A in context 1, and B in context 2. Digits and the other letter clear them.
- Two answer neurons are gates of an armed latch with the X or Y relay. The readout counts their spikes.
- Two X in a row arrive as one uninterrupted input stream, so the circuit needs a clock to answer only the first.
  A timer of four latches and one output neuron starts with X or Y and clears the armed latches about 230 ms
  later, inside the 500 ms window.

Seven weight values.

## Measurements

| Script | What it runs |
|---|---|
| `sim/sr_protocol.py` | port of the one-dimensional task, the LIF network and the readout |
| `sim/sr_circuit.py` | the 5-neuron circuit on the five settings of Table 1 of [1] |
| `sim/sr20.py` | port of the 20-dimensional task and the 81-neuron circuit |
| `sim/twelve_ax.py` | port of 12AX and the 25-neuron circuit |
| `sim/sr_train.py` | 60 LIF neurons trained with backpropagation through time in the setting of [1] |
| `sim/sr_finetune.py` | the same training, started from the programmed circuit with weight noise |

- One-dimensional task: seeds 1 to 5, 2,048 sequences per seed and setting. The weights were chosen on separate
  seeds, in the settings 200 ms and 2 s only.
- 20-dimensional task: seeds 1 to 3, 2,048 sequences each, test words from a fresh dictionary of 20 words per
  seed. The result is the same with the value inputs silent during RECALL, as described in [1], and with values
  shown during RECALL.
- 12AX: seeds 1 to 5, 2,000 episodes each, as many per seed as the test of [1].
- Trained LIF network of `sim/sr_train.py`: 98.5, 98.3 and 97.1 % at 200 ms for seeds 0 to 2 (96.7 % in [1]);
  50.3, 49.1 and 49.4 % at 2 s (51 % in [1]); 50.5 % at 4 s for seed 0 (50 % in [1]).
- Mean firing rate per neuron: 35 to 48 Hz (one-dimensional), 27 Hz (20-dimensional), 29 Hz (12AX). A latch
  that is on fires at the highest rate the refractory period allows, 250 Hz in the STORE-RECALL tasks and
  167 Hz in 12AX.

Outputs are in `sim/results/`.

## Training from the programmed circuit

`sim/sr_finetune.py` writes the 5-neuron circuit into a network of 60 LIF neurons, adds Gaussian noise to all
input and recurrent weights, and trains it like the network of `sim/sr_train.py`: one-dimensional STORE-RECALL
at the 2 s setting, 400 iterations, batch 64. The noise level is given in units of the standard deviation of
the random initialization. Test accuracy in %, seeds 0, 1, 2:

| Start | Before training | After, learning rate 0.001 | After, learning rate 0.01 |
|---|---|---|---|
| Random initialization | 50 | – | 50.5, 49.4, 49.0 |
| Programmed, no noise | 100, 100, 100 | 99.7, 99.3, 99.1 | 100, 97.2, 53.0 |
| Programmed, noise 0.15 | 66.1, 54.5, 65.5 | 100, 51.6, 57.0 | 99.6, 90.3, 49.0 |
| Programmed, noise 0.2 | 56.1, 49.3, 50.8 | 100, 50.2, 97.4 | 99.2, 57.5, 48.0 |

These runs use no rate regularization. With the rate regularization of [1], which pulls every neuron towards
10 Hz, training switches the latch off and the accuracy falls from 100 to 50.5, 52.2 and 50.1 % (no noise,
learning rate 0.01): a latch that is on fires at 250 Hz.

So the programmed circuit is kept by gradient training at the small learning rate, at the same size and
number of iterations at which training from a random initialization stays at chance. Repair of a noisy
circuit depends on the seed.

## Lean

`lean/SpikingCircuits/TwelveAX.lean` (Lean 4, core library only, no axioms; `lean/axioms.txt`).

- `target`: the target function of 12AX, with the last digit and the last relevant letter as state.
- `machine`: the state machine that the 12AX circuit implements, with four flags: context 1, context 2,
  armed for X, armed for Y.
- `machine_eq_target`: both give the same outputs on every symbol sequence.

Not formalized: the spiking dynamics. That the latches, gates and the timer realize the four flags under Poisson
input is covered by the measurements only.

## Scope and limits

- The weights are written by hand for each task. Nothing here is learned, and the comparison says nothing
  about learning rules, which are the subject of [1].
- The tasks have small finite state, so circuits of this kind exist in principle. What is measured is their
  size and their accuracy under the Poisson input noise of the benchmark.
- The accuracies are measured on the stated numbers of random sequences. The Lean file covers the logic of the
  12AX state machine, not the spiking dynamics.
- The delay labels are the nominal settings of [1]. Sequences are cut at their fixed length, so the delays that
  occur are shorter: the mean distance from STORE to RECALL is about 0.2, 1.4, 2.5, 4.6 and 7.3 s in the five
  settings. The generator is the one of [1], so the rows are comparable.
- The trained network of `sim/sr_train.py` starts every batch from a zero state, while the reference code carries
  the state over between training batches.
- Composable hand-built spiking circuits are an established idea, for example in [3]. The contribution here is
  the measurement on these benchmarks.

## References

1. D. Salaj, A. Subramoney, C. Kraišniković, G. Bellec, R. Legenstein, W. Maass. Spike frequency adaptation
   supports network computations on temporally dispersed information. eLife 10:e65459, 2021. Reference code:
   github.com/IGITUGraz/Spike-Frequency-Adaptation-Supports-Network-Computations (MIT licence).
2. Interpretable weight-space programming builds transparent transformers and brain encoding models.
   arXiv:2611.18114, 2026.
3. J. B. Aimone, W. Severa, C. M. Vineyard. Composing neural algorithms with Fugu. arXiv:1905.12130, 2019.
