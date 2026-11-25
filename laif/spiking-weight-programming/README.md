# Weight-space programming of spiking networks: working-memory benchmarks without training

Written 24 Nov 2026.

## Result

Weight-space programming writes the weights of a network directly, as a readable circuit, instead of training
them [2]. This folder applies it to recurrent networks of spiking neurons. The first three benchmarks are the
working-memory tasks of [1]: one-dimensional STORE-RECALL, 20-dimensional STORE-RECALL and 12AX. Tasks, neuron
model and readout are ported from the reference code of [1] and kept as they are there: leaky integrate-and-fire
(LIF) neurons with a 20 ms membrane time constant, a 1 ms time step, 1 ms synaptic delay, a refractory period,
no self-connections, random input spikes at fixed rates and a linear readout.

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

A fourth benchmark is the AL task (autonomous localization) of [4]: decide from 400 action commands whether a
robot ends on the right half-plane. Here the network has the shape of the benchmark's recurrent LIF model,
3-128-176-176-2, and the input is noise-free.

| Task | Previous best result [4] | Trained LIF [4] | Programmed LIF network |
|---|---|---|---|
| AL, sequence length 400, test accuracy | 87.42 % (PMSN neurons) | 54.40 % feedforward, 56.50 % recurrent | 25,000 of 25,000 sequences, and 5,000 of 5,000 from the generator of [4]; 194 of the 480 neurons used |

The published models of [4] learn the task from 50,000 examples. The network here is written from the known
rule of the task.

A fifth benchmark is the evidence accumulation task of [5]: seven cues appear on the left or on the right, and
after a delay of about one second the side with more cues has to be reported. Task and neuron model are ported
from the reference code of [5].

| Task | Trained network with adaptation [5] | Trained plain LIF [5] | Programmed plain-LIF circuit |
|---|---|---|---|
| Evidence accumulation, 7 cues, trial of 2250 ms | learned to the error criterion of 8 % with 50 LIF and 50 adaptive neurons | not solved, 100 neurons | 10,000 of 10,000 trials, 23 neurons |

A sixth benchmark is binary adding at sequence length 100 from the neuron comparison of [6]: a random bit and a
mask with nine ones arrive in every sequence, and the number of masked ones is the label (10 classes). The network
has the shape 2-128-128-10 and the membrane decay 0.5 and threshold 0.5 of the benchmark's recurrent LIF run
(its feedforward LIF run uses another decay).

| Task | Best published models [6] | Trained LIF [6] | Programmed LIF network |
|---|---|---|---|
| Binary adding, length 100, test accuracy | 100 % (three neuron models with slower or richer dynamics) | 53.35 % recurrent, 29.60 % feedforward | 10,000 of 10,000 sequences, and 2,000 of 2,000 from the generator of [6]; 41 of the 256 neurons used |

The same network, unchanged, at the longer sequences of the length comparison of [6] (its Fig. 8, which compares
five trained spiking neuron models and two non-spiking models; the values of [6] are read from the bars of
the figure, to about 2 points):

| Sequence length | 200 | 400 | 600 | 800 | 1200 | 1600 | 2400 |
|---|---|---|---|---|---|---|---|
| Best trained spiking neuron model in [6] | 100 % | 100 % | 100 % | 100 % | about 99 % | about 95 % | about 80 % |
| Trained non-spiking models in [6] | 100 % | 100 % | 100 % | 100 % | 100 % | 100 % | 100 % |
| Programmed LIF network, 41 neurons | 2,000 of 2,000 | 2,000 of 2,000 | 2,000 of 2,000 | 2,000 of 2,000 | 2,000 of 2,000 | 2,000 of 2,000 | 2,000 of 2,000 |

The count is held by which gate is silent, so the sequence length does not enter, and the gate logic is checked
in Lean for sequences of every length (below).

A two-neuron solution of the one-dimensional task with hand-set weights and adaptive neurons is shown in
[1, Figure 1D, E]. The circuits here use neurons without adaptation, and cover the two larger tasks.

**Every finite automaton, at every decay.** The gates of the binary adding network give a general construction in
the neuron model of [4] and [6] (potential d * c + x with hard reset, threshold 0.5). For an automaton with
states Q, input symbols A and any transition function, one recurrent layer of |Q| * |A| + 1 neurons with
weights 0.75 tracks the state: the gate (q, a) is silent exactly when the automaton is in state q and reads a,
and a linear readout gives the state after every step. A silent gate has drive 0 and a gate that fires is reset,
so the construction holds for every value of the decay d. This is proved in Lean
(`lean/LeakyGate/Automaton.lean`) and checked numerically on 300 random automata (`sim/lif_automaton.py`).
Recurrent networks of threshold units without leak are classically known to realize finite automata, and
automata have been built from cell assemblies of spiking neurons [7]; to our knowledge the statement for single
leaky neurons with hard reset at every decay, with a machine-checked proof, is new.

## The circuits

Weights are given in units of the firing threshold. The circuits are built from five parts.

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
- **NAND gate** (binary adding). A neuron that fires unless all of its conditions hold, with drive w times the
  number of conditions that fail and w = 0.75 against a threshold of 0.5. A silent neuron has drive exactly 0
  and a firing one is reset, so no potential is carried to the next step, whatever the membrane decay is.

**One-dimensional STORE-RECALL, 5 neurons** (`sim/sr_circuit.py`). A set detector (STORE without value 0) switches
the latch on, a reset detector (STORE without value 1) switches it off, and a fifth neuron fires at RECALL when
the latch is off. The readout takes the latch as "1" and the fifth neuron as "0". Five weight parameters.

**20-dimensional STORE-RECALL, 81 neurons** (`sim/sr20.py`). The same set detector, reset detector and latch for
each of the 20 bits, and one relay neuron for RECALL that serves as the reference level of the bias-free readout.

**12AX, 25 neurons** (`sim/twelve_ax.py`). The target of the task is a small state machine: answer R at an X
that follows 1 ... A ..., or at a Y that follows 2 ... B ..., where a digit clears the letter and an X or Y
clears it as well.
- Six relay neurons, one per relevant symbol, turn the random input spikes into regular spike trains and ignore the
  2 Hz background.
- Two latches hold the context (last digit 1 or 2).
- Two latches are armed by a gate: A in context 1, and B in context 2. Digits and the other letter clear them.
- Two answer neurons are gates of an armed latch with the X or Y relay. The readout counts their spikes.
- Two X in a row arrive as one uninterrupted input stream, so the circuit needs a clock to answer only the first.
  A timer of four latches and one output neuron starts with X or Y and clears the armed latches about 230 ms
  later, inside the 500 ms window.

Seven weight values.

**AL, 194 neurons in three layers** (`sim/al.py`). The neuron model of [4] has a hard reset and a membrane decay
per step, a layer sees the layer below in the same step, and the classifier output is averaged over all steps.
- Layer 1, 16 neurons: one neuron per pair (heading before the step, action). The heading before a step is a
  sum of these neurons at the previous step, so each neuron is a gate of that sum with the input.
- Layer 2, 174 neurons: a thermometer code of the x coordinate, where unit k fires while x is at least k, for
  k from -86 to 87. One step of this counter is a single threshold function of a unit, its two neighbours and
  the two layer-1 neurons "straight while facing +x" and "straight while facing -x". Outside the range the
  counter saturates.
- Layer 2, 2 more neurons: one fires when x goes from 0 to 1, the other when x goes from 1 to 0.
- Layer 3, 2 relay neurons. The classifier adds 1 for each spike of the first and subtracts 1 for each spike of
  the second. Over the whole sequence this sum equals 1 if the final x is at least 1 and 0 otherwise, so the
  time-averaged readout of [4] decides the label.

Four weight values, at membrane decay 0.3.

**Evidence accumulation, 23 neurons** (`sim/ea.py`). With seven cues the right side wins exactly when at least
four cues are on the right, so the circuit counts right cues up to four and ignores the left cues and the
background input.
- One relay neuron for the right-cue input and one for the recall input.
- Four latches L1 to L4, where Lk is on once k right cues have been seen.
- Between Lk and L(k+1), two slowly charging latches of about 65 ms each. They pass the state on about 130 ms
  after Lk switched on, when the cue that switched it on has ended. L(k+1) is a gate of this delayed signal and
  the relay, so each cue advances the count by exactly one. Any delay between 100 and 200 ms would do.
- One neuron fires at recall when L4 is off. The readout takes L4 as "right" and this neuron as "left".

Eight weight values, taken from the design calculation without adjustment on data.

**Binary adding, 41 neurons in two layers** (`sim/badd.py`): 40 NAND gates and one neuron that fires at every
step. A condition of a gate is an input, its complement, or "the count before the step is i".
- Layer 1, 30 neurons: for each count i from 0 to 9 and each of the three input cases (mask 0; mask 1 and bit 0;
  mask 1 and bit 1) one neuron that is silent exactly when the count before the step is i and the input is that
  case. Exactly one of the 30 is silent at every step, and "the count before the step is i" is a linear function
  of the silent neurons of the previous step. One further neuron fires at every step and marks the first step.
- Layer 2, 10 neurons: neuron j fires when the count after the step is j. The classifier reads them at the last
  step.

All weights are multiples of 0.75, and the always-firing neuron has bias 1. The result is the same at decay 0,
0.3, 0.5, 0.9 and 1 (2,000 sequences each).

## Measurements

| Script | What it runs |
|---|---|
| `sim/sr_protocol.py` | port of the one-dimensional task, the LIF network and the readout |
| `sim/sr_circuit.py` | the 5-neuron circuit on the five settings of Table 1 of [1] |
| `sim/sr20.py` | port of the 20-dimensional task and the 81-neuron circuit |
| `sim/twelve_ax.py` | port of 12AX and the 25-neuron circuit |
| `sim/sr_train.py` | 60 LIF neurons trained with backpropagation through time in the setting of [1] |
| `sim/sr_finetune.py` | the same training, started from the programmed circuit with weight noise |
| `sim/ea.py` | port of the evidence accumulation task and the 23-neuron circuit |
| `sim/ea_train.py` | 100 neurons trained with backpropagation through time in the tutorial setting of [5], with and without adaptation |
| `sim/badd.py` | the binary adding task and the programmed two-layer network |
| `sim/badd_reference_check.py` | the same network on sequences from the generator of [6] |
| `sim/lif_automaton.py` | network for any finite automaton; readout checked against the automaton on random automata, words and decays |
| `sim/badd_train.py` | recurrent LIF network of [6] trained with backpropagation through time on binary adding |
| `sim/al.py` | the AL task and the programmed three-layer network |
| `sim/al_reference_check.py` | the same network on sequences from the generator of [4] |
| `sim/al_drive_ranges.py` | every drive of the AL network lies in the ranges of `lean/LeakyGate/Basic.lean` |
| `sim/al_train.py` | recurrent LIF network of [4] trained with backpropagation through time on AL |

- One-dimensional task: seeds 1 to 5, 2,048 sequences per seed and setting. The weights were chosen on separate
  seeds, in the settings 200 ms and 2 s only.
- 20-dimensional task: seeds 1 to 3, 2,048 sequences each, test words from a fresh dictionary of 20 words per
  seed. The result is the same with the value inputs silent during RECALL, as described in [1], and with values
  shown during RECALL.
- 12AX: seeds 1 to 5, 2,000 episodes each, as many per seed as the test of [1].
- Trained LIF network of `sim/sr_train.py`: 98.5, 98.3 and 97.1 % at 200 ms for seeds 0 to 2 (96.7 % in [1]);
  50.3, 49.1 and 49.4 % at 2 s (51 % in [1]); 50.5 % at 4 s for seed 0 (50 % in [1]).
- AL: seeds 1 to 5, 5,000 sequences each (the test size of [4]) from `sim/al.py`, and 5,000 sequences from the
  unmodified generator of [4]. Labels are balanced (49.5 % positive). On average 18 % of the 480 neurons fire
  per step.
- Trained recurrent LIF network of `sim/al_train.py` on AL, 50,000 training sequences, best test accuracy over
  the epochs as in [4]: 53.5 % after 20 epochs at decay 0.5 (56.50 % after 100 epochs in [4]); 50.6 % after
  10 epochs at decay 0.3.
- Evidence accumulation: seeds 1 to 5, 2,000 trials each, in the setting of the reference tutorial of [5]
  (cues every 150 ms, recall in the last 150 ms of a 2250 ms trial, so the delay is fixed at about one second).
  Mean firing rate 108 Hz per neuron; a latch that is on fires at 200 Hz.
- Trained networks of `sim/ea_train.py` on evidence accumulation: with adaptation the error criterion of 7 % of
  the tutorial is reached after 240 and 180 iterations, test accuracy 95.3 and 93.8 % (seeds 0, 1); without
  adaptation the test accuracy is 49.2 and 51.3 % after 2,000 iterations.
- Binary adding: seeds 1 to 5, 2,000 sequences each with balanced classes (the test size of [6]) from
  `sim/badd.py`, and 2,000 test sequences drawn with the unmodified generator of [6], all at decay 0.5. On average
  12 % of the 256 neurons fire per step. Lengths 100 to 2400: 2,000 sequences each, seed 7, the fourth argument
  of `sim/badd.py` (`sim/results/badd_lengths.jsonl`).
- Finite automata: 300 random automata with up to 12 states and 5 symbols (up to 61 neurons), each at decays 0,
  0.3, 0.5, 0.9, 1 and one random value between -2 and 3, words of 200 symbols, 360,000 steps in total; the
  readout equals the state of the automaton after every step, in 32-bit floating point
  (`sim/results/lif_automaton.jsonl`).
- Trained recurrent LIF network of `sim/badd_train.py` on binary adding, in the setting of [6] (50,000 training
  sequences, 50 epochs): best test accuracy over the epochs 56.6 % (53.35 % in [6]), 53.2 % after the last epoch.
- Mean firing rate per neuron: 35 to 47 Hz (one-dimensional), 27 Hz (20-dimensional), 29 Hz (12AX). A latch
  that is on fires at the highest rate the refractory period allows, 250 Hz in the STORE-RECALL tasks and
  167 Hz in 12AX.

Outputs are in `sim/results/`.

## Training from the programmed circuit

`sim/sr_finetune.py` writes the 5-neuron circuit into a network of 60 LIF neurons, adds normally distributed noise to all
input and recurrent weights, and trains it like the network of `sim/sr_train.py`: one-dimensional STORE-RECALL
at the 2 s setting, 400 iterations, batch 64. The noise level is given in units of the standard deviation of
the random initialization. Test accuracy in %, seeds 0, 1, 2:

| Start | Before training | After, learning rate 0.001 | After, learning rate 0.01 |
|---|---|---|---|
| Random initialization | – | – | 50.5, 49.4, 49.0 |
| Programmed, no noise | 100, 100, 100 | 99.7, 99.3, 99.1 | 100, 97.2, 53.0 |
| Programmed, noise 0.15 | 66.1, 54.5, 65.5 | 100, 51.6, 57.0 | 99.6, 90.3, 49.0 |
| Programmed, noise 0.2 | 56.1, 49.3, 50.8 | 100, 50.2, 97.4 | 99.2, 57.5, 48.0 |

These runs use no rate regularization. With the rate regularization of [1], which pulls every neuron towards
10 Hz, training switches the latch off and the accuracy falls from 100 to 50.5, 52.2 and 50.1 % (no noise,
learning rate 0.01): a latch that is on fires at 250 Hz.

So gradient training at the small learning rate keeps the accuracy of the programmed circuit, at the same size
and number of iterations at which training from a random initialization (run at learning rate 0.01) stays at
chance. At learning rate 0.01 one of three seeds loses the circuit. Repair of a noisy circuit depends on the
seed. Only the accuracy is measured, not the distance of the weights from the circuit.

## Lean

`lean/SpikingCircuits/TwelveAX.lean` (Lean 4, core library only, no axioms; all axiom checks are in
`lean/axioms.txt`).

- `target`: the target function of 12AX, with the last digit and the last relevant letter as state.
- `machine`: the state machine that the 12AX circuit implements, with four flags: context 1, context 2,
  armed for X, armed for Y.
- `machine_eq_target`: both give the same outputs on every symbol sequence.
- `target_not_constant` and `machineNoClear_ne_target`: the target answers differently on two sequences, and a
  machine that does not clear its flags at X and Y disagrees with the target, so the statement has content.

`lean/SpikingCircuits/Localization.lean` (Lean 4, core library only, standard axioms).

- `finalX`: the final x coordinate of the robot in the AL task for a sequence of actions.
- `unext`: one step of a thermometer unit, a threshold function of the unit, its two neighbours and the
  increment. `unext_thermo`: it maps the thermometer code of x to that of the new x.
- `event`: the output of the two crossing units in one step. `readout`: their sum along a sequence.
- `readout_eq_label`: for every action sequence the summed readout is 1 if the final x is at least 1 and 0
  otherwise.
- `label_one`, `label_zero` and `readoutUp_ne_label`: the label takes both values, and a readout without the
  second crossing unit is wrong on a walk to x = 1 and back, so the statement has content.

In this file the thermometer code is unbounded, the heading is given directly and the crossing units are a
Boolean formula; the network of `sim/al.py` tracks x from -86 to 87, holds the heading in 16 neurons and has
extra terms for the first step.

`lean/SpikingCircuits/BinaryAdding.lean` (core Lean, standard axioms).

- `gate`: a gate with drive 3/4 times the number of its conditions that fail, against the threshold 1/2, stated
  in integers. `step`: the 30 gates of the first layer, where the count before a step is read from the silent
  gate of the previous step. `classUnit`: the units of the second layer.
- `network_eq_label`: for every non-empty sequence of masks and bits, of any length, in which at most nine steps
  have mask and bit on, class unit j fires after the last step exactly when j is the number of such steps.
- `class_units_differ` and `ten_ones_no_class`: the answer depends on the input, and with ten counted steps no
  class unit fires, so the statement has content and the bound of nine is needed.

This file states the logic of the gates with integer drives. A gate that does not fire has drive 0 and a gate that
fires is reset, so no potential is carried between steps.

`lean/LeakyGate/Basic.lean` (Lean 4 with Mathlib, standard axioms).

- Neuron model of [4]: the potential after an input x is d * c + x, where c is the potential carried over (0 after
  a spike), and the neuron spikes when it exceeds the threshold.
- `spikes_eq`: if every input is low, in [lo, L], or high, at least F, the conditions `Margins` hold, and the
  carried potential starts in the range [m, M] of `Margins` (for example at 0), the neuron spikes exactly at the
  high inputs, for input sequences of any length.
- `and_gate`, `counter_unit`, `crossing_unit`, `relay_unit`: `Margins` holds at decay 3/10 and threshold 1/2 for
  drive ranges of the four kinds of neurons of the AL network, each with a tolerance of 0.01 around the values
  given by the weights, so the hypotheses of `spikes_eq` can be met. `sim/al_drive_ranges.py` asserts that every
  drive of the simulation, computed in 32-bit floating point, lies in these ranges.
- `and_gate_outcomes`, `low_inputs_fire_at_decay_half`, `no_and_gate_margins_at_decay_half`: both outcomes occur;
  at decay 1/2 the same neuron fires at a repeated low input; and the conditions for the gate cannot be met at
  decay 1/2. So the statement has content, and its conclusion fails in a case where the margins do not hold. `Margins` is a
  sufficient condition.

`lean/LeakyGate/Automaton.lean` (Lean 4 with Mathlib, standard axioms).

- `step`: one step of the layer of |Q| * |A| gates and one marker neuron, with real potentials, hard reset and
  an arbitrary real decay d. `stateTerm`: the linear function of the spikes that says whether the automaton is in
  a given state.
- `network_hot`: for every finite automaton, every real d and every non-empty input word, after the last step
  exactly the gate of the state before the last symbol and the last symbol is silent.
- `readout_eq_state`: the linear readout for a state is 1 if the automaton is in that state after the word and 0
  otherwise.
- `hot_unique`, `not_hot_init`, `parity_readouts`, `parity_net_ne_or`: the silent gate determines state and
  symbol, the pattern is absent before the first step, the readout of the parity automaton takes both values,
  and it differs from the state of another automaton on a word of two symbols. So the statement has content.

The input is one symbol per step as a one-hot vector, and the potentials are real numbers; the weights 0.75 and
their small integer multiples are exact in binary floating point.

Lean version and Mathlib revision are fixed in `lean/lean-toolchain` and `lean/lake-manifest.json`.

Not formalized: that the drives of the neurons of `sim/al.py` lie in the ranges used above (asserted on sampled
sequences by `sim/al_drive_ranges.py`), the composition of
the three AL statements into one theorem about the network, the floating-point arithmetic of the binary adding
network, and the spiking dynamics
of the other circuits (that the latches, gates and timers realize the state machines under the random input
spikes of the tasks of [1] and [5]). These points are covered by the measurements only.

## Scope and limits

- The weights are written by hand for each task. Nothing here is learned, and the comparison says nothing
  about learning rules, which are the subject of [1].
- The tasks of [1] have small finite state, so circuits of this kind exist in principle. What is measured is their
  size and their accuracy under the random input spikes of the benchmark.
- The accuracies are measured on the stated numbers of random sequences. The Lean file covers the logic of the
  12AX state machine, not the spiking dynamics.
- The AL results are at membrane decay 0.3. With the same weights the network is also right on 2,000 of 2,000
  sequences at decay 0.2, and it fails at decay 0.35, 0.4 and 0.5 (2,000 sequences each, 51 to 53 %). The
  recurrent LIF run of [4] uses decay 0.5; decay is set per model there, between 0.3 and 1.
- In AL the x coordinate is tracked from -86 to 87. Final coordinates up to 114 in absolute value occurred in
  the test sequences and were classified correctly, since the counter saturates far from the decision boundary.
  A sequence that leaves this range and later returns to the boundary would be miscounted; this needs about
  176 moves in one direction.
- The evidence accumulation circuit uses that a trial has exactly seven cues, as in [5]. With another number
  of cues the count to four would have to change.
- Three models of [6] also reach 100 % on binary adding after training. The programmed network shows that the
  LIF model of the benchmark can represent the solution at its own decay and threshold.
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
4. Neuromorphic Sequential Arena. arXiv:2505.22035, 2025. Code: github.com/liyc5929/neuroseqbench.
5. G. Bellec, F. Scherr, A. Subramoney, E. Hajek, D. Salaj, R. Legenstein, W. Maass. A solution to the learning
   dilemma for recurrent networks of spiking neurons. Nature Communications 11:3625, 2020. Reference code:
   github.com/IGITUGraz/eligibility_propagation.
6. Spiking neural networks for temporal processing: status quo and future prospects. arXiv:2502.09449, 2025.
   Code: github.com/liyc5929/neuroseqbench.
7. J. Cabessa, G. Horcholle-Bossavit, B. Quenet. Neural computation with spiking neural networks composed of
   synfire rings. ICANN 2017, LNCS 10613, pp. 245-253.
