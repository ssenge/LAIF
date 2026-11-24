#!/bin/bash
# The runs of the pixel test (about 4 minutes each on 2 CPU threads); results are appended to pixel_runs.jsonl.
PY=${PY:-python}
cd "$(dirname "$0")"
for seed in 0 1 2; do for cfg in "lewm" "inv" "invcov --white 1 --mu 10" "sup"; do
  $PY pixel_toy.py --seed $seed --out pixel_runs.jsonl --variant $cfg | tail -1
done; done
for mu in 1 10; do $PY pixel_toy.py --seed 0 --out pixel_runs.jsonl --variant cov --white 1 --mu $mu | tail -1; done
$PY pixel_table.py pixel_runs.jsonl
