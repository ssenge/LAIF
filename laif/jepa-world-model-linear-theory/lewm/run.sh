#!/bin/bash
# The TwoRoom runs with the static distractor: train 4000 steps at 64 px on MPS, then the planning evaluation of LeWM.
# Needs: a clone of the LeWM code in $LEWM_DIR (default ./le-wm), stable-worldmodel[train,env] and hdf5plugin installed,
# and the TwoRoom dataset as $STABLEWM_HOME/datasets/tworoom.h5.
# usage: run.sh NAME SEED [extra overrides], e.g. run.sh invcov 3072 +b2.lam_inv=1 +b2.mu=0.1
set -e
D="$(cd "$(dirname "$0")" && pwd)"; LEWM_DIR=${LEWM_DIR:-$D/le-wm}; export LEWM_DIR
export PYTORCH_ENABLE_MPS_FALLBACK=1 B2_DISTRACT=${B2_DISTRACT:-1.0}
NAME=$1; SEED=$2; shift 2
python "$D/train_b2.py" --config-path="$LEWM_DIR/config/train" --config-name=lewm data=tworoom seed=$SEED \
  output_model_name=$NAME subdir=$NAME img_size=64 model.encoder.patch_size=8 loader.batch_size=64 num_workers=2 \
  trainer.accelerator=mps trainer.precision=32 trainer.max_epochs=1 wandb.enabled=False \
  +trainer.limit_train_batches=4000 +trainer.limit_val_batches=50 "data.dataset.keys_to_load=[pixels,action,proprio,ep_idx]" "$@"
python "$D/eval_b2.py" --config-path="$LEWM_DIR/config/eval" --config-name=tworoom.yaml policy=$NAME eval.img_size=64 \
  solver.device=mps eval.num_eval=50 world.max_episode_steps=100
