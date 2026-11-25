"""LeWM planning evaluation (eval.py of the LeWM code at $LEWM_DIR, unchanged) for checkpoints that carry the extra inverse-dynamics head."""
import os
import sys

import train_b2  # noqa: F401  (patches jepa.JEPA so that the checkpoints load)
import eval as lewm_eval  # the LeWM eval.py, on the path set by train_b2
import torch

_to = torch.nn.Module.to


def _to_mps(self, *args, **kwargs):  # eval.py moves the model to "cuda"; this machine has MPS
    args = tuple("mps" if a == "cuda" else a for a in args)
    return _to(self, *args, **kwargs)


torch.nn.Module.to = _to_mps

import distract  # noqa: E402

if distract.AMP:
    distract.patch_eval()

if __name__ == "__main__":
    sys.argv[0] = os.path.join(train_b2.LEWM, "eval.py")
    lewm_eval.run()
