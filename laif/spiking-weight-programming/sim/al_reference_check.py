"""Check of sim/al.py against the benchmark's own data generator, run unmodified from a local clone of
github.com/liyc5929/neuroseqbench (not part of this folder).

usage: al_reference_check.py PATH_TO/neuroseqbench/src/neuroseqbench/utils/dataset/autonomous_localization.py DATA_DIR
"""
import importlib.util, json, sys
import numpy as np
import torch
from al import circuit, run

if __name__ == "__main__":
    torch.set_num_threads(1)
    spec = importlib.util.spec_from_file_location("al_reference", sys.argv[1])
    ref = importlib.util.module_from_spec(spec); spec.loader.exec_module(ref)
    torch.manual_seed(1234)
    data = ref.AL(root=sys.argv[2], subset="test", num_data=5000, seq_length=400, capacity=20)
    x = torch.stack(data.inputs).transpose(0, 1).contiguous()          # (T, B, 3)
    y = torch.stack(data.labels).numpy()
    c = circuit()
    pred = np.concatenate([run(x[:, i:i + 1000], c, 0.3)[0].argmax(1).numpy() for i in range(0, 5000, 1000)])
    print(json.dumps(dict(check="AL circuit on 5000 sequences of the reference generator", shape=list(x.shape),
                          label_mean=float(y.mean()), accuracy=float((pred == y).mean()), wrong=int((pred != y).sum()))))
