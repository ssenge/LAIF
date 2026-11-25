"""Check of sim/badd.py against the benchmark's own data generator, run unmodified from a local clone of
github.com/liyc5929/neuroseqbench (not part of this folder).

usage: badd_reference_check.py PATH_TO/neuroseqbench/src/neuroseqbench/utils/dataset/adding_problem.py DATA_DIR
"""
import importlib.util, json, sys
import numpy as np
import torch
from badd import circuit, run

if __name__ == "__main__":
    torch.set_num_threads(1)
    spec = importlib.util.spec_from_file_location("badd_reference", sys.argv[1])
    ref = importlib.util.module_from_spec(spec); spec.loader.exec_module(ref)
    np.random.seed(1234)
    data = ref.AddingProblem(root=sys.argv[2], subset="test", num_data=2000, seq_length=100, is_binary=True)
    x = torch.stack(data.inputs).transpose(0, 1).contiguous()          # (T, B, 2)
    y = torch.stack(data.labels).numpy()
    pred = run(x, circuit(), 0.5)[0].argmax(1).numpy()
    print(json.dumps(dict(check="binary adding network on 2000 test sequences of the reference generator",
                          shape=list(x.shape), class_counts=np.bincount(y, minlength=10).tolist(),
                          accuracy=float((pred == y).mean()), wrong=int((pred != y).sum()))))
