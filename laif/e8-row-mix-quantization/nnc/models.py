"""Test models and data: small vision nets trained here, small open-weight LLMs from the Hub."""
import os, pathlib
import numpy as np
import torch
import torch.nn as nn
import torch.nn.functional as F

os.environ.setdefault('HF_HUB_DISABLE_TELEMETRY', '1')
ROOT = pathlib.Path(__file__).resolve().parents[1]
CKPT = ROOT / 'models'
LLMS = {'smollm': 'HuggingFaceTB/SmolLM2-135M', 'smollm360': 'HuggingFaceTB/SmolLM2-360M', 'qwen05': 'Qwen/Qwen2.5-0.5B',
        'qwen15': 'Qwen/Qwen2.5-1.5B'}


def vision_data(name):
    from datasets import load_dataset
    if name == 'mnist':
        ds = load_dataset('ylecun/mnist')
        f = lambda s: torch.tensor(np.stack([np.array(im) for im in ds[s]['image']]), dtype=torch.float32)[:, None] / 255.
        mean, std = 0.1307, 0.3081
        key = 'label'
    else:
        ds = load_dataset('uoft-cs/cifar10')
        f = lambda s: torch.tensor(np.stack([np.array(im) for im in ds[s]['img']]), dtype=torch.float32).permute(0, 3, 1, 2) / 255.
        mean, std = torch.tensor([0.49, 0.48, 0.45])[:, None, None], torch.tensor([0.25, 0.24, 0.26])[:, None, None]
        key = 'label'
    return [((f(s) - mean) / std, torch.tensor(ds[s][key])) for s in ('train', 'test')]


class MLP(nn.Module):
    def __init__(self):
        super().__init__()
        self.net = nn.Sequential(nn.Flatten(), nn.Linear(784, 1024), nn.ReLU(), nn.Linear(1024, 1024), nn.ReLU(), nn.Linear(1024, 10))

    def forward(self, x):
        return self.net(x)


class CNN(nn.Module):
    def __init__(self):
        super().__init__()
        c = lambda i, o: [nn.Conv2d(i, o, 3, padding=1), nn.BatchNorm2d(o), nn.ReLU()]
        self.net = nn.Sequential(*c(3, 64), *c(64, 64), nn.MaxPool2d(2), *c(64, 128), *c(128, 128), nn.MaxPool2d(2),
                                 *c(128, 256), *c(256, 256), nn.MaxPool2d(2), nn.Flatten(),
                                 nn.Linear(4096, 512), nn.ReLU(), nn.Dropout(0.3), nn.Linear(512, 10))

    def forward(self, x):
        return self.net(x)


def train_vision(name, epochs, lr=1e-3, bs=128):
    (xtr, ytr), (xte, yte) = vision_data(name)
    model = MLP() if name == 'mnist' else CNN()
    opt = torch.optim.AdamW(model.parameters(), lr=lr, weight_decay=5e-4)
    steps = epochs * (len(xtr) // bs)
    sched = torch.optim.lr_scheduler.OneCycleLR(opt, lr, total_steps=steps)
    for ep in range(epochs):
        model.train()
        perm = torch.randperm(len(xtr))
        for k in range(len(xtr) // bs):
            idx = perm[k * bs:(k + 1) * bs]
            x = xtr[idx]
            if name == 'cifar':  # flips and 4-pixel shifts
                if torch.rand(1) < 0.5:
                    x = x.flip(3)
                dx, dy = torch.randint(-4, 5, (2,))
                x = torch.roll(x, (int(dx), int(dy)), (2, 3))
            loss = F.cross_entropy(model(x), ytr[idx])
            opt.zero_grad(); loss.backward(); opt.step(); sched.step()
        print(name, 'epoch', ep, 'acc', accuracy(model, xte, yte), flush=True)
    CKPT.mkdir(exist_ok=True)
    torch.save(model.state_dict(), CKPT / f'{name}.pt')
    return model


@torch.no_grad()
def accuracy(model, x, y, bs=1000):
    model.eval()
    return sum((model(x[k:k + bs]).argmax(1) == y[k:k + bs]).sum().item() for k in range(0, len(x), bs)) / len(x)


def load_vision(name):
    model = MLP() if name == 'mnist' else CNN()
    model.load_state_dict(torch.load(CKPT / f'{name}.pt'))
    return model.eval()


def load_llm(name):
    from transformers import AutoModelForCausalLM, AutoTokenizer
    path = LLMS[name]
    tok = AutoTokenizer.from_pretrained(path)
    model = AutoModelForCausalLM.from_pretrained(path, dtype=torch.float32)
    return model.eval(), tok


def wikitext_ids(tok, split):
    """Token ids of a WikiText-2 split, cached on disk: tokenizing in-process costs over 1 GB of RSS."""
    f = ROOT / 'runs' / 'cache' / f"ids_{tok.name_or_path.replace('/', '_')}_{split}.pt"
    if f.exists():
        return torch.load(f)
    from datasets import load_dataset
    text = '\n\n'.join(load_dataset('Salesforce/wikitext', 'wikitext-2-raw-v1')[split]['text'])
    ids = tok(text, return_tensors='pt').input_ids[0].clone()
    f.parent.mkdir(parents=True, exist_ok=True)
    torch.save(ids, f)
    return ids


@torch.no_grad()
def perplexity(model, ids, seqlen=512, n=None, bs=4):
    w = ids[: (len(ids) // seqlen) * seqlen].reshape(-1, seqlen)
    if n:
        w = w[:n]
    nll = 0.0
    for k in range(0, len(w), bs):
        x = w[k:k + bs]
        h = model.model(x, use_cache=False).last_hidden_state[:, :-1]
        for i in range(0, h.shape[1], 512):  # head and loss in chunks: full logits are 1.2 GB per 2048 tokens
            logits = model.lm_head(h[:, i:i + 512]).float()
            nll += F.cross_entropy(logits.reshape(-1, logits.shape[-1]), x[:, i + 1:i + 513].reshape(-1), reduction='sum').item()
    v = float(np.exp(nll / (len(w) * (seqlen - 1))))
    return v if np.isfinite(v) else float('inf')  # overflow in a destroyed model counts as infinite perplexity
