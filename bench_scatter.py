import time, numpy as np

def best(f, reps, sync=lambda: None):
    f(); sync()
    ts = []
    for _ in range(reps):
        sync(); t0 = time.perf_counter(); f(); sync(); ts.append(time.perf_counter() - t0)
    return min(ts) * 1000

def data(m, n):
    k = np.arange(1, m + 1)
    return ((k * 7919) % n).astype(np.int64), (k % 97).astype(np.float32)

for m, n in ((1 << 20, 256), (1 << 20, 1 << 20)):
    idx, w = data(m, n)
    print(f"scatter {m} into {n}  numpy add.at best={best(lambda: np.add.at(np.zeros(n, np.float32), idx, w), 3):.3f} ms")
    print(f"scatter {m} into {n}  numpy bincount best={best(lambda: np.bincount(idx, weights=w, minlength=n), 5):.3f} ms")
idx, _ = data(65536, 10000); g = ((np.arange(1, 65536 * 64 + 1) % 7).astype(np.float32)).reshape(65536, 64)
print(f"embedding backward 65536x64 into 10000  numpy add.at best={best(lambda: np.add.at(np.zeros((10000, 64), np.float32), idx, g), 3):.3f} ms")

try:
    import torch
    for m, n in ((1 << 20, 256), (1 << 20, 1 << 20)):
        idx, w = data(m, n); ti, tw = torch.from_numpy(idx), torch.from_numpy(w)
        print(f"scatter {m} into {n}  torch cpu index_add best={best(lambda: torch.zeros(n).index_add_(0, ti, tw), 5):.3f} ms")
        if torch.cuda.is_available():
            gi, gw = ti.cuda(), tw.cuda()
            print(f"scatter {m} into {n}  torch cuda index_add best={best(lambda: torch.zeros(n, device='cuda').index_add_(0, gi, gw), 5, torch.cuda.synchronize):.3f} ms")
    idx, _ = data(65536, 10000); ti, tg = torch.from_numpy(idx), torch.from_numpy(g)
    print(f"embedding backward 65536x64 into 10000  torch cpu best={best(lambda: torch.zeros(10000, 64).index_add_(0, ti, tg), 5):.3f} ms")
    if torch.cuda.is_available():
        gi, gg = ti.cuda(), tg.cuda()
        print(f"embedding backward 65536x64 into 10000  torch cuda best={best(lambda: torch.zeros(10000, 64, device='cuda').index_add_(0, gi, gg), 5, torch.cuda.synchronize):.3f} ms")
except ImportError:
    print("no torch")
