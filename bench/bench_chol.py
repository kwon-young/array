import time, sys, numpy as np

def spd(n):
    i = np.arange(n)
    return (np.minimum.outer(i, i) + 1).astype(np.float32)

def best(f, reps, sync=lambda: None):
    f(); sync()
    ts = []
    for _ in range(reps):
        sync(); t0 = time.perf_counter(); f(); sync(); ts.append(time.perf_counter() - t0)
    return min(ts) * 1000

for n in (32, 64, 256, 1024):
    a = spd(n)
    print(f"cholesky {n}  numpy best={best(lambda: np.linalg.cholesky(a), 5):.3f} ms")
for m, n in ((1024, 32), (256, 64)):
    a = np.broadcast_to(spd(n), (m, n, n)).copy()
    print(f"cholesky {n}x{m} batch  numpy best={best(lambda: np.linalg.cholesky(a), 5):.3f} ms")

try:
    import torch
    for n in (32, 64, 256, 1024):
        a = torch.from_numpy(spd(n))
        print(f"cholesky {n}  torch cpu best={best(lambda: torch.linalg.cholesky(a), 5):.3f} ms")
        if torch.cuda.is_available():
            g = a.cuda()
            print(f"cholesky {n}  torch cuda best={best(lambda: torch.linalg.cholesky(g), 5, torch.cuda.synchronize):.3f} ms")
    for m, n in ((1024, 32), (256, 64)):
        a = torch.from_numpy(np.broadcast_to(spd(n), (m, n, n)).copy())
        print(f"cholesky {n}x{m} batch  torch cpu best={best(lambda: torch.linalg.cholesky(a), 5):.3f} ms")
        if torch.cuda.is_available():
            g = a.cuda()
            print(f"cholesky {n}x{m} batch  torch cuda best={best(lambda: torch.linalg.cholesky(g), 5, torch.cuda.synchronize):.3f} ms")
except ImportError:
    print("no torch")
