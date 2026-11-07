import time, sys, numpy as np

# A key-payload sort as in sort.pl: N float32 keys, distinct and scrambled, with their
# positions as payload. numpy's argsort and torch's sort, which return the payload order and
# the sorted keys, the best of 5 runs.

def best(f, reps, sync=lambda: None):
    f(); sync()
    ts = []
    for _ in range(reps):
        sync(); t0 = time.perf_counter(); f(); sync(); ts.append(time.perf_counter() - t0)
    return min(ts) * 1000

def keys(n):
    i = np.arange(1, n + 1, dtype=np.int64)
    return (((i * 7919) % n) + 0.5).astype(np.float32)

SIZES = [65536, 1048576, 4194304]

if __name__ == "__main__":
    reps = 5
    for n in SIZES:
        k = keys(n)
        print(f"sort {n}  numpy argsort best={best(lambda: np.argsort(k), reps):.3f} ms")
    try:
        import torch
        for n in SIZES:
            t = torch.from_numpy(keys(n))
            print(f"sort {n}  torch cpu best={best(lambda: torch.sort(t), reps):.3f} ms")
            if torch.cuda.is_available():
                g = t.cuda()
                sync = torch.cuda.synchronize
                print(f"sort {n}  torch cuda best={best(lambda: torch.sort(g), reps, sync):.3f} ms")
    except ImportError:
        print("no torch")
