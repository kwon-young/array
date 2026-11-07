import time, torch

def best(f, reps):
    f(); torch.cuda.synchronize()
    ts = []
    for _ in range(reps):
        torch.cuda.synchronize(); t0 = time.perf_counter(); f(); torch.cuda.synchronize()
        ts.append(time.perf_counter() - t0)
    return min(ts) * 1000

def data(shape):
    n = 1
    for s in shape: n *= s
    return (((torch.arange(1, n + 1, dtype=torch.float32) % 97) / 97).reshape(shape)).cuda()

print(torch.__version__, torch.cuda.get_device_name(0), "tf32:", torch.backends.cuda.matmul.allow_tf32)
for n in (512, 1024):
    a, b = data((n, n)), data((n, n))
    print(f"matmul {n}^3  torch cuda best={best(lambda: a @ b, 5):.3f} ms")
x = data((1024, 1024)); print(f"softmax 1024x1024 torch cuda best={best(lambda: torch.softmax(x, 1), 5):.3f} ms")
x = data((64, 4096));   print(f"softmax 64x4096   torch cuda best={best(lambda: torch.softmax(x, 1), 5):.3f} ms")
a, b = data((1 << 20,)), data((1 << 20,)); print(f"dot 1M            torch cuda best={best(lambda: a @ b, 5):.3f} ms")
