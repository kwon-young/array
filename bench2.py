import time, numpy as np, os

def data(shape):
    n = int(np.prod(shape))
    return (((np.arange(1, n + 1) % 97) / 97).astype(np.float32)).reshape(shape)

def best(f, reps):
    f()
    ts = []
    for _ in range(reps):
        t0 = time.perf_counter(); f(); ts.append(time.perf_counter() - t0)
    return min(ts) * 1000

def softmax(x):
    m = x.max(axis=1, keepdims=True)
    e = np.exp(x - m)
    return e / e.sum(axis=1, keepdims=True)

a, b = data((512, 512)), data((512, 512))
print(f"matmul 512^3   numpy best={best(lambda: a @ b, 5):.3f} ms")
a, b = data((1024, 1024)), data((1024, 1024))
print(f"matmul 1024^3  numpy best={best(lambda: a @ b, 3):.3f} ms")
x = data((1024, 1024))
print(f"softmax 1024x1024 numpy best={best(lambda: softmax(x), 5):.3f} ms")
x = data((64, 4096))
print(f"softmax 64x4096   numpy best={best(lambda: softmax(x), 5):.3f} ms")
a, b = data((1 << 20,)), data((1 << 20,))
print(f"dot 1M            numpy best={best(lambda: a @ b, 5):.3f} ms")
print("threads:", os.cpu_count(), "OPENBLAS_NUM_THREADS=", os.environ.get("OPENBLAS_NUM_THREADS"))
