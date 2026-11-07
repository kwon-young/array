import time, torch

def best(f, reps, sync=lambda: None):
    f(); sync()
    ts = []
    for _ in range(reps):
        sync(); t0 = time.perf_counter(); f(); sync(); ts.append(time.perf_counter() - t0)
    return min(ts) * 1000

S, D, H = 256, 768, 3072
def mlp(x, w1, b1, w2, b2):
    a = x @ w1 + b1
    a = a * torch.sigmoid(1.702 * a)
    return a @ w2 + b2 + x

for dev in ["cpu", "cuda"] if torch.cuda.is_available() else ["cpu"]:
    x, w1, b1, w2, b2 = (torch.rand(S, D, device=dev), torch.rand(D, H, device=dev) - 0.5, torch.rand(H, device=dev),
                         torch.rand(H, D, device=dev) - 0.5, torch.rand(D, device=dev))
    sync = torch.cuda.synchronize if dev == "cuda" else (lambda: None)
    print(f"mlp {S}x{D}x{H}  torch {dev} eager best={best(lambda: mlp(x, w1, b1, w2, b2), 5, sync):.3f} ms")
    if dev == "cuda":
        with torch.profiler.profile(activities=[torch.profiler.ProfilerActivity.CUDA]) as prof:
            mlp(x, w1, b1, w2, b2); torch.cuda.synchronize()
        n = sum(1 for e in prof.events() if e.device_type == torch.autograd.DeviceType.CUDA)
        print(f"mlp torch cuda eager kernels: {n}")
        try:
            compiled = torch.compile(mlp)
            print(f"mlp {S}x{D}x{H}  torch cuda compiled best={best(lambda: compiled(x, w1, b1, w2, b2), 5, sync):.3f} ms")
        except Exception as e:
            print("torch.compile failed:", str(e)[:80])
