import time, torch, torch.nn.functional as Fn

def best(f, reps, sync=lambda: None):
    f(); sync()
    ts = []
    for _ in range(reps):
        sync(); t0 = time.perf_counter(); f(); sync(); ts.append(time.perf_counter() - t0)
    return min(ts) * 1000

S, D, H, F = 256, 768, 12, 3072
Dh = D // H

def block(x, p):
    xn = Fn.layer_norm(x, (D,), p["g1"], p["b1"], 1e-5)
    qkv = xn @ p["wqkv"] + p["bqkv"]
    q, k, v = qkv.split(D, dim=1)
    q = q.view(S, H, Dh).transpose(0, 1); k = k.view(S, H, Dh).transpose(0, 1); v = v.view(S, H, Dh).transpose(0, 1)
    sc = (q @ k.transpose(1, 2)) / (Dh ** 0.5)
    pr = sc.softmax(dim=-1)
    o = (pr @ v).transpose(0, 1).reshape(S, D)
    x2 = o @ p["wo"] + p["bo"] + x
    xn2 = Fn.layer_norm(x2, (D,), p["g2"], p["b2"], 1e-5)
    a = xn2 @ p["w1"] + p["bb1"]
    a = a * torch.sigmoid(1.702 * a)
    return a @ p["w2"] + p["bb2"] + x2

for dev in ["cpu", "cuda"] if torch.cuda.is_available() else ["cpu"]:
    r = lambda *sh: torch.rand(*sh, device=dev) - 0.5
    p = dict(g1=r(D) + 1, b1=r(D), wqkv=r(D, 3 * D) * 0.05, bqkv=r(3 * D), wo=r(D, D) * 0.05, bo=r(D),
             g2=r(D) + 1, b2=r(D), w1=r(D, F) * 0.05, bb1=r(F), w2=r(F, D) * 0.05, bb2=r(D))
    x = r(S, D)
    sync = torch.cuda.synchronize if dev == "cuda" else (lambda: None)
    print(f"vit block {S}x{D} h{H} f{F}  torch {dev} eager best={best(lambda: block(x, p), 5, sync):.3f} ms")
    if dev == "cuda":
        with torch.profiler.profile(activities=[torch.profiler.ProfilerActivity.CUDA]) as prof:
            block(x, p); torch.cuda.synchronize()
        n = sum(1 for e in prof.events() if e.device_type == torch.autograd.DeviceType.CUDA)
        print(f"vit block torch cuda eager kernels: {n}")
