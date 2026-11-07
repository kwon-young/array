import time, torch, torch.nn.functional as Fn

def best(f, reps, sync=lambda: None):
    f(); sync()
    ts = []
    for _ in range(reps):
        sync(); t0 = time.perf_counter(); f(); sync(); ts.append(time.perf_counter() - t0)
    return min(ts) * 1000

S, D, H, F = 256, 768, 12, 3072
Dh = D // H

def block(x, p, sdpa=False):
    xn = Fn.layer_norm(x, (D,), p["g1"], p["b1"], 1e-5)
    qkv = xn @ p["wqkv"] + p["bqkv"]
    q, k, v = qkv.split(D, dim=1)
    q = q.view(S, H, Dh).transpose(0, 1); k = k.view(S, H, Dh).transpose(0, 1); v = v.view(S, H, Dh).transpose(0, 1)
    if sdpa:
        o = Fn.scaled_dot_product_attention(q, k, v)
    else:
        sc = (q @ k.transpose(1, 2)) / (Dh ** 0.5)
        o = sc.softmax(dim=-1) @ v
    o = o.transpose(0, 1).reshape(S, D)
    x2 = o @ p["wo"] + p["bo"] + x
    xn2 = Fn.layer_norm(x2, (D,), p["g2"], p["b2"], 1e-5)
    a = xn2 @ p["w1"] + p["bb1"]
    a = a * torch.sigmoid(1.702 * a)
    return a @ p["w2"] + p["bb2"] + x2

def kernels(f):
    with torch.profiler.profile(activities=[torch.profiler.ProfilerActivity.CUDA]) as prof:
        f(); torch.cuda.synchronize()
    return sum(1 for e in prof.events() if e.device_type == torch.autograd.DeviceType.CUDA)

print("torch", torch.__version__)
for dev in ["cpu", "cuda"] if torch.cuda.is_available() else ["cpu"]:
    r = lambda *sh: torch.rand(*sh, device=dev) - 0.5
    p = dict(g1=r(D) + 1, b1=r(D), wqkv=r(D, 3 * D) * 0.05, bqkv=r(3 * D), wo=r(D, D) * 0.05, bo=r(D),
             g2=r(D) + 1, b2=r(D), w1=r(D, F) * 0.05, bb1=r(F), w2=r(F, D) * 0.05, bb2=r(D))
    x = r(S, D)
    sync = torch.cuda.synchronize if dev == "cuda" else (lambda: None)
    if dev == "cuda":
        print("cuda device", torch.cuda.get_device_name(0), "capability", torch.cuda.get_device_capability(0))
    variants = [("eager", lambda: block(x, p)), ("eager+sdpa", lambda: block(x, p, sdpa=True))]
    for name, f in variants:
        try:
            line = f"vit block {S}x{D} h{H} f{F}  torch {dev} {name:12s} best={best(f, 5, sync):.3f} ms"
            if dev == "cuda":
                line += f"  kernels={kernels(f)}"
            print(line)
        except Exception as e:
            print(f"vit block torch {dev} {name}: failed: {str(e).splitlines()[0][:100]}")
    for name, sdpa in [("compile", False), ("compile+sdpa", True)]:
        try:
            torch._dynamo.reset()
            c = torch.compile(lambda x, p: block(x, p, sdpa=sdpa))
            f = lambda: c(x, p)
            line = f"vit block {S}x{D} h{H} f{F}  torch {dev} {name:12s} best={best(f, 5, sync):.3f} ms"
            if dev == "cuda":
                line += f"  kernels={kernels(f)}"
            print(line)
        except Exception as e:
            print(f"vit block torch {dev} {name}: failed: {str(e).splitlines()[0][:120]}")
