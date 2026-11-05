import time, sys, numpy as np

# One UKF step as in ukf2.pl: B states of dimension N, scored against D detections of
# dimension M, the constant-velocity track observed as range and y. Same sigma set (2N
# points, equal weights) and same outputs: Score[B, D], PPost[B, N, N], MuSel[B, N].

CRIT = 9.21

def best(f, reps, sync=lambda: None):
    f(); sync()
    ts = []
    for _ in range(reps):
        sync(); t0 = time.perf_counter(); f(); sync(); ts.append(time.perf_counter() - t0)
    return min(ts) * 1000

def data(B, N, M, D, rng):
    mu = rng.standard_normal((B, N)).astype(np.float32) * 5 + 10
    a = rng.standard_normal((B, N, N)).astype(np.float32) * 0.1
    p = a @ a.transpose(0, 2, 1) + np.eye(N, dtype=np.float32) * 0.5
    r = np.eye(M, dtype=np.float32) * 0.5
    z = rng.standard_normal((D, M)).astype(np.float32) * 5 + 10
    sel = rng.integers(0, D, B)
    return mu, p, r, z, sel

def step_np(mu, p, r, z, sel):
    B, N = mu.shape; M = r.shape[0]; K = 2 * N
    l = np.linalg.cholesky(N * p)                                   # B N N
    x = np.concatenate([mu[:, None, :] + l.transpose(0, 2, 1), mu[:, None, :] - l.transpose(0, 2, 1)], axis=1)
    y = x.copy(); y[..., 0] += 0.5 * x[..., 2]; y[..., 1] += 0.5 * x[..., 3]
    zz = np.stack([np.sqrt(x[..., 0] ** 2 + x[..., 1] ** 2), x[..., 1]], axis=-1)
    mu_pred = y.mean(1); mu_z = zz.mean(1)
    dy = y - mu_pred[:, None]; dz = zz - mu_z[:, None]
    p_pred = np.einsum('bki,bkj->bij', dy, dy) / K
    szz = np.einsum('bki,bkj->bij', dz, dz) / K + r
    pyz = np.einsum('bki,bkj->bij', dy, dz) / K
    ls = np.linalg.cholesky(szz)
    linv = np.linalg.solve(ls, np.broadcast_to(np.eye(M, dtype=ls.dtype), ls.shape))
    sinv = linv.transpose(0, 2, 1) @ linv
    logdet = 2 * np.log(np.diagonal(ls, axis1=1, axis2=2)).sum(1)
    e = z[None, :, :] - mu_z[:, None, :]                            # B D M
    d2 = np.einsum('bdi,bij,bdj->bd', e, sinv, e)
    score = np.where(d2 <= CRIT, 0.5 * d2 + 0.5 * logdet[:, None] + 0.5 * M * np.log(2 * np.pi), np.inf)
    g = pyz @ sinv
    mu_post = mu_pred[:, None, :] + np.einsum('bij,bdj->bdi', g, e)
    p_post = p_pred - g @ szz @ g.transpose(0, 2, 1)
    mu_sel = mu_post[np.arange(B), sel]
    return score, p_post, mu_sel

def step_torch(mu, p, r, z, sel):
    import torch
    B, N = mu.shape; M = r.shape[0]; K = 2 * N
    l = torch.linalg.cholesky(N * p)
    lt = l.transpose(1, 2)
    x = torch.cat([mu[:, None, :] + lt, mu[:, None, :] - lt], dim=1)
    y = torch.stack([x[..., 0] + 0.5 * x[..., 2], x[..., 1] + 0.5 * x[..., 3], x[..., 2], x[..., 3]], dim=-1)
    zz = torch.stack([torch.sqrt(x[..., 0] ** 2 + x[..., 1] ** 2), x[..., 1]], dim=-1)
    mu_pred = y.mean(1); mu_z = zz.mean(1)
    dy = y - mu_pred[:, None]; dz = zz - mu_z[:, None]
    p_pred = dy.transpose(1, 2) @ dy / K
    szz = dz.transpose(1, 2) @ dz / K + r
    pyz = dy.transpose(1, 2) @ dz / K
    ls = torch.linalg.cholesky(szz)
    linv = torch.linalg.solve_triangular(ls, torch.eye(M, dtype=ls.dtype, device=ls.device).expand_as(ls), upper=False)
    sinv = linv.transpose(1, 2) @ linv
    logdet = 2 * torch.log(torch.diagonal(ls, dim1=1, dim2=2)).sum(1)
    e = z[None, :, :] - mu_z[:, None, :]
    d2 = torch.einsum('bdi,bij,bdj->bd', e, sinv, e)
    score = torch.where(d2 <= CRIT, 0.5 * d2 + 0.5 * logdet[:, None] + 0.5 * M * np.log(2 * np.pi), torch.inf)
    g = pyz @ sinv
    mu_post = mu_pred[:, None, :] + torch.einsum('bij,bdj->bdi', g, e)
    p_post = p_pred - g @ szz @ g.transpose(1, 2)
    mu_sel = mu_post[torch.arange(B, device=mu.device), sel]
    return score, p_post, mu_sel

def dump(path, mu, p, r, z, sel, score, p_post, mu_sel):
    # Flat row-major CSVs, so the Prolog bench can check its results against numpy.
    for name, a in (("mu", mu), ("p", p), ("r", r), ("z", z), ("sel", sel),
                    ("score", score), ("p_post", p_post), ("mu_sel", mu_sel)):
        np.savetxt(f"{path}/ukf_{name}.csv", np.asarray(a, dtype=np.float64).ravel(), delimiter=",")

SIZES = [(256, 4, 2, 16), (4096, 4, 2, 64), (65536, 4, 2, 64)]

if __name__ == "__main__":
    rng = np.random.default_rng(0)
    reps = 5
    for B, N, M, D in SIZES:
        mu, p, r, z, sel = data(B, N, M, D, rng)
        print(f"ukf B={B} N={N} M={M} D={D}  numpy best={best(lambda: step_np(mu, p, r, z, sel), reps):.3f} ms")
        if len(sys.argv) > 1 and B == 256:
            dump(sys.argv[1], mu, p, r, z, sel, *step_np(mu, p, r, z, sel))
    try:
        import torch
        for B, N, M, D in SIZES:
            mu, p, r, z, sel = data(B, N, M, D, rng)
            t = [torch.from_numpy(a) for a in (mu, p, r, z)] + [torch.from_numpy(sel)]
            print(f"ukf B={B} N={N} M={M} D={D}  torch cpu best={best(lambda: step_torch(*t), reps):.3f} ms")
            if torch.cuda.is_available():
                g = [a.cuda() for a in t]
                sync = torch.cuda.synchronize
                print(f"ukf B={B} N={N} M={M} D={D}  torch cuda best={best(lambda: step_torch(*g), reps, sync):.3f} ms")
                try:
                    c = torch.compile(step_torch)
                    print(f"ukf B={B} N={N} M={M} D={D}  torch cuda compiled best={best(lambda: c(*g), reps, sync):.3f} ms")
                except Exception as ex:
                    print(f"torch.compile failed: {type(ex).__name__}: {str(ex)[:120]}")
    except ImportError:
        print("no torch")
