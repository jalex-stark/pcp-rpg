import numpy as np, nc, sys, json, time
def climb(rng, n, m, iters, start=None, log_every=0):
    W = 3*n
    g = list(start) if start is not None else nc.random_circuit(rng, n, m)
    cur = nc.count_S(g, n); hist = [cur]; acc_pos = []
    for it in range(iters):
        i = int(rng.integers(m)); old = g[i]; g[i] = nc.random_gate(rng, W)
        c = nc.count_S(g, n)
        if c <= cur:
            if c < cur: acc_pos.append(i)
            cur = c
        else: g[i] = old
        if log_every and it % log_every == 0: hist.append(cur)
        if cur == 0: break
    return g, cur, it + 1, acc_pos, hist

if __name__ == "__main__":
    n, m, iters, seeds = map(int, sys.argv[1:5]); out = sys.argv[5]
    res = []
    for s in range(seeds):
        rng = np.random.default_rng(1000 + s); t = time.time()
        g, cur, its, acc, hist = climb(rng, n, m, iters, log_every=max(1, iters//200))
        print(f"seed {s}: final count {cur} after {its} iters, {len(acc)} improving moves  [{time.time()-t:.0f}s]", flush=True)
        res.append(dict(seed=s, gates=g, count=cur, iters=its, acc=acc, hist=hist))
    json.dump(res, open(out, "w"))
