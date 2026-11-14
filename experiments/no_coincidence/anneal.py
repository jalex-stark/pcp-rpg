import numpy as np, nc, sys, json, time, math
def anneal(rng, n, m, iters, T0=2.0, T1=0.05):
    W = 3*n; g = nc.random_circuit(rng, n, m); cur = nc.count_S(g, n); acc = []; hist = []
    for it in range(iters):
        T = T0 * (T1/T0) ** (it/iters)
        i = int(rng.integers(m)); old = g[i]; g[i] = nc.random_gate(rng, W)
        c = nc.count_S(g, n)
        if c <= cur or rng.random() < math.exp(-(c - cur)/T):
            if c < cur: acc.append(i)
            cur = c
        else: g[i] = old
        if it % (1000 if n < 10 else 100) == 0: hist.append(cur)
        if cur == 0: break
    return g, cur, it + 1, acc, hist
if __name__ == "__main__":
    n, m, iters, s0, s1 = map(int, sys.argv[1:6]); out = sys.argv[6]
    T0 = float(sys.argv[7]) if len(sys.argv) > 7 else 2.0; T1 = float(sys.argv[8]) if len(sys.argv) > 8 else 0.05
    for s in range(s0, s1):
        rng = np.random.default_rng(5000 + s); t = time.time()
        g, cur, its, acc, hist = anneal(rng, n, m, iters, T0, T1)
        with open(out, "a") as f: f.write(json.dumps(dict(n=n, m=m, seed=s, gates=g, count=cur, iters=its, acc=acc, hist=hist)) + "\n")
        print(f"n={n} m={m} seed {s}: final {cur} after {its} iters [{time.time()-t:.0f}s]", flush=True)
