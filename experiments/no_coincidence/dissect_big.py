import numpy as np, nc, json, sys
R = [json.loads(l) for l in open(sys.argv[1])]
for r in R:
    n, g = r["n"], [tuple(x) for x in r["gates"]]; m = len(g)
    rng = np.random.default_rng(0)
    xs = rng.integers(0, 1 << (2*n), 20000, dtype=np.uint64)   # sample of S
    st = xs.copy(); const_counts = []
    for k in range(m):
        st = nc.evaluate([g[k]], n, st)
        zb = nc.bits(st >> np.uint64(2*n), n)
        const_counts.append(int(np.sum(np.all(zb == zb[0], axis=0))))
    cc = np.array(const_counts)
    h = r["hist"]
    print(f"seed {r['seed']}: start {h[0]} -> final {r['count']} (ideal random {2**n}); "
          f"z-wires constant on sampled reachable set: at 25/50/75/100% depth = {cc[m//4]},{cc[m//2]},{cc[3*m//4]},{cc[-1]}; "
          f"max over depth {cc.max()}; affineAI={nc.affine_ai(g, n)}")
    print("   trajectory:", h[::max(1, len(h)//15)])
