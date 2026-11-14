import numpy as np, nc, collections, time
rng = np.random.default_rng(2); n = 6
def run(name, gen, N):
    t = time.time(); res = collections.Counter(); P = 0
    for _ in range(N):
        g = gen(); p = nc.count_S(g, n) == 0; P += p
        v = nc.V(g, n, rng); res[(p, (v or 'reject').split('(')[0])] += 1
    print(f"{name:34s} N={N:4d}  P-holds={P:4d}  " + "  ".join(f"{'P' if k[0] else '¬P'}:{k[1]}={c}" for k, c in sorted(res.items())) + f"  [{time.time()-t:.0f}s]")
run("random m=200 (soundness)", lambda: nc.random_circuit(rng, n, 200), 300)
run("feistel m=120", lambda: nc.feistel_circuit(rng, n, 120), 100)
aff = [nc.affine_P_circuit(rng, n, 80) for _ in range(50)]
it = iter(aff); run("affine-P m=80", lambda: next(it), 50)
it = iter(aff); run("affine-P + nonlinear cancelling pairs", lambda: nc.rewrite_pairs(rng, next(it), n, 10), 50)
run("disguised(feistel, side=60)", lambda: nc.disguised(rng, n, nc.feistel_circuit(rng, n, 80), 60), 60)
it = iter(aff); run("disguised(affine, side=60)", lambda: nc.disguised(rng, n, next(it), 60), 50)
# kind 3
run("disguised + 2 pair-insertions", lambda: nc.rewrite_pairs(rng, nc.disguised(rng, n, nc.feistel_circuit(rng, n, 80), 60), n, 2), 40)
run("  ... after peephole canonicaliser", lambda: nc.peephole(nc.rewrite_pairs(rng, nc.disguised(rng, n, nc.feistel_circuit(rng, n, 80), 60), n, 2)), 40)
run("disguised + 1 swap-relabel", lambda: nc.rewrite_swap(rng, nc.disguised(rng, n, nc.feistel_circuit(rng, n, 80), 60), n, 1), 40)
run("  ... after peephole canonicaliser", lambda: nc.peephole(nc.rewrite_swap(rng, nc.disguised(rng, n, nc.feistel_circuit(rng, n, 80), 60), n, 1)), 40)
