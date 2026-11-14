import numpy as np, nc, analyze as A, json, time, sys
n = 6; rng = np.random.default_rng(3)
bad = 0; acc = 0
for _ in range(150):
    g = nc.random_circuit(rng, n, int(rng.integers(30, 120)))
    if nc.cnf_ai(g, n): acc += 1; bad += nc.count_S(g, n) > 0
print("cnf_ai on random circuits: accepted", acc, " unsound", bad)
R = [json.loads(l) for l in open("results/an_n6.jsonl")]; R = [r for r in R if r["count"] == 0]
for r in R:
    g = [tuple(x) for x in r["gates"]]
    Z = nc.z_image_of_S(g, n); deg = A.reason_degree(Z, n)
    ess = sum(nc.count_S(g[:i] + g[i+1:], n) > 0 for i in range(len(g)))
    print(f"seed {r['seed']:2d} deg {deg} essential {ess:3d}  affineAI {nc.affine_ai(g, n)!s:5s}  3-CNF-AI {nc.cnf_ai(g, n)}", flush=True)
