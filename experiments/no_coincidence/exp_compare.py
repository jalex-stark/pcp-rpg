import numpy as np, nc, analyze as A, json, sys
rng = np.random.default_rng(7); n = 6
def natural(m):
    while True:
        g = nc.random_circuit(rng, n, m)
        if nc.count_S(g, n) == 0: return g
fams = {
 "feistel m=120": [nc.feistel_circuit(rng, n, 120) for _ in range(20)],
 "disguised(feistel), side 60": [nc.disguised(rng, n, nc.feistel_circuit(rng, n, 80), 60) for _ in range(20)],
 "natural: random m=80 with P": [natural(80) for _ in range(30)],
 "natural: random m=120 with P": [natural(120) for _ in range(20)],
}
hc = [json.loads(l) for l in open("results/an_n6.jsonl")]
fams["ANNEALED m=200 (count 0)"] = [[tuple(x) for x in r["gates"]] for r in hc if r["count"] == 0]
for k, gs in fams.items(): A.summarize(k, [A.profile(g, n, rng) for g in gs])
