import numpy as np, nc, collections
rng = np.random.default_rng(21); n = 6
def verdicts(gs):
    c = collections.Counter()
    for g in gs:
        assert nc.count_S(g, n) == 0
        c[(nc.V(g, n, rng) or "reject").split("(")[0]] += 1
    return dict(c)
base = {"feistel": [nc.feistel_circuit(rng, n, 100) for _ in range(20)],
        "disguised(feistel)": [nc.disguised(rng, n, nc.feistel_circuit(rng, n, 80), 50) for _ in range(20)]}
rw = {"none": lambda g: g,
      "commutation drift": lambda g: nc.drift(rng, g, 4000),
      "pair insert x3 + drift": lambda g: nc.rewrite_pairs(rng, g, n, 3),
      "swap-relabel x1": lambda g: nc.rewrite_swap(rng, g, n, 1),
      "split every gate f=f1^f2": lambda g: nc.rewrite_split(rng, g, n),
      "split + drift": lambda g: nc.drift(rng, nc.rewrite_split(rng, g, n), 4000)}
for bn, gs in base.items():
    for rn, r in rw.items():
        print(f"{bn:20s} | {rn:26s} | {verdicts([r(g) for g in gs])}", flush=True)
