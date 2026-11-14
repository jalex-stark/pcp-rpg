import numpy as np, nc, analyze as A, json, sys, itertools
n = 6
R = [json.loads(l) for l in open("results/an_n6.jsonl")]; R = [r for r in R if r["count"] == 0]
def state_after(g, k):
    xs = np.arange(1 << 12, dtype=np.uint64); return nc.evaluate(g[:k], n, xs)
fn = lambda f: {0:'0',1:'NOR',2:'~a&b',3:'~a',4:'a&~b',5:'~b',6:'XOR',7:'NAND',8:'AND',9:'XNOR',10:'b',11:'~a|b',12:'a',13:'a|~b',14:'OR',15:'1'}[f]
for r in R:
    g = [tuple(x) for x in r["gates"]]
    ess = [i for i in range(len(g)) if nc.count_S(g[:i] + g[i+1:], n) > 0]
    if len(ess) > 3: continue
    Z = nc.z_image_of_S(g, n); B = nc.bits(Z, n); deg = A.reason_degree(Z, n)
    print(f"\n--- seed {r['seed']}: degree {deg}, essential gates {ess}")
    for i in ess:
        t, c1, c2, f = g[i]; st = state_after(g, i)
        cv = lambda w: np.unique((st >> np.uint64(w)) & np.uint64(1))
        print(f"  gate {i}: w{t} ^= {fn(f)}(w{c1}, w{c2});  before it, values on reachable set: t{list(cv(t))} c1{list(cv(c1))} c2{list(cv(c2))}")
    # zero-pattern constraints in final z image
    for k in (1, 2, 3):
        for S in itertools.combinations(range(n), k):
            if not np.any(np.all(B[:, list(S)] == 0, axis=1)):
                # minimal only
                print(f"  final image never has z{[s for s in S]} all zero"); 
        else: continue
    # track each z wire constancy across depth
    xs = np.arange(1 << 12, dtype=np.uint64); st = xs.copy(); const_hist = []
    for k, gate in enumerate(g):
        st = nc.evaluate([gate], n, st)
        if k in ess or k == len(g) - 1:
            zb = nc.bits(st >> np.uint64(12), n)
            const_hist.append((k, [f"z{j}={zb[0,j]}" for j in range(n) if np.all(zb[:, j] == zb[0, j])]))
    print("  constant z-wires on reachable set after essential gates/end:", const_hist)
