# What is the reason in naturally occurring P-circuits of under-mixed random circuits?
import numpy as np, nc, analyze as A, collections, itertools
rng = np.random.default_rng(11); n = 6; stats = collections.Counter(); ex = []
for trial in range(40):
    while True:
        g = nc.random_circuit(rng, n, 80)
        if nc.count_S(g, n) == 0: break
    Z = nc.z_image_of_S(g, n); B = nc.bits(Z, n)
    const1 = [j for j in range(n) if B[:, j].all()]
    deg = A.reason_degree(Z, n)
    # last gate targeting each z-wire
    lastf = {}
    for k, (t, c1, c2, f) in enumerate(g):
        if t >= 2*n: lastf[t - 2*n] = (k, f, c1, c2)
    untouched = [j for j in range(n) if j not in lastf]
    if const1:
        j = const1[0]; k, f, c1, c2 = lastf.get(j, (None, None, None, None))
        # does the wire's value after its last gate equal 1 identically? (constant f=15 or depends)
        kind = "const-1 coordinate; last gate f=%s" % f
    elif deg == 1: kind = "affine hyperplane (weight>1 functional)"
    else: kind = f"degree-{deg} reason"
    stats[kind.split(';')[0]] += 1
    targets = collections.Counter(t - 2*n for (t, *_ ) in g if t >= 2*n)
    if trial < 8: print(f"trial {trial}: {kind}; z-wire target counts {dict(sorted(targets.items()))}; deg {deg}")
print(dict(stats))
