import numpy as np, nc, analyze as A, json, sys
n = 6; rng = np.random.default_rng(9)
R = [json.loads(l) for l in open(sys.argv[1])]; R = [r for r in R if r["count"] == 0]
rows = []
for r in R:
    g = [tuple(x) for x in r["gates"]]; m = len(g)
    Z = nc.z_image_of_S(g, n); deg = A.reason_degree(Z, n); cov = len(np.unique(Z))
    ess = [i for i in range(m) if nc.count_S(g[:i] + g[i+1:], n) > 0]
    ztarg = sum(g[i][0] >= 2*n for i in ess)
    rows.append((deg, cov, len(ess), ess, ztarg, nc.affine_ai(g, n), r["iters"]))
rows.sort(key=lambda x: (x[0], x[2]))
print("deg cov #essential  AI   essential gate positions (z-targets among them)")
for deg, cov, ne, ess, zt, ai, it in rows:
    pos = ess if ne <= 12 else f"{ess[:6]}...{ess[-3:]} (median pos {int(np.median(ess))})"
    print(f"{deg:3d} {cov:3d} {ne:6d}  {str(ai):5s} {pos}  z-targets={zt}")
