import numpy as np, nc, sys, time
n = int(sys.argv[1]); ms = [int(a) for a in sys.argv[2].split(',')]; N = int(sys.argv[3])
rng = np.random.default_rng(1)
mu = 2.0**(2*n) * 2.0**(2*n) / 2.0**(3*n)
print(f"n={n}: ideal mean≈{mu:.1f}, var≈{mu:.1f}")
for m in ms:
    t = time.time()
    c = np.array([nc.count_S(nc.random_circuit(rng, n, m), n) for _ in range(N)])
    print(f"m={m:4d}  mean={c.mean():8.1f}  var/mean={c.var()/c.mean():7.2f}  frac(P)={np.mean(c==0):.4f}  ({(time.time()-t)/N*1e3:.1f} ms/circuit)")
