import numpy as np, nc
rng = np.random.default_rng(0)
n = 6
# sanity: count_S vs direct evaluation
for _ in range(5):
    g = nc.random_circuit(rng, n, 60)
    zi = nc.z_image_of_S(g, n)
    assert nc.count_S(g, n) == int((zi == 0).sum()), "mismatch"
# reversibility check: evaluate twice reversed = identity
g = nc.random_circuit(rng, n, 60)
pts = rng.integers(0, 1 << 18, 1000, dtype=np.uint64)
assert np.all(nc.evaluate(g[::-1], n, nc.evaluate(g, n, pts)) == pts)
# swapf/rewrite equivalence
for k in range(3):
    g2 = nc.rewrite_swap(rng, g, n, 3); assert np.all(nc.evaluate(g2, n, pts) == nc.evaluate(g, n, pts))
    g3 = nc.rewrite_pairs(rng, g, n, 5); assert np.all(nc.evaluate(g3, n, pts) == nc.evaluate(g, n, pts))
    assert nc.peephole(g3) is not None
print("basic ok")
