import numpy as np, nc, json, sys, itertools, collections
from math import comb

def monomials(Z, n, d):
    """Evaluate all monomials of degree 1..d in the n z-bits (no constant term)."""
    B = nc.bits(Z, n).astype(np.uint8); cols = []
    for k in range(1, d + 1):
        for S in itertools.combinations(range(n), k):
            cols.append(np.bitwise_and.reduce(B[:, list(S)], axis=1))
    return np.stack(cols, axis=1)

def reason_degree(Z, n):
    """Least d such that some polynomial q of degree <= d with q(0)=0 is 1 on every z in Z.
    (d=1: affine hyperplane missing 0.)  Returns None if 0 in Z."""
    Zu = np.unique(Z)
    if np.any(Zu == 0): return None
    for d in range(1, n + 1):
        if nc.gf2_solve(monomials(Zu, n, d), np.ones(len(Zu), dtype=np.uint8)) is not None: return d

def image_test(gates, n, rng, d=1, K=None):
    """Kind-1 tester on S: sample K points of S; accept iff their z-images fit a degree-<=d
    'reason' polynomial (q(0)=0, q=1 on samples)."""
    M = sum(comb(n, k) for k in range(1, d + 1)); K = K or 8*M + 64
    xs = rng.integers(0, 1 << (2*n), K, dtype=np.uint64)
    Z = nc.evaluate(gates, n, xs) >> np.uint64(2*n)
    if np.any(Z == 0): return False
    return nc.gf2_solve(monomials(np.unique(Z), n, d), np.ones(len(np.unique(Z)), dtype=np.uint8)) is not None

def knockout_survival(gates, n):
    return np.mean([nc.count_S(gates[:i] + gates[i+1:], n) == 0 for i in range(len(gates))])

def profile(g, n, rng, full_V=True):
    Z = nc.z_image_of_S(g, n)
    return dict(P=bool(np.all(Z != 0)), coverage=int(len(np.unique(Z[Z != 0]))),
                deg=reason_degree(Z, n), V=(nc.V(g, n, rng) or "reject").split("(")[0] if full_V else None,
                img1=image_test(g, n, rng, 1), img2=image_test(g, n, rng, 2),
                ko=float(knockout_survival(g, n)))

def summarize(name, profs):
    c = collections.Counter
    print(f"\n== {name}  (N={len(profs)})")
    print("  V verdicts:        ", dict(c(p['V'] for p in profs)))
    print("  image-test d=1/d=2:", sum(p['img1'] for p in profs), "/", sum(p['img2'] for p in profs))
    print("  reason degree:     ", dict(sorted(c(p['deg'] for p in profs).items(), key=str)))
    cov = [p['coverage'] for p in profs]; ko = [p['ko'] for p in profs]
    print(f"  z-image coverage of nonzero values: min {min(cov)} median {np.median(cov)} max {max(cov)}  (of {2**6-1})")
    print(f"  knockout survival (frac of single-gate deletions keeping P): median {np.median(ko):.3f}  mean {np.mean(ko):.3f}")
