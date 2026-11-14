"""Reversible-circuit no-coincidence experiment.

Wires: W = 3n.  x = wires [0, 2n), z = wires [2n, 3n).  S = {inputs with z = 0}.
P(C):  C(S) ∩ S = ∅   (no zero-suffix input maps to a zero-suffix output).
Gate (t, c1, c2, f):  x_t ^= f(x_c1, x_c2), f a 4-bit truth table indexed by 2a+b.
"""
import ctypes, os
import numpy as np

_lib = ctypes.CDLL(os.path.join(os.path.dirname(os.path.abspath(__file__)), "libcore.so"))
_lib.count_S.restype = ctypes.c_long
_lib.count_S.argtypes = [ctypes.c_int]*3 + [ctypes.POINTER(ctypes.c_int), ctypes.c_int]
_lib.eval_words.restype = None
_lib.eval_words.argtypes = [ctypes.c_int, ctypes.c_int, ctypes.POINTER(ctypes.c_int),
                            ctypes.POINTER(ctypes.c_uint64), ctypes.c_long]
NTHREADS = 4

def _garr(gates):
    g = np.ascontiguousarray(np.asarray(gates, dtype=np.int32).reshape(-1, 4))
    return g, g.ctypes.data_as(ctypes.POINTER(ctypes.c_int))

def count_S(gates, n):
    """|C(S) ∩ S| computed exactly over all 2^(2n) points of S."""
    g, p = _garr(gates)
    return _lib.count_S(3*n, n, len(g), p, 1 if n <= 9 else NTHREADS)

def evaluate(gates, n, pts):
    """Evaluate C on an int array of 3n-bit inputs (bit i = wire i)."""
    W = 3*n
    pts = np.asarray(pts, dtype=np.uint64)
    N = len(pts); Np = (N + 63)//64*64
    buf = np.zeros(Np, dtype=np.uint64); buf[:N] = pts
    bits = ((buf[:, None] >> np.arange(W, dtype=np.uint64)) & np.uint64(1)).astype(np.uint8)  # Np x W
    st = np.ascontiguousarray(np.packbits(bits.T, axis=1, bitorder='little')).view(np.uint64).copy()  # W x Np/64
    g, p = _garr(gates)
    _lib.eval_words(W, len(g), p, st.ctypes.data_as(ctypes.POINTER(ctypes.c_uint64)), st.shape[1])
    ob = np.unpackbits(np.ascontiguousarray(st).view(np.uint8), axis=1, bitorder='little')[:, :N]  # W x N
    return (ob.astype(np.uint64) << np.arange(W, dtype=np.uint64)[:, None]).sum(axis=0).astype(np.uint64)

def z_image_of_S(gates, n):
    xs = np.arange(1 << (2*n), dtype=np.uint64)
    return evaluate(gates, n, xs) >> np.uint64(2*n)

# ---------------------------------------------------------------- gate helpers
LINEAR_F = [12, 10, 6, 15, 3, 5, 9]          # a, b, a^b, 1, ~a, ~b, ~(a^b)
def fval(f, a, b): return (f >> (2*a + b)) & 1

def random_gate(rng, W, targets=None, controls=None, fs=None):
    targets = range(W) if targets is None else targets
    t = int(rng.choice(list(targets)))
    ctl = [w for w in (range(W) if controls is None else controls) if w != t]
    c1, c2 = rng.choice(ctl, 2, replace=False)
    c1, c2 = int(min(c1, c2)), int(max(c1, c2))
    f = int(rng.integers(16)) if fs is None else int(rng.choice(fs))
    return (t, c1, c2, f)

def random_circuit(rng, n, m):
    return [random_gate(rng, 3*n) for _ in range(m)]

def is_z(w, n): return w >= 2*n

def gate_preserves_S(g, n):
    """Syntactic rule: gate maps S into S (hence onto S and S^c onto S^c)."""
    t, c1, c2, f = g
    if not is_z(t, n): return True
    za, zb = is_z(c1, n), is_z(c2, n)
    # f must vanish whenever every z-control reads 0
    for a in (0, 1):
        for b in (0, 1):
            if (za and a) or (zb and b): continue
            if fval(f, a, b): return False
    return True

def gates_commute(g, h):
    return g[0] not in (h[1], h[2]) and h[0] not in (g[1], g[2])

# ---------------------------------------------------------------- GF(2) linear algebra
def gf2_solve(A, b):
    """Solve A x = b over GF(2). A: (r, c) uint8, b: (r,). Returns x or None."""
    A = A.copy() % 2; b = b.copy() % 2
    r, c = A.shape; piv = []; row = 0
    for col in range(c):
        p = next((i for i in range(row, r) if A[i, col]), None)
        if p is None: continue
        A[[row, p]] = A[[p, row]]; b[[row, p]] = b[[p, row]]
        for i in range(r):
            if i != row and A[i, col]:
                A[i] ^= A[row]; b[i] ^= b[row]
        piv.append(col); row += 1
        if row == r: break
    if any(b[i] for i in range(row, r)): return None
    x = np.zeros(c, dtype=np.uint8)
    for i, col in enumerate(piv): x[col] = b[i]
    return x

def bits(v, k): return ((np.asarray(v, dtype=np.uint64)[..., None] >> np.arange(k, dtype=np.uint64)) & np.uint64(1)).astype(np.uint8)

def hyperplane_avoiding_zero(vecs, k):
    """Is there ℓ with ℓ·v = 1 for every v?  (v's affine span misses 0)."""
    V = bits(vecs, k)
    return gf2_solve(V, np.ones(len(V), dtype=np.uint8)) is not None

# ---------------------------------------------------------------- Kind-1 testers
def feistel_test(gates, n, rng, T=128, R=4):
    """Accept iff, on samples, C(x,z) = (π(x), A z ⊕ F(x)) with A independent of x and the
    sampled F values lying in an affine hyperplane that misses 0."""
    W = 3*n; xm = (1 << (2*n)) - 1
    xs = rng.integers(0, 1 << (2*n), T, dtype=np.uint64)
    zs = rng.integers(0, 1 << n, (T, R), dtype=np.uint64)
    ej = np.array([1 << j for j in range(n)], dtype=np.uint64)
    pts = np.concatenate([xs, (xs[:, None] | (zs << np.uint64(2*n))).ravel(),
                          xs[0] | (ej << np.uint64(2*n))])
    out = evaluate(gates, n, pts)
    base = out[:T]; var = out[T:T + T*R].reshape(T, R); col = out[T + T*R:]
    if np.any((var & np.uint64(xm)) != (base & np.uint64(xm))[:, None]): return False
    F = base >> np.uint64(2*n); Fv = var >> np.uint64(2*n)
    A = (col >> np.uint64(2*n)) ^ F[0]          # A e_j
    Az = np.zeros_like(zs)
    for j in range(n): Az ^= np.where((zs >> np.uint64(j)) & np.uint64(1), A[j], np.uint64(0))
    if np.any(Fv != (Az ^ F[:, None])): return False
    return hyperplane_avoiding_zero(F, n)

def affine_decide(gates, n, rng, T=64):
    """Accept iff C passes affinity tests, and the reconstructed affine map provably satisfies P."""
    W = 3*n
    a, b, c = (rng.integers(0, 1 << W, T, dtype=np.uint64) for _ in range(3))
    basis = np.array([0] + [1 << i for i in range(W)], dtype=np.uint64)
    y = rng.integers(0, 1 << W, T, dtype=np.uint64)
    out = evaluate(gates, n, np.concatenate([a, b, c, a ^ b ^ c, basis, y]))
    oa, ob, oc, oabc = out[:T], out[T:2*T], out[2*T:3*T], out[3*T:4*T]
    if np.any(oa ^ ob ^ oc ^ oabc): return False
    c0 = out[4*T]; cols = out[4*T + 1:4*T + 1 + W] ^ c0
    oy = out[4*T + 1 + W:]
    pred = np.full(T, c0, dtype=np.uint64)
    for i in range(W): pred ^= np.where((y >> np.uint64(i)) & np.uint64(1), cols[i], np.uint64(0))
    if np.any(pred != oy): return False
    M = bits(cols, W).T                          # W x W, M[:, i] = image of e_i
    Mzx = M[2*n:, :2*n]; cz = bits(c0, W)[2*n:]
    return gf2_solve(Mzx, cz) is None            # no x with M_zx x = c_z  <=>  P

def affine_preserves_S(gates, n, rng, T=32):
    W = 3*n
    a, b, c = (rng.integers(0, 1 << W, T, dtype=np.uint64) for _ in range(3))
    basis = np.array([0] + [1 << i for i in range(2*n)], dtype=np.uint64)
    out = evaluate(gates, n, np.concatenate([a, b, c, a ^ b ^ c, basis]))
    if np.any(out[:T] ^ out[T:2*T] ^ out[2*T:3*T] ^ out[3*T:4*T]): return False
    return not np.any(out[4*T:] >> np.uint64(2*n))

# ---------------------------------------------------------------- Kind-2: the type system
def segment_check(gates, n, rng, use_affine_pres=False):
    """Judgments: Pres(seg) by per-gate syntax; Out(seg) by a kind-1 tester.
    Rule  Pres ; Out ; Pres  ⊢  P.  The certificate would be the cut (i, j), but there are only
    O(m^2) cuts so V just searches them all."""
    m = len(gates)
    pre = [True]
    for g in gates: pre.append(pre[-1] and gate_preserves_S(g, n))
    suf = [True]
    for g in reversed(gates): suf.append(suf[-1] and gate_preserves_S(g, n))
    suf = suf[::-1]                               # suf[j]: gates[j:] all Pres
    I = [i for i in range(m + 1) if pre[i]]; J = [j for j in range(m + 1) if suf[j]]
    for i in I:
        for j in J:
            if j <= i: continue
            seg = gates[i:j]
            if feistel_test(seg, n, rng) or affine_decide(seg, n, rng):
                return (i, j)
    return None

def V(gates, n, rng):
    if affine_ai(gates, n): return "affine-AI"
    if feistel_test(gates, n, rng): return "feistel"
    if affine_decide(gates, n, rng): return "affine"
    cut = segment_check(gates, n, rng)
    if cut is not None: return f"segment{cut}"
    return None

# ---------------------------------------------------------------- families
def feistel_circuit(rng, n, m, p_x=0.4, p_mix=0.2):
    """x -> π(x);  z -> A z ⊕ F(x) with ℓ·F(x) = 1 for a hidden ℓ (tracked through mixing)."""
    W = 3*n; X = list(range(2*n)); Z = list(range(2*n, W))
    ell = rng.integers(0, 2, n); ell[0] = 1
    gates = [(2*n, 0, 1, 15)]                    # z0 ^= 1 : F = e0, ℓ·F = 1
    while len(gates) < m:
        r = rng.random()
        if r < p_x:
            gates.append(random_gate(rng, W, X, X))
        elif r < p_x + p_mix:                     # z_i ^= z_j : ℓ_j += ℓ_i
            i, j = rng.choice(n, 2, replace=False)
            d = int(rng.choice([w for w in range(W) if w not in (2*n + i, 2*n + j)]))
            c1, c2 = sorted((2*n + j, d)); f = 12 if c1 == 2*n + j else 10
            gates.append((2*n + i, c1, c2, f)); ell[j] ^= ell[i]
        else:                                     # z gets g(x) along a direction in ker ℓ
            g = random_gate(rng, W, [0], X)[1:]
            zero = [j for j in range(n) if ell[j] == 0]
            if zero and rng.random() < 0.6:
                gates.append((2*n + int(rng.choice(zero)),) + g)
            else:
                ones = [j for j in range(n) if ell[j] == 1]
                if len(ones) < 2: continue
                j, k = rng.choice(ones, 2, replace=False)
                gates += [(2*n + int(j),) + g, (2*n + int(k),) + g]
    return gates

def affine_P_circuit(rng, n, m, max_tries=100000):
    for _ in range(max_tries):
        g = [random_gate(rng, 3*n, fs=LINEAR_F) for _ in range(m)]
        if count_S(g, n) == 0: return g
    raise RuntimeError

def random_pres_gate(rng, n, p_z=0.3):
    W = 3*n
    while True:
        if rng.random() < p_z:
            t = int(rng.integers(2*n, W))
            c1, c2 = sorted(rng.choice([w for w in range(W) if w != t], 2, replace=False))
            g = (t, int(c1), int(c2), int(rng.integers(1, 16)))
        else:
            g = random_gate(rng, W, range(2*n), None)
            if g[3] == 0: continue
        if gate_preserves_S(g, n): return g

def disguised(rng, n, core, m_side):
    R = [random_pres_gate(rng, n) for _ in range(m_side)]
    L = [random_pres_gate(rng, n) for _ in range(m_side)]
    return R + core + L

# ---------------------------------------------------------------- Kind-3: rewrites
def drift(rng, gates, steps):
    g = list(gates)
    for _ in range(steps):
        i = int(rng.integers(len(g) - 1))
        if gates_commute(g[i], g[i+1]): g[i], g[i+1] = g[i+1], g[i]
    return g

def rewrite_pairs(rng, gates, n, k, drift_steps=None):
    """Insert k copies of g·g (identity) with random non-Pres g, then commute gates around."""
    g = list(gates)
    for _ in range(k):
        while True:
            h = random_gate(rng, 3*n)
            if not gate_preserves_S(h, n): break
        p = int(rng.integers(len(g) + 1)); g[p:p] = [h, h]
    return drift(rng, g, drift_steps if drift_steps is not None else 20*len(g))

def peephole(gates):
    """Cancel equal gates that can be brought together by commutations (canonicaliser V')."""
    g = list(gates); changed = True
    while changed:
        changed = False
        for i in range(len(g)):
            for j in range(i + 1, len(g)):
                if g[j] == g[i]:
                    del g[j]; del g[i]; changed = True; break
                if not gates_commute(g[i], g[j]): break
            if changed: break
    return g

def cnot(t, c, W):
    d = next(w for w in range(W) if w not in (t, c))
    c1, c2 = sorted((c, d)); return (t, c1, c2, 12 if c1 == c else 10)

def rewrite_swap(rng, gates, n, k):
    """Insert SWAP(u,v) = 3 CNOTs at a random point, relabel u<->v in everything after, and
    append SWAP(u,v) at the end. Functionally identical; wire roles move mid-circuit."""
    W = 3*n; g = list(gates)
    for _ in range(k):
        u = int(rng.integers(2*n)); v = int(rng.integers(2*n, W))
        p = int(rng.integers(len(g) + 1))
        sw = [cnot(u, v, W), cnot(v, u, W), cnot(u, v, W)]
        perm = lambda w: v if w == u else u if w == v else w
        tail = [(perm(a), *sorted((perm(b), perm(c))), f if (perm(b) < perm(c)) == (b < c) else swapf(f))
                for a, b, c, f in g[p:]]
        g = g[:p] + sw + tail + sw
    return g

def swapf(f):
    """truth table of f with arguments swapped"""
    return sum(fval(f, b, a) << (2*a + b) for a in (0, 1) for b in (0, 1))

# ---------------------------------------------------------------- Kind-2 without certificate:
# forward abstract interpretation with an affine domain + value-numbered fresh variables.
def affine_ai(gates, n):
    """Sound proof of P (no randomness): over-approximate C_i(S) by {p + G λ}, where each
    nonlinear gate value becomes a fresh parameter λ (identical expressions share one).
    Accept iff the final z-coordinates p_z + G_z λ can never all be 0."""
    W = 3*n
    p = np.zeros(W, dtype=np.uint8)
    cols = [np.eye(W, dtype=np.uint8)[:, i] for i in range(2*n)]   # x free, z = 0
    memo = {}
    def form(w):  # affine form of wire w: (coeff vector over params, const)
        return tuple(i for i, c in enumerate(cols) if c[w]), int(p[w])
    for (t, c1, c2, f) in gates:
        (a, a0), (b, b0) = form(c1), form(c2)
        P = len(cols); av = np.zeros(P, np.uint8); av[list(a)] = 1; bv = np.zeros(P, np.uint8); bv[list(b)] = 1
        # restrict f to the affine forms
        res = None
        if not av.any() and not bv.any(): res = (np.zeros(P, np.uint8), fval(f, a0, b0))
        elif not bv.any() or (av == bv).all():
            # f(u, v) with v = const or v = u + const: unary in u
            if not bv.any(): g0, g1 = fval(f, a0, b0), fval(f, a0 ^ 1, b0)
            else: g0, g1 = fval(f, a0, b0), fval(f, a0 ^ 1, b0 ^ 1)
            res = ((g0 ^ g1) * av, g0)      # value = g0 + (g0^g1)*(u - a0) ; u-a0 = a·λ
        elif not av.any():
            g0, g1 = fval(f, a0, b0), fval(f, a0, b0 ^ 1); res = ((g0 ^ g1) * bv, g0)
        else:
            # independent: affine iff f is affine as a 2-variable function
            f00, f01, f10, f11 = fval(f, a0, b0), fval(f, a0, b0^1), fval(f, a0^1, b0), fval(f, a0^1, b0^1)
            if f00 ^ f01 ^ f10 ^ f11 == 0: res = (((f10 ^ f00) * av) ^ ((f01 ^ f00) * bv), f00)
        if res is not None:
            h, h0 = res; p[t] ^= h0
            for i in range(P):
                if h[i]: cols[i][t] ^= 1
        else:
            key = (f, a, a0, b, b0)
            if key not in memo:
                memo[key] = len(cols); cols.append(np.zeros(W, dtype=np.uint8))
            cols[memo[key]][t] ^= 1
    G = np.stack(cols, axis=1) if cols else np.zeros((W, 0), np.uint8)
    return gf2_solve(G[2*n:], p[2*n:]) is None

# ---------------------------------------------------------------- Kind-2 without certificate (2):
# forward propagation of a k-CNF invariant (clauses of width <= k), checked locally per gate.
import itertools as _it
def cnf_ai(gates, n, k=3):
    """Sound proof of P: maintain a set of clauses (literal = (wire, value)) that hold on C_i(S).
    For each gate t ^= f(c1,c2): clauses avoiding t survive; new clauses containing t, over t,
    the controls and z-wires, are kept if implied by the old clauses restricted to the local
    wires. Accept iff some final clause is violated by z = 0 (all its literals are (z_j, 1))."""
    W = 3*n; Zw = list(range(2*n, W))
    Phi = {frozenset([(z, 1 - 1)]) for z in Zw}            # z_j = 0  i.e. literal (z_j, 0)
    def holds(cl, assign): return any(assign[w] == v for w, v in cl)
    for (t, c1, c2, f) in gates:
        keep = {cl for cl in Phi if all(w != t for w, _ in cl)}
        pool = sorted(set(Zw) | {c1, c2} - {t})
        new = set()
        for r in range(0, k):
            for others in _it.combinations(pool, r):
                Vw = sorted({t, c1, c2, *others})
                local = [cl for cl in Phi if all(w in Vw for w, _ in cl)]
                posts = []
                for vals in _it.product((0, 1), repeat=len(Vw)):
                    a = dict(zip(Vw, vals))
                    if all(holds(cl, a) for cl in local):
                        a[t] ^= fval(f, a[c1], a[c2]); posts.append(a)
                for signs in _it.product((0, 1), repeat=r + 1):
                    cl = frozenset([(t, signs[0])] + [(w, s) for w, s in zip(others, signs[1:])])
                    if all(holds(cl, a) for a in posts): new.add(cl)
        # drop subsumed clauses
        allc = keep | new
        Phi = {c for c in allc if not any(d < c for d in allc)}
    return any(all(w >= 2*n and v == 1 for w, v in cl) for cl in Phi)

def rewrite_split(rng, gates, n, frac=1.0):
    """Replace gate t^=f by t^=f1 ; t^=f2 with f1 xor f2 = f, f1 random (same controls).
    Functionally identical; each half is typically nonlinear."""
    out = []
    for g in gates:
        t, c1, c2, f = g
        if rng.random() < frac:
            f1 = int(rng.integers(16)); out += [(t, c1, c2, f1), (t, c1, c2, f ^ f1)]
        else: out.append(g)
    return out
