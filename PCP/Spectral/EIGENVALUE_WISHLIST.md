# Eigenvalue Theory Wishlist

Missing lemmas for `Matrix.IsHermitian.eigenvalues` that would simplify spectral theory work.

## High Priority - Needed for Unit03_OperatorNorm

### 1. Identity Matrix Eigenvalues
```lean
lemma Matrix.IsHermitian.eigenvalues_one [DecidableEq n] [Nonempty n]
    (h1 : (1 : Matrix n n ℝ).IsHermitian) (i : n) :
    h1.eigenvalues i = 1
```
**Why**: Identity matrix has all eigenvalues equal to 1 (basic spectral theory fact)
**Use case**: Prove `spectralRadius_one` in Unit03_OperatorNorm

### 2. Scalar Multiplication
```lean
lemma Matrix.IsHermitian.eigenvalues_smul [DecidableEq n]
    (A : Matrix n n ℝ) (hA : A.IsHermitian) (c : ℝ)
    (hcA : (c • A).IsHermitian) (i : n) :
    hcA.eigenvalues i = c * hA.eigenvalues i
```
**Why**: Eigenvalues scale linearly with matrix scaling
**Use case**: Prove `spectralRadius_smul` (needed for spectral radius properties)

### 3. Matrix Negation
```lean
lemma Matrix.IsHermitian.eigenvalues_neg [DecidableEq n]
    (A : Matrix n n ℝ) (hA : A.IsHermitian) (hNA : (-A).IsHermitian) (i : n) :
    hNA.eigenvalues i = -(hA.eigenvalues i)
```
**Why**: Eigenvalues of `-A` are negatives of eigenvalues of `A`
**Use case**: Prove `spectralRadius_neg` (spectral radius unchanged under negation since we take absolute values)

## Medium Priority - Nice to Have

### 4. Transpose Invariance
```lean
lemma Matrix.IsHermitian.eigenvalues_transpose [DecidableEq n]
    (A : Matrix n n ℝ) (hA : A.IsHermitian) (hAT : Aᵀ.IsHermitian) :
    ∃ σ : Equiv.Perm n, ∀ i, hAT.eigenvalues i = hA.eigenvalues (σ i)
```
**Why**: For Hermitian matrices, transpose has same eigenvalues (possibly reordered)
**Use case**: Prove `spectralRadius_transpose`
**Note**: Might just be equality of eigenvalues functions if ordering is preserved

### 5. Addition Bound
```lean
lemma Matrix.IsHermitian.eigenvalues_add_bound [DecidableEq n]
    (A B : Matrix n n ℝ) (hA : A.IsHermitian) (hB : B.IsHermitian)
    (hAB : (A + B).IsHermitian) (i : n) :
    ∃ j k, hAB.eigenvalues i ≤ hA.eigenvalues j + hB.eigenvalues k
```
**Why**: Eigenvalues of sum relate to eigenvalues of summands
**Use case**: Prove `spectralRadius_add_le` bounds

## Lower Priority - Advanced Theory

### 6. Rayleigh Quotient Maximum
```lean
lemma Matrix.IsHermitian.eigenvalues_eq_rayleigh_max [DecidableEq n] [Nonempty n]
    (A : Matrix n n ℝ) (hA : A.IsHermitian) :
    (univ.sup' univ_nonempty hA.eigenvalues) =
      ⨆ (v : n → ℝ) (_ : v ≠ 0), (A *ᵥ v) ⬝ᵥ v / (v ⬝ᵥ v)
```
**Why**: Maximum eigenvalue equals maximum Rayleigh quotient (variational characterization)
**Use case**: Connect spectral radius to operator norm via Rayleigh quotient

### 7. Matrix Powers
```lean
lemma Matrix.IsHermitian.eigenvalues_pow [DecidableEq n]
    (A : Matrix n n ℝ) (hA : A.IsHermitian) (k : ℕ)
    (hAk : (A ^ k).IsHermitian) (i : n) :
    ∃ j, hAk.eigenvalues i = (hA.eigenvalues j) ^ k
```
**Why**: Eigenvalues of `A^k` are k-th powers of eigenvalues of `A`
**Use case**: Spectral radius of matrix powers

## Proof Strategy Notes

All of these should be provable using:
- `Matrix.IsHermitian.spectral_theorem` - the diagonalization `A = U D U*`
- `Matrix.IsHermitian.mulVec_eigenvectorBasis` - eigenvector property `Av = λv`
- Properties of diagonal matrices under operations
- Uniqueness of spectral decomposition

The proofs are not trivial (likely >5 tactics), so they don't fit the "slop" lemma budget. They belong in mathlib or in helper lemma files.

## Status Tracking

- [ ] #1 - Identity eigenvalues
- [ ] #2 - Scalar multiplication
- [ ] #3 - Negation
- [ ] #4 - Transpose
- [ ] #5 - Addition bound
- [ ] #6 - Rayleigh maximum
- [ ] #7 - Matrix powers

## Related Mathlib

Existing eigenvalue infrastructure we're building on:
- `Mathlib.LinearAlgebra.Matrix.Spectrum` - core spectral theorem
- `Mathlib.Analysis.InnerProductSpace.Rayleigh` - Rayleigh quotient theory
- `Mathlib.Analysis.InnerProductSpace.Spectrum` - linear map eigenvalues

## Contribution Path

If we prove these lemmas, they should be:
1. First proven in `PCP/Spectral/Matrix.lean` or a new `PCP/Spectral/EigenvalueOps.lean`
2. Tested in our use cases
3. Generalized and submitted to mathlib as PR (if generally useful)
