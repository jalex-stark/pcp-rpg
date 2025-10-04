# Eigenvalue Theory Available in Mathlib

## ✅ What Exists

### 1. **Mathlib.LinearAlgebra.Matrix.Spectrum**
Main spectral theory for Hermitian/symmetric matrices:

- `Matrix.IsHermitian.eigenvalues : n → ℝ` - the eigenvalues (indexed by matrix indices)
- `Matrix.IsHermitian.eigenvectorBasis` - orthonormal basis of eigenvectors
- `Matrix.IsHermitian.spectral_theorem` - **A = U D U*** (diagonalization)
- `Matrix.IsHermitian.mulVec_eigenvectorBasis` - **Av = λv** for eigenvectors
- `Matrix.IsHermitian.eigenvalues_mem_spectrum_real` - eigenvalues are in spectrum
- `Matrix.IsHermitian.det_eq_prod_eigenvalues` - det(A) = ∏ λᵢ

### 2. **Mathlib.Analysis.InnerProductSpace.Spectrum**  
General linear operator spectral theory:

- `LinearMap.IsSymmetric.conj_eigenvalue_eq_self` - **eigenvalues are real**
- `LinearMap.IsSymmetric.orthogonalFamily_eigenspaces` - **eigenspaces are orthogonal**
- `LinearMap.IsSymmetric.diagonalization` - isometry to direct sum of eigenspaces
- `LinearMap.IsSymmetric.eigenvalues` - sorted eigenvalues (decreasing order)
- `LinearMap.IsSymmetric.eigenvectorBasis` - orthonormal eigenvector basis
- `LinearMap.eigenvalue_nonneg_of_nonneg` - PSD → non-negative eigenvalues
- `LinearMap.eigenvalue_pos_of_pos` - PD → positive eigenvalues

### 3. **Mathlib.Analysis.InnerProductSpace.Rayleigh**
Rayleigh quotient variational characterization:

- `rayleigh T x = ⟪T x, x⟫ / ‖x‖²` definition
- `rayleigh_smul` - scale invariance
- `iSup_rayleigh_eq_iSup_rayleigh_sphere` - supremum characterization
- `hasEigenvector_of_isMaxOn` - **max Rayleigh quotient → eigenvector**
- `hasEigenvector_of_isMinOn` - **min Rayleigh quotient → eigenvector**  
- `hasEigenvalue_iSup_of_finiteDimensional` - **largest eigenvalue exists**
- `hasEigenvalue_iInf_of_finiteDimensional` - **smallest eigenvalue exists**

## 🔧 What We Can Use

For our spectral work:

1. **Import directly**: `import Mathlib.LinearAlgebra.Matrix.Spectrum`
2. Use `Matrix.IsHermitian` (which includes `Matrix.IsSymm` for real matrices)
3. Get eigenvalues: `hA.eigenvalues : n → ℝ`
4. Get eigenvectors: `hA.eigenvectorBasis`
5. Rayleigh quotient bounds available

## 📝 What to Update

Our **Unit03_OperatorNorm** can now:

1. Use `Matrix.IsHermitian.eigenvalues` instead of defining from scratch
2. Connect `spectralRadius` to `⨆ i, |hA.eigenvalues i|`
3. Use Rayleigh quotient variational principle from mathlib
4. Prove operator norm = spectral radius using existing infrastructure

## 🔍 Additional Findings

### Available in Mathlib:
- `Matrix.IsHermitian.eigenvalues_eq_zero_iff` - eigenvalues all zero iff matrix is zero
  - **Use for**: `spectralRadius_zero` lemma
- `Matrix.IsHermitian.trace_eq_sum_eigenvalues` - trace equals sum of eigenvalues
- `Matrix.IsHermitian.det_eq_prod_eigenvalues` - determinant equals product of eigenvalues

### NOT in Mathlib (need to prove):
- Eigenvalues of identity matrix (all equal to 1)
- Eigenvalues under scalar multiplication: `(c • A).eigenvalues = c • A.eigenvalues`
- Eigenvalues under negation: `(-A).eigenvalues i = -(A.eigenvalues i)`
- Eigenvalues under transpose (for Hermitian, should be unchanged)

These would need to be proven using the spectral theorem and properties of matrix operations.

## Example Usage

```lean
import Mathlib.LinearAlgebra.Matrix.Spectrum

variable {n : Type*} [Fintype n] [DecidableEq n]
variable (A : Matrix n n ℝ) (hA : A.IsHermitian)

-- Eigenvalues exist
#check hA.eigenvalues : n → ℝ

-- Spectral decomposition
#check hA.spectral_theorem : A = U * diagonal λᵢ * U*

-- Eigenvector property  
example (i : n) : A *ᵥ (hA.eigenvectorBasis i) = hA.eigenvalues i • (hA.eigenvectorBasis i) :=
  hA.mulVec_eigenvectorBasis i
```
