-- Operator norm and spectral radius for matrices
import Mathlib.LinearAlgebra.Matrix.Spectrum
import Mathlib.Analysis.InnerProductSpace.Rayleigh
import PCP.Spectral.Matrix

namespace Spectral.Unit03

open Matrix BigOperators Finset

variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]

/-- The spectral radius of a Hermitian matrix (maximum absolute eigenvalue). -/
noncomputable def spectralRadius (A : Matrix n n ℝ) (hA : A.IsHermitian) : ℝ :=
  univ.sup' univ_nonempty (fun i => |hA.eigenvalues i|)

/-- Spectral radius is non-negative. -/
lemma spectralRadius_nonneg (A : Matrix n n ℝ) (hA : A.IsHermitian) :
    0 ≤ spectralRadius A hA := by
  unfold spectralRadius
  trans (|hA.eigenvalues (Classical.arbitrary n)|)
  · exact abs_nonneg _
  · exact Finset.le_sup' (fun j => |hA.eigenvalues j|) (mem_univ _)

/-- Spectral radius equals maximum absolute eigenvalue (definitional). -/
lemma spectralRadius_eq_max_abs_eigenvalue (A : Matrix n n ℝ) (hA : A.IsHermitian) :
    spectralRadius A hA = univ.sup' univ_nonempty (fun i => |hA.eigenvalues i|) := by
  rfl

/-- Zero matrix has zero spectral radius. -/
lemma spectralRadius_zero (h0 : (0 : Matrix n n ℝ).IsHermitian) :
    spectralRadius 0 h0 = 0 := by
  unfold spectralRadius
  have : h0.eigenvalues = 0 := h0.eigenvalues_eq_zero_iff.mpr rfl
  simp [this]

/-- Spectral radius of identity matrix equals 1. -/
lemma spectralRadius_one (h1 : (1 : Matrix n n ℝ).IsHermitian) :
    spectralRadius 1 h1 = 1 := by
  unfold spectralRadius
  sorry -- All eigenvalues of identity are 1

/-- Spectral radius scales with positive scalar multiplication. -/
lemma spectralRadius_smul (A : Matrix n n ℝ) (hA : A.IsHermitian) (c : ℝ) (hc : 0 ≤ c)
    (hcA : (c • A).IsHermitian) :
    spectralRadius (c • A) hcA = c * spectralRadius A hA := by
  unfold spectralRadius
  sorry -- Eigenvalues scale: λ(cA) = c·λ(A)

/-- Spectral radius is invariant under transpose for Hermitian matrices. -/
lemma spectralRadius_transpose (A : Matrix n n ℝ) (hA : A.IsHermitian) (hAT : Aᵀ.IsHermitian) :
    spectralRadius Aᵀ hAT = spectralRadius A hA := by
  unfold spectralRadius
  sorry -- Eigenvalues unchanged under transpose for Hermitian

/-- Spectral radius of negative matrix. -/
lemma spectralRadius_neg (A : Matrix n n ℝ) (hA : A.IsHermitian) (hNA : (-A).IsHermitian) :
    spectralRadius (-A) hNA = spectralRadius A hA := by
  unfold spectralRadius
  sorry -- Eigenvalues of -A are negatives of eigenvalues of A, |−λ| = |λ|

/-- Eigenvalues are bounded by spectral radius. -/
lemma eigenvalue_abs_le_spectralRadius (A : Matrix n n ℝ) (hA : A.IsHermitian) (i : n) :
    |hA.eigenvalues i| ≤ spectralRadius A hA := by
  unfold spectralRadius
  exact Finset.le_sup' (fun j => |hA.eigenvalues j|) (mem_univ i)

/-- Spectral radius achieved by some eigenvalue. -/
lemma exists_eigenvalue_eq_spectralRadius (A : Matrix n n ℝ) (hA : A.IsHermitian) :
    ∃ i : n, |hA.eigenvalues i| = spectralRadius A hA := by
  unfold spectralRadius
  have := Finset.exists_mem_eq_sup' univ_nonempty (fun j => |hA.eigenvalues j|)
  obtain ⟨i, hi, heq⟩ := this
  exact ⟨i, heq.symm⟩

/-- For Hermitian matrices, spectral radius connects to Rayleigh quotient. -/
lemma spectralRadius_eq_rayleigh_sup (A : Matrix n n ℝ) (hA : A.IsHermitian) :
    spectralRadius A hA = ⨆ (v : n → ℝ) (_ : v ≠ 0), |(A *ᵥ v) ⬝ᵥ v / (v ⬝ᵥ v)| := by
  sorry -- Uses Rayleigh quotient characterization from mathlib

end Spectral.Unit03
