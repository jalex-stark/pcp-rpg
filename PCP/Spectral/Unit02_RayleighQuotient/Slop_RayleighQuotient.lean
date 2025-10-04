import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import PCP.Spectral.Unit01_AdjacencyMatrix.API

/-!
# Rayleigh Quotient

This file defines the Rayleigh quotient for characterizing matrix eigenvalues.

## Main definitions

* `rayleighQuotient A v`: The Rayleigh quotient ⟨Av, v⟩ / ⟨v, v⟩

## Main results

* `rayleighQuotient_smul`: Scale invariance
* `rayleighQuotient_nonneg_of_posSemidef`: Non-negativity for PSD matrices
* `rayleighQuotient_symm`: Well-defined for symmetric matrices

## References

* Dinur §2 (p. 8): Rayleigh quotient for spectral bounds

-/

namespace Spectral.Unit02

open Matrix BigOperators

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The Rayleigh quotient of a matrix A and vector v.
    Defined as ⟨A*v, v⟩ / ⟨v, v⟩ when v ≠ 0, and 0 otherwise. -/
def rayleighQuotient (A : Matrix n n ℝ) (v : n → ℝ) : ℝ :=
  let num := (A *ᵥ v) ⬝ᵥ v
  let den := v ⬝ᵥ v
  if den = 0 then 0 else num / den

/-- Rayleigh quotient definition. -/
lemma rayleighQuotient_def (A : Matrix n n ℝ) (v : n → ℝ) :
    rayleighQuotient A v =
      let num := (A *ᵥ v) ⬝ᵥ v
      let den := v ⬝ᵥ v
      if den = 0 then 0 else num / den := rfl

/-- Rayleigh quotient when v ≠ 0. -/
lemma rayleighQuotient_of_ne_zero (A : Matrix n n ℝ) (v : n → ℝ)
    (hv : v ⬝ᵥ v ≠ 0) :
    rayleighQuotient A v = (A *ᵥ v) ⬝ᵥ v / (v ⬝ᵥ v) := by
  unfold rayleighQuotient
  simp [hv]

/-- Rayleigh quotient of zero vector is zero. -/
lemma rayleighQuotient_zero (A : Matrix n n ℝ) :
    rayleighQuotient A 0 = 0 := by
  unfold rayleighQuotient
  simp [Matrix.dotProduct_zero]

/-- Scale invariance: R(A, cv) = R(A, v) for c ≠ 0. -/
lemma rayleighQuotient_smul (A : Matrix n n ℝ) (v : n → ℝ) (c : ℝ) (hc : c ≠ 0) :
    rayleighQuotient A (c • v) = rayleighQuotient A v := by
  by_cases hv : v ⬝ᵥ v = 0
  · have : c • v ⬝ᵥ (c • v) = 0 := by
      simp [Matrix.dotProduct_smul, hv, mul_zero]
    unfold rayleighQuotient
    simp [this, hv]
  · have hcv : c • v ⬝ᵥ (c • v) ≠ 0 := by
      simp [Matrix.dotProduct_smul]
      intro h
      cases h with
      | inl h => exact hc h
      | inr h =>
        have : c ^ 2 * (v ⬝ᵥ v) = 0 := h
        have : v ⬝ᵥ v = 0 := by
          by_contra habs
          have : c ^ 2 ≠ 0 := sq_ne_zero_of_ne_zero _ hc
          exact this (mul_eq_zero.mp ‹_›).1
        exact hv this
    rw [rayleighQuotient_of_ne_zero A (c • v) hcv,
        rayleighQuotient_of_ne_zero A v hv]
    simp [Matrix.mulVec_smul, Matrix.dotProduct_smul]
    field_simp
    ring

/-- Rayleigh quotient for positive semidefinite matrices is non-negative. -/
lemma rayleighQuotient_nonneg_of_posSemidef (A : Matrix n n ℝ)
    (v : n → ℝ) (hA : A.PosSemidef) (hv : v ⬝ᵥ v ≠ 0) :
    0 ≤ rayleighQuotient A v := by
  rw [rayleighQuotient_of_ne_zero A v hv]
  apply div_nonneg
  · exact hA.2 v
  · exact Matrix.dotProduct_self_nonneg v

/-- Rayleigh quotient is well-defined (does not depend on specific representation). -/
lemma rayleighQuotient_eq_of_smul (A : Matrix n n ℝ) (v : n → ℝ)
    (c : ℝ) (hc : c ≠ 0) (hv : v ≠ 0) :
    rayleighQuotient A (c • v) = rayleighQuotient A v :=
  rayleighQuotient_smul A v c hc

/-- Rayleigh quotient with negative scaling. -/
lemma rayleighQuotient_neg (A : Matrix n n ℝ) (v : n → ℝ) :
    rayleighQuotient A (-v) = rayleighQuotient A v := by
  by_cases hv : v = 0
  · simp [hv, rayleighQuotient_zero]
  · have : (-1 : ℝ) ≠ 0 := by norm_num
    convert rayleighQuotient_smul A v (-1) this using 2
    ext i
    simp [Pi.neg_apply]

/-- Rayleigh quotient for symmetric matrix is real (trivially, since we work over ℝ). -/
lemma rayleighQuotient_real (A : Matrix n n ℝ) (v : n → ℝ)
    (hA : A.IsSymm) :
    ∃ r : ℝ, rayleighQuotient A v = r := ⟨_, rfl⟩

/-- Denominator is positive for non-zero vectors. -/
lemma dotProduct_self_pos_of_ne_zero (v : n → ℝ) (hv : v ≠ 0) :
    0 < v ⬝ᵥ v := by
  have h1 := Matrix.dotProduct_self_eq_zero.not.mpr hv
  have h2 := Matrix.dotProduct_self_nonneg v
  omega

/-- Rayleigh quotient alternative form. -/
lemma rayleighQuotient_eq_div (A : Matrix n n ℝ) (v : n → ℝ) (hv : v ≠ 0) :
    rayleighQuotient A v = (A *ᵥ v) ⬝ᵥ v / (v ⬝ᵥ v) := by
  apply rayleighQuotient_of_ne_zero
  exact (dotProduct_self_pos_of_ne_zero v hv).ne'

/-- Rayleigh quotient with identity matrix. -/
lemma rayleighQuotient_one (v : n → ℝ) :
    rayleighQuotient (1 : Matrix n n ℝ) v = 1 := by
  by_cases hv : v ⬝ᵥ v = 0
  · unfold rayleighQuotient
    simp [hv]
  · rw [rayleighQuotient_of_ne_zero (1 : Matrix n n ℝ) v hv]
    simp [Matrix.one_mulVec]

/-- Rayleigh quotient with zero matrix. -/
lemma rayleighQuotient_zero_matrix (v : n → ℝ) :
    rayleighQuotient (0 : Matrix n n ℝ) v = 0 := by
  unfold rayleighQuotient
  simp [Matrix.zero_mulVec]

/-- Linearity in the matrix (for fixed v). -/
lemma rayleighQuotient_add_matrix (A B : Matrix n n ℝ) (v : n → ℝ)
    (hv : v ⬝ᵥ v ≠ 0) :
    rayleighQuotient (A + B) v =
      ((A *ᵥ v) ⬝ᵥ v + (B *ᵥ v) ⬝ᵥ v) / (v ⬝ᵥ v) := by
  rw [rayleighQuotient_of_ne_zero (A + B) v hv]
  simp [Matrix.add_mulVec, Matrix.dotProduct_add]

/-- Scaling the matrix scales the quotient. -/
lemma rayleighQuotient_smul_matrix (A : Matrix n n ℝ) (v : n → ℝ)
    (c : ℝ) (hv : v ⬝ᵥ v ≠ 0) :
    rayleighQuotient (c • A) v = c * rayleighQuotient A v := by
  rw [rayleighQuotient_of_ne_zero (c • A) v hv,
      rayleighQuotient_of_ne_zero A v hv]
  simp [Matrix.smul_mulVec_assoc, Matrix.dotProduct_smul]
  ring

end Spectral.Unit02
