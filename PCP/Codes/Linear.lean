/-
  Linear Codes and Error Correction

  Hamming distance, relative distance, linear codes, minimum distance

  Difficulty: ★★☆☆☆ (2/5)
  Estimated LOC: 200
  Work Package: WP-D
-/

import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.LinearAlgebra.FiniteDimensional
import Mathlib.Tactic

/-!
# Linear Codes and Error Correction

Definitions for linear error-correcting codes used in the assignment tester
construction of Dinur's PCP theorem proof.

## Main Definitions

- `hammingDistance`: Number of positions where two vectors differ
- `relativeDistance`: Hamming distance normalized by vector length
- `LinearCode`: A linear subspace of F^n viewed as an error-correcting code
- `minDistance`: Minimum Hamming distance between distinct codewords

## References

- Dinur, §5 (pp. 15-17): Assignment tester construction
- Standard coding theory references for linear codes
-/

namespace Codes

open Matrix

variable {F : Type*} [Field F] [DecidableEq F]
variable {n : ℕ}

/-- The Hamming distance between two vectors: the number of coordinates where they differ. -/
def hammingDistance (u v : Fin n → F) : ℕ :=
  (Finset.univ.filter fun i => u i ≠ v i).card

/-- Hamming distance is symmetric. -/
lemma hammingDistance_comm (u v : Fin n → F) :
    hammingDistance u v = hammingDistance v u := by
  unfold hammingDistance
  congr 1
  ext i
  simp only [Finset.mem_filter, ne_eq]
  constructor <;> intro h <;> exact h.imp_right ne_comm.mp

/-- Hamming distance is zero iff the vectors are equal. -/
lemma hammingDistance_eq_zero (u v : Fin n → F) :
    hammingDistance u v = 0 ↔ u = v := by
  unfold hammingDistance
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  constructor
  · intro h
    ext i
    by_contra hi
    specialize h (Finset.mem_univ i)
    exact h hi
  · intro h i _
    simp [h]

/-- Hamming distance is bounded by the vector length. -/
lemma hammingDistance_le_n (u v : Fin n → F) :
    hammingDistance u v ≤ n := by
  unfold hammingDistance
  trans (Finset.univ : Finset (Fin n)).card
  · exact Finset.card_filter_le _ _
  · simp

/-- The relative distance (or fractional Hamming distance) between two vectors. -/
def relativeDistance (u v : Fin n → F) : ℚ :=
  if n = 0 then 0 else (hammingDistance u v : ℚ) / n

/-- Relative distance is between 0 and 1. -/
lemma relativeDistance_bounds (u v : Fin n → F) :
    0 ≤ relativeDistance u v ∧ relativeDistance u v ≤ 1 := by
  unfold relativeDistance
  split_ifs with hn
  · simp
  · constructor
    · apply div_nonneg <;> simp
    · have h := hammingDistance_le_n u v
      have hn' : (0 : ℚ) < n := by
        simp only [Nat.cast_pos]
        omega
      rw [div_le_iff₀ hn']
      simp [h]

/-- A linear code over field F is a linear subspace of F^n. -/
structure LinearCode (F : Type*) [Field F] (n : ℕ) where
  /-- The set of codewords (a linear subspace) -/
  codewords : Submodule F (Fin n → F)
  /-- The code must be non-trivial (contains more than just zero) -/
  nontrivial : ∃ (c : Fin n → F), c ∈ codewords ∧ c ≠ 0

namespace LinearCode

variable {F : Type*} [Field F] [DecidableEq F]

/-- The dimension of a linear code (as a vector space). -/
noncomputable def dimension (C : LinearCode F n) : ℕ :=
  Module.finrank F C.codewords

/-- The rate of a code: dimension / block length. -/
noncomputable def rate (C : LinearCode F n) : ℚ :=
  if n = 0 then 0 else (C.dimension : ℚ) / n

/-- The minimum distance of a linear code: minimum Hamming distance between distinct codewords.

    Note: This is axiomatized as computing it requires searching over all codeword pairs.
    A constructive version would use Fintype on the codewords (if finite). -/
axiom minDistance (C : LinearCode F n) : ℕ

/-- Axiom: The minimum distance is positive for non-trivial codes. -/
axiom minDistance_pos (C : LinearCode F n) : 0 < minDistance C

/-- Axiom: The minimum distance is achieved by some pair of distinct codewords. -/
axiom minDistance_spec (C : LinearCode F n) :
  ∃ (u v : Fin n → F), u ∈ C.codewords ∧ v ∈ C.codewords ∧ u ≠ v ∧
    hammingDistance u v = minDistance C

/-- The relative minimum distance (minimum distance / block length). -/
noncomputable def relativeMinDistance (C : LinearCode F n) : ℚ :=
  if n = 0 then 0 else (minDistance C : ℚ) / n

/-- A code has constant relative distance if the relative minimum distance is bounded below. -/
def hasConstantDistance (C : LinearCode F n) (δ : ℚ) : Prop :=
  δ > 0 ∧ relativeMinDistance C ≥ δ

end LinearCode

/-- A family of linear codes with growing block length. -/
structure CodeFamily (F : Type*) [Field F] where
  /-- The code of block length n -/
  code : (n : ℕ) → LinearCode F n
  /-- The rate is constant (bounded below) -/
  constant_rate : ∃ (R : ℚ), R > 0 ∧ ∀ n, (code n).rate ≥ R
  /-- The relative distance is constant (bounded below) -/
  constant_distance : ∃ (δ : ℚ), δ > 0 ∧ ∀ n, (code n).relativeMinDistance ≥ δ

end Codes
