import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Rat.Defs
import PCP.Codes.Unit01_HammingDistance.API

/-!
# Relative Hamming Distance

This file defines the relative (normalized) Hamming distance.

## Main definitions

* `relativeDistance x y`: The Hamming distance normalized by vector length

## Main results

* `relativeDistance_mem_unit_interval`: Relative distance is in [0,1]
* `relativeDistance_comm`: Symmetry
* `relativeDistance_eq_zero_iff`: Zero distance iff equal (for n > 0)
* `relativeDistance_triangle`: Triangle inequality

-/

namespace Codes.Unit02

open Codes.Unit01

variable {n : ℕ} {α : Type*} [DecidableEq α]

/-- The relative Hamming distance: Hamming distance divided by vector length. -/
def relativeDistance (x y : Fin n → α) : ℚ :=
  if n = 0 then 0 else (hammingDist x y : ℚ) / n

/-- Relative distance is well-defined. -/
lemma relativeDistance_def (x y : Fin n → α) :
    relativeDistance x y = if n = 0 then 0 else (hammingDist x y : ℚ) / n := rfl

/-- Relative distance when n > 0. -/
lemma relativeDistance_of_pos (x y : Fin n → α) (hn : 0 < n) :
    relativeDistance x y = (hammingDist x y : ℚ) / n := by
  unfold relativeDistance
  simp [hn.ne']

/-- Relative distance is non-negative. -/
lemma relativeDistance_nonneg (x y : Fin n → α) :
    0 ≤ relativeDistance x y := by
  unfold relativeDistance
  split_ifs
  · rfl
  · apply div_nonneg
    · exact Nat.cast_nonneg _
    · exact Nat.cast_pos.mpr (Nat.pos_of_ne_zero ‹_›)

/-- Relative distance is at most 1. -/
lemma relativeDistance_le_one (x y : Fin n → α) :
    relativeDistance x y ≤ 1 := by
  unfold relativeDistance
  split_ifs with h
  · norm_num
  · rw [div_le_one]
    · norm_cast
      exact hammingDist_le_length x y
    · exact Nat.cast_pos.mpr (Nat.pos_of_ne_zero h)

/-- Relative distance is in [0,1]. -/
lemma relativeDistance_mem_unit_interval (x y : Fin n → α) :
    0 ≤ relativeDistance x y ∧ relativeDistance x y ≤ 1 :=
  ⟨relativeDistance_nonneg x y, relativeDistance_le_one x y⟩

/-- Relative distance to self is zero. -/
lemma relativeDistance_self (x : Fin n → α) :
    relativeDistance x x = 0 := by
  unfold relativeDistance
  split_ifs
  · rfl
  · simp [hammingDist_self]

/-- Relative distance is symmetric. -/
lemma relativeDistance_comm (x y : Fin n → α) :
    relativeDistance x y = relativeDistance y x := by
  unfold relativeDistance
  congr 1
  exact hammingDist_comm x y

/-- Zero relative distance implies equal vectors (when n > 0). -/
lemma eq_of_relativeDistance_eq_zero (x y : Fin n → α) (hn : 0 < n)
    (h : relativeDistance x y = 0) :
    x = y := by
  rw [relativeDistance_of_pos x y hn] at h
  have : (hammingDist x y : ℚ) = 0 := by
    have hn' : (0 : ℚ) < n := Nat.cast_pos.mpr hn
    exact (div_eq_zero_iff hn'.ne').mp h
  norm_cast at this
  exact eq_of_hammingDist_eq_zero x y this

/-- Zero relative distance iff vectors are equal (when n > 0). -/
lemma relativeDistance_eq_zero_iff (x y : Fin n → α) (hn : 0 < n) :
    relativeDistance x y = 0 ↔ x = y := by
  constructor
  · exact eq_of_relativeDistance_eq_zero x y hn
  · intro h
    subst h
    exact relativeDistance_self x

/-- Triangle inequality for relative distance. -/
lemma relativeDistance_triangle (x y z : Fin n → α) :
    relativeDistance x z ≤ relativeDistance x y + relativeDistance y z := by
  unfold relativeDistance
  split_ifs with h
  · norm_num
  · have hn : (0 : ℚ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero h)
    rw [div_add_div_same]
    apply div_le_div_of_nonneg_right
    · norm_cast
      exact hammingDist_triangle x y z
    · exact hn.le

/-- Relative distance equals 1 iff vectors differ in all positions (when n > 0). -/
lemma relativeDistance_eq_one_iff (x y : Fin n → α) (hn : 0 < n) :
    relativeDistance x y = 1 ↔ hammingDist x y = n := by
  rw [relativeDistance_of_pos x y hn]
  have hn' : (0 : ℚ) < n := Nat.cast_pos.mpr hn
  constructor
  · intro h
    have : (hammingDist x y : ℚ) = n := by
      field_simp at h
      norm_cast at h
      exact h
    exact Nat.cast_injective this
  · intro h
    field_simp
    norm_cast

/-- Symmetry of relative distance (alternative name). -/
lemma relativeDistance_symm (x y : Fin n → α) :
    relativeDistance x y = relativeDistance y x :=
  relativeDistance_comm x y

end Codes.Unit02
