import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Algebra.Order.Field.Defs
import PCP.Codes.Linear

namespace Codes.Unit01

open Codes

variable {F : Type*} [Field F] [DecidableEq F]
variable {n : ℕ}

/-- Hamming distance is the cardinality of differing positions. -/
lemma hammingDistance_def (u v : Fin n → F) :
    hammingDistance u v = (Finset.univ.filter fun i => u i ≠ v i).card := rfl

/-- Hamming distance is non-negative. -/
lemma hammingDistance_nonneg (u v : Fin n → F) :
    0 ≤ hammingDistance u v := Nat.zero_le _

/-- Hamming distance from a vector to itself is zero. -/
lemma hammingDistance_self (u : Fin n → F) :
    hammingDistance u u = 0 := by
  unfold hammingDistance
  simp

/-- Zero Hamming distance iff vectors are equal (forward direction). -/
lemma eq_of_hammingDistance_eq_zero (u v : Fin n → F) :
    hammingDistance u v = 0 → u = v := by
  intro h
  exact (hammingDistance_eq_zero u v).mp h

/-- Zero Hamming distance iff vectors are equal (backward direction). -/
lemma hammingDistance_eq_zero_of_eq (u v : Fin n → F) :
    u = v → hammingDistance u v = 0 := by
  intro h
  exact (hammingDistance_eq_zero u v).mpr h

/-- Positive Hamming distance for distinct vectors. -/
lemma hammingDistance_pos_of_ne (u v : Fin n → F) (h : u ≠ v) :
    0 < hammingDistance u v := by
  rw [Nat.pos_iff_ne_zero]
  intro hz
  rw [hammingDistance_eq_zero] at hz
  exact h hz

/-- Alternative form: Hamming distance less than n+1. -/
lemma hammingDistance_lt_succ (u v : Fin n → F) :
    hammingDistance u v < n + 1 := by
  have := hammingDistance_le_n u v
  omega

/-- Relative distance is the normalized Hamming distance. -/
lemma relativeDistance_def (u v : Fin n → F) :
    relativeDistance u v = if n = 0 then 0 else (hammingDistance u v : ℚ) / n := rfl

/-- Relative distance is non-negative. -/
lemma relativeDistance_nonneg (u v : Fin n → F) :
    0 ≤ relativeDistance u v := by
  unfold relativeDistance
  split_ifs
  · simp
  · apply div_nonneg <;> simp

/-- Relative distance from a vector to itself is zero. -/
lemma relativeDistance_self (u : Fin n → F) :
    relativeDistance u u = 0 := by
  unfold relativeDistance
  simp [hammingDistance_self]

/-- Zero relative distance iff vectors are equal (forward direction). -/
lemma eq_of_relativeDistance_eq_zero (u v : Fin n → F) :
    relativeDistance u v = 0 → u = v := by
  sorry

/-- Hamming distance on empty vectors is zero. -/
lemma hammingDistance_of_n_eq_zero (u v : Fin 0 → F) :
    hammingDistance u v = 0 := by
  unfold hammingDistance
  simp

/-- Hamming distance is a natural number (trivial). -/
lemma hammingDistance_nat (u v : Fin n → F) :
    ∃ k : ℕ, hammingDistance u v = k := ⟨hammingDistance u v, rfl⟩

/-- Alternative characterization: non-zero distance for distinct vectors. -/
lemma hammingDistance_ne_zero_iff (u v : Fin n → F) :
    hammingDistance u v ≠ 0 ↔ u ≠ v := by
  rw [← not_iff_not]
  push_neg
  exact hammingDistance_eq_zero u v

end Codes.Unit01
