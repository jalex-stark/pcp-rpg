/-
  Basic definitions and helper lemmas for PCP formalization.

  Simple theorems for testing the orchestrator system.
-/

import Mathlib.Tactic

namespace PCP.Basic

-- Simple test theorems for orchestrator

-- These have correct proofs (for testing)
theorem nat_add_zero_solved (n : ℕ) : n + 0 = n := by simp

theorem nat_zero_add_solved (n : ℕ) : 0 + n = n := by simp

-- These have sorry (for orchestrator to solve)
theorem nat_add_zero (n : ℕ) : n + 0 = n := by
  sorry

theorem nat_zero_add (n : ℕ) : 0 + n = n := by
  sorry

theorem nat_add_comm (m n : ℕ) : m + n = n + m := by
  sorry

theorem nat_mul_one (n : ℕ) : n * 1 = n := by
  sorry

theorem list_append_nil {α : Type*} (l : List α) : l ++ [] = l := by
  sorry

theorem list_nil_append {α : Type*} (l : List α) : [] ++ l = l := by
  sorry

end PCP.Basic