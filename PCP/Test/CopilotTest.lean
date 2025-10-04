import LeanCopilot
import Mathlib.Tactic

/-- Simple test for LeanCopilot - it works! -/
theorem test_add_comm_copilot (a b : Nat) : a + b = b + a := by
  rw [add_comm]  -- ✓ Suggested by LeanCopilot!
