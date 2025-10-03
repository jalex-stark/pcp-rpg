import LeanCopilot

-- Simple test theorem to verify LeanCopilot is working
theorem test_add_comm (a b : Nat) : a + b = b + a := by
  suggest_tactics
  sorry
