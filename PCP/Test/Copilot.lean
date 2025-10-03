import LeanCopilot

/-- Test theorem to verify LeanCopilot is working -/
theorem test_add_comm (a b : Nat) : a + b = b + a := by
  -- suggest_tactics should provide suggestions here in VSCode
  -- For now, just complete the proof
  omega
