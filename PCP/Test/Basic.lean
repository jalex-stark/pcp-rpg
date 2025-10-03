import Mathlib.Tactic

/-!
# Basic Test Theorems for Orchestrator

Simple theorems to test LeanDojo integration.
-/

namespace PCP.Test

-- Should be solved by `rfl`
theorem nat_zero_add (n : ℕ) : 0 + n = n := by
  sorry

-- Should be solved by `simp`
theorem nat_add_zero (n : ℕ) : n + 0 = n := by
  sorry

-- Should be solved by `ring`
theorem nat_mul_zero (n : ℕ) : n * 0 = 0 := by
  sorry

-- Should be solved by `ring`
theorem nat_zero_mul (n : ℕ) : 0 * n = 0 := by
  sorry

-- Should be solved by `omega`
theorem nat_sub_self (n : ℕ) : n - n = 0 := by
  sorry

-- Should be solved by `omega`
theorem nat_sub_zero (n : ℕ) : n - 0 = n := by
  sorry

-- More challenging - might need aesop or combination
theorem nat_add_comm (n m : ℕ) : n + m = m + n := by
  sorry

-- Requires induction or existing lemma
theorem nat_add_assoc (n m k : ℕ) : (n + m) + k = n + (m + k) := by
  sorry

end PCP.Test
