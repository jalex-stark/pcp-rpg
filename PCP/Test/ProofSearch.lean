import Mathlib.Tactic

/-!
# Test Theorems for Proof Search

Simple theorems to test LeanCopilot and other automated provers.
-/

/-- Simple arithmetic theorem -/
theorem test_add_comm (a b : Nat) : a + b = b + a := by
  sorry

/-- Rational arithmetic -/
theorem test_rat_div (a b : ℚ) (h : 0 < b) : a / b * b = a := by
  sorry

/-- List append -/
theorem test_list_append (xs ys : List α) : (xs ++ ys).length = xs.length + ys.length := by
  sorry

/-- Finset cardinality -/
theorem test_finset_card (s t : Finset Nat) (h : Disjoint s t) :
  (s ∪ t).card = s.card + t.card := by
  sorry

/-- Simple inequality -/
theorem test_nat_le (n : Nat) : n ≤ n + 1 := by
  sorry
