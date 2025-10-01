/-
  Constraint Graph Examples

  Concrete instances to validate definitions
-/

import PCP.ConstraintGraph.Defs

/-!
# Constraint Graph Examples

Simple examples to test that our definitions work correctly.
-/

namespace Examples

-- Simple vertex and alphabet types
abbrev V3 := Fin 3  -- 3 vertices
abbrev Bool2 := Bool  -- Binary alphabet

/-!
## Example 1: Triangle of equality constraints

Three vertices where each pair must be equal.
This is SATISFIABLE (all vertices can have the same value).
-/

-- Equality relation
def eq_rel : BinRel Bool2 where
  carrier := fun (a, b) => a = b
  decidable_carrier := by infer_instance

-- Create edges for a triangle
def triangle_edge_01 : EdgeC V3 Bool2 := {
  e := s(0, 1)
  rel := eq_rel
}

def triangle_edge_12 : EdgeC V3 Bool2 := {
  e := s(1, 2)
  rel := eq_rel
}

def triangle_edge_02 : EdgeC V3 Bool2 := {
  e := s(0, 2)
  rel := eq_rel
}

-- The triangle CSP
def triangle_csp : BinaryCSP V3 Bool2 := {
  E := {triangle_edge_01, triangle_edge_12, triangle_edge_02}
  nonempty := by simp [Finset.card_insert_of_not_mem]; norm_num
}

-- All-true assignment
def all_true : Assignment V3 Bool2 := fun _ => true

-- All-false assignment
def all_false : Assignment V3 Bool2 := fun _ => false

-- Test: all_true satisfies the triangle
example : EdgeC.sat all_true triangle_edge_01 := by
  unfold EdgeC.sat all_true triangle_edge_01 eq_rel
  simp
  use 0, 1
  simp [Sym2.eq_iff]

-- Test: satFrac for all_true should be 1
example : triangle_csp.satFrac all_true = 1 := by
  unfold BinaryCSP.satFrac triangle_csp all_true
  simp [EdgeC.sat, triangle_edge_01, triangle_edge_12, triangle_edge_02, eq_rel]
  sorry  -- Should be provable but needs careful Finset manipulation

/-!
## Example 2: Inequality constraint

Two vertices that must be DIFFERENT.
-/

def neq_rel : BinRel Bool2 where
  carrier := fun (a, b) => a ≠ b
  decidable_carrier := by infer_instance

def neq_edge : EdgeC (Fin 2) Bool2 := {
  e := s(0, 1)
  rel := neq_rel
}

def neq_csp : BinaryCSP (Fin 2) Bool2 := {
  E := {neq_edge}
  nonempty := by simp
}

-- Assignment where both vertices are true
def both_true : Assignment (Fin 2) Bool2 := fun _ => true

-- Assignment where they differ
def differ : Assignment (Fin 2) Bool2 := fun i => if i = 0 then true else false

-- Test: both_true does NOT satisfy the inequality
example : ¬EdgeC.sat both_true neq_edge := by
  unfold EdgeC.sat both_true neq_edge neq_rel
  simp
  intro u v _
  by_cases h : u = 0
  · simp [h]
    intro h2
    by_cases h3 : v = 0 <;> simp [h3]
  · sorry

-- Test: differ DOES satisfy the inequality
example : EdgeC.sat differ neq_edge := by
  unfold EdgeC.sat differ neq_edge neq_rel
  simp
  use 0, 1
  simp [Sym2.eq_iff]

/-!
## Example 3: Over-constrained system (UNSAT)

A triangle where edges alternate between equality and inequality.
This should be UNSATISFIABLE with a binary alphabet.
-/

def unsat_edge_01 : EdgeC V3 Bool2 := {
  e := s(0, 1)
  rel := eq_rel  -- 0 = 1
}

def unsat_edge_12 : EdgeC V3 Bool2 := {
  e := s(1, 2)
  rel := neq_rel  -- 1 ≠ 2
}

def unsat_edge_02 : EdgeC V3 Bool2 := {
  e := s(0, 2)
  rel := eq_rel  -- 0 = 2
}

def unsat_csp : BinaryCSP V3 Bool2 := {
  E := {unsat_edge_01, unsat_edge_12, unsat_edge_02}
  nonempty := by simp [Finset.card_insert_of_not_mem]; norm_num
}

-- Test: No assignment can satisfy all constraints
-- If 0=1 and 0=2, then 1=2, contradicting 1≠2
theorem unsat_csp_is_unsat : ∀ σ : Assignment V3 Bool2,
  unsat_csp.satFrac σ < 1 := by
  intro σ
  sorry  -- Should be provable by case analysis on σ values

/-!
## Example 4: Degree computation

Check that degree function works correctly.
-/

-- Triangle has degree 2 for each vertex
example : triangle_csp.degree 0 = 2 := by
  unfold BinaryCSP.degree triangle_csp
  sorry  -- Should count edges involving vertex 0

example : triangle_csp.IsRegular 2 := by
  unfold BinaryCSP.IsRegular
  intro v
  sorry  -- Each vertex has degree 2

/-!
## Helper: Compute satFrac manually

For debugging and understanding.
-/

def count_satisfied (G : BinaryCSP V3 Bool2) (σ : Assignment V3 Bool2) : ℕ :=
  (G.E.filter (fun ec => EdgeC.sat σ ec)).card

example : count_satisfied triangle_csp all_true = 3 := by
  unfold count_satisfied triangle_csp all_true
  sorry  -- All 3 edges satisfied

example : count_satisfied unsat_csp all_true ≤ 2 := by
  unfold count_satisfied unsat_csp all_true
  sorry  -- At most 2 of 3 edges can be satisfied

end Examples
