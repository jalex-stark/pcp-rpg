/-
  SAT and NP-completeness

  Boolean satisfiability problem and Cook-Levin theorem

  Difficulty: ★★★☆☆ (3/5)
  Estimated LOC: 200
  Work Package: WP-A

  Notes: May be available in mathlib complexity theory library
-/

import Mathlib.Data.Bool.Basic
import Mathlib.Data.List.Basic
import Mathlib.Data.Fintype.Basic
import PCP.Language

/-!
# SAT and NP-completeness

Boolean satisfiability problem, CNF formulas, and Cook-Levin theorem.
-/

/-- A Boolean variable (identified by a natural number). -/
abbrev BoolVar := ℕ

/-- A literal is a variable or its negation. -/
inductive Literal where
  | pos : BoolVar → Literal
  | neg : BoolVar → Literal
  deriving DecidableEq

/-- A clause is a disjunction of literals. -/
abbrev Clause := List Literal

/-- A CNF formula is a conjunction of clauses. -/
abbrev CNF := List Clause

/-- An assignment of truth values to variables. -/
abbrev BoolAssignment := BoolVar → Bool

namespace Literal

/-- Evaluate a literal under an assignment. -/
def eval (τ : BoolAssignment) : Literal → Bool
  | pos v => τ v
  | neg v => !(τ v)

end Literal

namespace Clause

/-- A clause is satisfied if at least one literal is true. -/
def sat (τ : BoolAssignment) (c : Clause) : Bool :=
  c.any (Literal.eval τ)

end Clause

namespace CNF

/-- A CNF formula is satisfied if all clauses are satisfied. -/
def sat (τ : BoolAssignment) (φ : CNF) : Bool :=
  φ.all (Clause.sat τ)

/-- A formula is satisfiable if there exists a satisfying assignment. -/
def satisfiable (φ : CNF) : Prop :=
  ∃ τ : BoolAssignment, sat τ φ = true

/-- The SAT language: encodings of satisfiable CNF formulas. -/
def SAT_Language : Language :=
  {x : Bitstring | ∃ φ : CNF, satisfiable φ}  -- Simplified encoding

/-- 3-SAT: each clause has exactly 3 literals. -/
def is3CNF (φ : CNF) : Prop :=
  ∀ c ∈ φ, c.length = 3

def ThreeSAT_Language : Language :=
  {x : Bitstring | ∃ φ : CNF, is3CNF φ ∧ satisfiable φ}

end CNF

/-!
## NP-completeness

Polynomial-time reductions and NP-hard problems.
-/

/-- Polynomial-time many-one reduction. -/
axiom ReducesPolyTime (L₁ L₂ : Language) : Prop

notation:50 L₁ " ≤ₚ " L₂ => ReducesPolyTime L₁ L₂

/-- A language is NP-hard if all NP problems reduce to it. -/
def NPHard (L : Language) : Prop :=
  ∀ L' ∈ NP_class, L' ≤ₚ L

/-- A language is NP-complete if it's in NP and NP-hard. -/
def NPComplete (L : Language) : Prop :=
  L ∈ NP_class ∧ NPHard L

/-!
## Cook-Levin Theorem

SAT is NP-complete.
-/

/-- SAT is in NP (easy direction). -/
theorem SAT_in_NP : CNF.SAT_Language ∈ NP_class := by
  sorry

/-- SAT is NP-hard (Cook-Levin theorem). -/
theorem SAT_is_NPhard : NPHard CNF.SAT_Language := by
  sorry

/-- SAT is NP-complete. -/
theorem SAT_is_NPcomplete : NPComplete CNF.SAT_Language :=
  ⟨SAT_in_NP, SAT_is_NPhard⟩

/-- 3-SAT is NP-complete (via reduction from SAT). -/
theorem ThreeSAT_is_NPcomplete : NPComplete CNF.ThreeSAT_Language := by
  sorry

-- Re-export NP_class for use in other files
axiom NP_class : Set Language
