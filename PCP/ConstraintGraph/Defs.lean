/-
  Constraint Graph Definitions
  
  Binary CSP, assignments, satisfaction, UNSAT value
  
  Difficulty: ★★☆☆☆ (2/5)
  Estimated LOC: 200
  Work Package: WP-A
-/

import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Sym.Sym2
import Mathlib.Order.Bounds.Basic

/-!
# Constraint Graph Definitions

Binary CSP (Constraint Satisfaction Problem), assignments, satisfaction, and UNSAT value.

This file defines the core constraint graph structures used in Dinur's gap amplification proof.
-/

/-- Binary constraint on alphabet α: a decidable subset of α × α. -/
structure BinRel (α : Type*) where
  /-- The constraint relation -/
  carrier : α × α → Prop
  /-- The constraint must be decidable -/
  [decidable_carrier : DecidablePred carrier]

attribute [instance] BinRel.decidable_carrier

/-- A labeled edge with a binary constraint. -/
structure EdgeC (V α : Type*) where
  /-- The edge (unordered pair of vertices) -/
  e : Sym2 V
  /-- The constraint on this edge -/
  rel : BinRel α

/-- An assignment maps vertices to alphabet symbols. -/
abbrev Assignment (V α : Type*) := V → α

/-- Finite binary CSP on vertices V over alphabet α. -/
structure BinaryCSP (V α : Type*) [Fintype V] [Fintype α] where
  /-- Set of constrained edges -/
  E : Finset (EdgeC V α)
  /-- The CSP must have at least one constraint -/
  nonempty : 0 < E.card

namespace EdgeC

/-- Satisfaction of a single constrained edge by an assignment. -/
def sat {V α : Type*} [DecidableEq V] (σ : Assignment V α) (ec : EdgeC V α) : Prop :=
  ∃ (u v : V), ec.e = s(u, v) ∧ ec.rel.carrier (σ u, σ v)

/-- Decidability instance for edge satisfaction. -/
instance sat_decidable {V α : Type*} [DecidableEq V] [Fintype V]
  (σ : Assignment V α) (ec : EdgeC V α) : Decidable (sat σ ec) := by
  unfold sat
  infer_instance

end EdgeC

namespace BinaryCSP

variable {V α : Type*} [Fintype V] [Fintype α] [DecidableEq V]

/-- Fraction of constraints satisfied by an assignment. -/
def satFrac (G : BinaryCSP V α) (σ : Assignment V α) : ℚ :=
  (G.E.filter (fun ec => EdgeC.sat σ ec)).card / G.E.card

/-- The maximum satisfaction fraction over all assignments. -/
def maxSat (G : BinaryCSP V α) : ℚ :=
  (Finset.univ.image (fun σ => satFrac G σ)).sup' (by
    simp [Finset.image_nonempty]
    exact Finset.univ_nonempty) id

/-- UNSAT value: minimum fraction of unsatisfied constraints. -/
def unsat (G : BinaryCSP V α) : ℚ :=
  1 - maxSat G

end BinaryCSP

/-!
## 3-Colorability is NP-hard

Reduction from 3-Colorability to 2-CSP satisfiability (to be formalized).
-/

-- Placeholders for complexity-theoretic reductions
axiom ThreeColor : Type
axiom reduces_poly : Type → Type → Prop
axiom threeColor_to_csp : True
