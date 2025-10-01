/-
  Constraint Graph Definitions
  
  Binary CSP, assignments, satisfaction, UNSAT value
  
  Difficulty: ★★☆☆☆ (2/5)
  Estimated LOC: 200
  Work Package: WP-A
-/

import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Sym.Sym2
import Mathlib.Order.Bounds.Basic
import Mathlib.Tactic

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
axiom maxSat (G : BinaryCSP V α) : ℚ

/-- UNSAT value: minimum fraction of unsatisfied constraints. -/
noncomputable def unsat (G : BinaryCSP V α) : ℚ :=
  1 - maxSat G

/-- Axiom: maxSat returns a valid satisfaction fraction -/
axiom maxSat_spec (G : BinaryCSP V α) :
  ∃ (σ : Assignment V α), satFrac G σ = maxSat G ∧
  ∀ (σ' : Assignment V α), satFrac G σ' ≤ maxSat G

/-- Satisfaction fraction is non-negative. -/
lemma satFrac_nonneg (G : BinaryCSP V α) (σ : Assignment V α) :
  0 ≤ satFrac G σ := by
  unfold satFrac
  apply div_nonneg <;> simp

/-- Satisfaction fraction is bounded by 1. -/
lemma satFrac_le_one (G : BinaryCSP V α) (σ : Assignment V α) :
  satFrac G σ ≤ 1 := by
  unfold satFrac
  have h1 : (G.E.filter fun ec => EdgeC.sat σ ec).card ≤ G.E.card := Finset.card_filter_le _ _
  have h2 : (0 : ℚ) < G.E.card := by simp [G.nonempty]
  rw [div_le_iff₀ h2, one_mul]
  simp [h1]

/-- UNSAT is bounded between 0 and 1. -/
lemma unsat_bounds (G : BinaryCSP V α) : 0 ≤ unsat G ∧ unsat G ≤ 1 := by
  unfold unsat
  obtain ⟨σ, hσ, hle⟩ := maxSat_spec G
  constructor
  · -- 0 ≤ 1 - maxSat G, i.e., maxSat G ≤ 1
    have : maxSat G ≤ 1 := hσ ▸ satFrac_le_one G σ
    linarith
  · -- 1 - maxSat G ≤ 1, i.e., 0 ≤ maxSat G
    have : 0 ≤ maxSat G := hσ ▸ satFrac_nonneg G σ
    linarith

/-- If all constraints can be satisfied, UNSAT is 0. -/
lemma unsat_zero_iff_satisfiable (G : BinaryCSP V α) :
  unsat G = 0 ↔ ∃ σ : Assignment V α, satFrac G σ = 1 := by
  unfold unsat
  constructor
  · -- unsat G = 0 → ∃ σ, satFrac G σ = 1
    intro h
    obtain ⟨σ, hσ, _⟩ := maxSat_spec G
    use σ
    linarith
  · -- (∃ σ, satFrac G σ = 1) → unsat G = 0
    intro ⟨σ, hσ⟩
    obtain ⟨σ', hσ', hle⟩ := maxSat_spec G
    have h1 : maxSat G ≥ 1 := hσ ▸ hle σ
    have h2 : maxSat G ≤ 1 := hσ' ▸ satFrac_le_one G σ'
    linarith

/-- The number of edges in a CSP. -/
def size (G : BinaryCSP V α) : ℕ := G.E.card

/-- A CSP with more constraints has larger size. -/
lemma size_pos (G : BinaryCSP V α) : 0 < size G := G.nonempty

end BinaryCSP

/-!
## Graph Degree and Regularity

Definitions for degree-regular constraint graphs.
-/

namespace BinaryCSP

variable {V α : Type*} [Fintype V] [Fintype α] [DecidableEq V]

/-- The degree of a vertex in a constraint graph (number of constraints involving it). -/
def degree (G : BinaryCSP V α) (v : V) : ℕ :=
  (G.E.filter (fun ec => ∃ u, ec.e = s(v, u) ∨ ec.e = s(u, v))).card

/-- A constraint graph is d-regular if all vertices have degree d. -/
def IsRegular (G : BinaryCSP V α) (d : ℕ) : Prop :=
  ∀ v : V, degree G v = d

/-- Regular graphs have bounded size. -/
lemma regular_size_bound (G : BinaryCSP V α) (d : ℕ) (h : IsRegular G d) :
  size G ≤ d * (Fintype.card V) / 2 := by
  unfold size
  sorry

end BinaryCSP

/-!
## 3-Colorability is NP-hard

Reduction from 3-Colorability to 2-CSP satisfiability (to be formalized).
-/

-- Placeholders for complexity-theoretic reductions
axiom ThreeColor : Type
axiom reduces_poly : Type → Type → Prop
axiom threeColor_to_csp : True
