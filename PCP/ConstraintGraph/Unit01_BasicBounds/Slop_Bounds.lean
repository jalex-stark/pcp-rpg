import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Algebra.Order.Field.Defs
import PCP.ConstraintGraph.Defs

namespace ConstraintGraph.Unit01

open BinaryCSP

/-- Edge cardinality is positive for non-empty CSPs. -/
lemma card_pos {V α : Type*} [Fintype V] [Fintype α]
    (G : BinaryCSP V α) : (0 : ℚ) < G.E.card := by
  simp [G.nonempty]

/-- Satisfaction fraction is non-negative. -/
lemma satFrac_nonneg {V α : Type*} [Fintype V] [Fintype α] [DecidableEq V]
    (G : BinaryCSP V α) (σ : Assignment V α) :
    0 ≤ satFrac G σ := by
  unfold satFrac
  apply div_nonneg <;> simp

/-- Filter cardinality is bounded by set cardinality. -/
lemma card_filter_sat_le {V α : Type*} [Fintype V] [Fintype α] [DecidableEq V]
    (G : BinaryCSP V α) (σ : Assignment V α) :
    (G.E.filter fun ec => EdgeC.sat σ ec).card ≤ G.E.card :=
  Finset.card_filter_le _ _

/-- Satisfaction fraction is at most one. -/
lemma satFrac_le_one {V α : Type*} [Fintype V] [Fintype α] [DecidableEq V]
    (G : BinaryCSP V α) (σ : Assignment V α) :
    satFrac G σ ≤ 1 := by
  unfold satFrac
  rw [div_le_iff₀ (card_pos G), one_mul]
  exact Nat.cast_le.mpr (card_filter_sat_le G σ)

/-- Satisfaction fraction is in the unit interval. -/
lemma satFrac_in_unit {V α : Type*} [Fintype V] [Fintype α] [DecidableEq V]
    (G : BinaryCSP V α) (σ : Assignment V α) :
    0 ≤ satFrac G σ ∧ satFrac G σ ≤ 1 :=
  ⟨satFrac_nonneg G σ, satFrac_le_one G σ⟩

/-- Maximum satisfaction is non-negative. -/
lemma maxSat_nonneg {V α : Type*} [Fintype V] [Fintype α] [DecidableEq V]
    (G : BinaryCSP V α) : 0 ≤ maxSat G := by
  obtain ⟨σ, hσ, _⟩ := maxSat_spec G
  rw [← hσ]
  exact satFrac_nonneg G σ

/-- Maximum satisfaction is at most one. -/
lemma maxSat_le_one {V α : Type*} [Fintype V] [Fintype α] [DecidableEq V]
    (G : BinaryCSP V α) : maxSat G ≤ 1 := by
  obtain ⟨σ, hσ, _⟩ := maxSat_spec G
  rw [← hσ]
  exact satFrac_le_one G σ

/-- Maximum satisfaction is in the unit interval. -/
lemma maxSat_in_unit {V α : Type*} [Fintype V] [Fintype α] [DecidableEq V]
    (G : BinaryCSP V α) :
    0 ≤ maxSat G ∧ maxSat G ≤ 1 :=
  ⟨maxSat_nonneg G, maxSat_le_one G⟩

/-- UNSAT is non-negative. -/
lemma unsat_nonneg {V α : Type*} [Fintype V] [Fintype α] [DecidableEq V]
    (G : BinaryCSP V α) : 0 ≤ unsat G := by
  unfold unsat
  have : maxSat G ≤ 1 := maxSat_le_one G
  linarith

/-- UNSAT is at most one. -/
lemma unsat_le_one {V α : Type*} [Fintype V] [Fintype α] [DecidableEq V]
    (G : BinaryCSP V α) : unsat G ≤ 1 := by
  unfold unsat
  have : 0 ≤ maxSat G := maxSat_nonneg G
  linarith

/-- UNSAT is in the unit interval. -/
lemma unsat_in_unit {V α : Type*} [Fintype V] [Fintype α] [DecidableEq V]
    (G : BinaryCSP V α) :
    0 ≤ unsat G ∧ unsat G ≤ 1 :=
  ⟨unsat_nonneg G, unsat_le_one G⟩

/-- UNSAT equals one minus maximum satisfaction. -/
lemma unsat_complement {V α : Type*} [Fintype V] [Fintype α] [DecidableEq V]
    (G : BinaryCSP V α) : unsat G = 1 - maxSat G := rfl

/-- Maximum satisfaction equals one minus UNSAT. -/
lemma maxSat_eq_one_sub_unsat {V α : Type*} [Fintype V] [Fintype α] [DecidableEq V]
    (G : BinaryCSP V α) : maxSat G = 1 - unsat G := by
  unfold unsat
  linarith

/-- UNSAT is zero iff maximum satisfaction is one. -/
lemma unsat_eq_zero_iff {V α : Type*} [Fintype V] [Fintype α] [DecidableEq V]
    (G : BinaryCSP V α) :
    unsat G = 0 ↔ maxSat G = 1 := by
  unfold unsat
  constructor <;> intro h <;> linarith

/-- UNSAT is one iff maximum satisfaction is zero. -/
lemma unsat_eq_one_iff {V α : Type*} [Fintype V] [Fintype α] [DecidableEq V]
    (G : BinaryCSP V α) :
    unsat G = 1 ↔ maxSat G = 0 := by
  unfold unsat
  constructor <;> intro h <;> linarith

end ConstraintGraph.Unit01
