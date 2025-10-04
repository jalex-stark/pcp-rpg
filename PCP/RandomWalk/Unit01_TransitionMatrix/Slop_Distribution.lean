import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Algebra.Order.Field.Defs
import Mathlib.Tactic
import PCP.RandomWalk.Defs

namespace RandomWalk.Unit01

open RandomWalk

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Distribution validity definition. -/
lemma Distribution_isValid_def (p : Distribution V) :
    p.isValid ↔ (∀ v, 0 ≤ p v) ∧ Finset.univ.sum p = 1 := Iff.rfl

/-- Uniform distribution definition. -/
lemma uniformDistribution_def [Nonempty V] (v : V) :
    uniformDistribution V v = (1 : ℚ) / Fintype.card V := rfl

/-- Uniform distribution has non-negative entries. -/
lemma uniformDistribution_nonneg [Nonempty V] (v : V) :
    0 ≤ uniformDistribution V v := by
  unfold uniformDistribution
  positivity

/-- Each entry of uniform distribution equals 1/|V|. -/
lemma uniformDistribution_entry [Nonempty V] (v : V) :
    uniformDistribution V v = (1 : ℚ) / Fintype.card V := rfl

/-- Uniform distribution entries sum to 1. -/
lemma uniformDistribution_sum [Nonempty V] :
    Finset.univ.sum (uniformDistribution V) = 1 := by
  unfold uniformDistribution
  rw [Finset.sum_const, Finset.card_univ]
  simp only [nsmul_eq_mul]
  norm_cast
  have : (0 : ℚ) < Fintype.card V := by positivity
  field_simp

/-- Uniform distribution is valid. -/
lemma uniformDistribution_valid [Nonempty V] :
    (uniformDistribution V).isValid := by
  unfold Distribution.isValid
  constructor
  · intro v
    exact uniformDistribution_nonneg v
  · exact uniformDistribution_sum

/-- All entries of uniform distribution are equal. -/
lemma uniformDistribution_eq [Nonempty V] (u v : V) :
    uniformDistribution V u = uniformDistribution V v := rfl

/-- Uniform distribution is positive. -/
lemma uniformDistribution_pos [Nonempty V] (v : V) :
    0 < uniformDistribution V v := by
  unfold uniformDistribution
  positivity

/-- Valid distribution has non-negative entries. -/
lemma Distribution_isValid_nonneg {p : Distribution V} (h : p.isValid) (v : V) :
    0 ≤ p v := h.1 v

/-- Valid distribution sums to 1. -/
lemma Distribution_isValid_sum {p : Distribution V} (h : p.isValid) :
    Finset.univ.sum p = 1 := h.2

/-- Uniform distribution on singleton is 1. -/
lemma uniformDistribution_singleton {V : Type*} [Fintype V] [DecidableEq V]
    [Nonempty V] (h : Fintype.card V = 1) (v : V) :
    uniformDistribution V v = 1 := by
  unfold uniformDistribution
  rw [h]
  norm_num

/-- Alternative characterization of valid distribution. -/
lemma Distribution_isValid_iff (p : Distribution V) :
    p.isValid ↔ (∀ v, 0 ≤ p v) ∧ Finset.univ.sum p = 1 := Iff.rfl

end RandomWalk.Unit01
