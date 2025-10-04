import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Rat.Defs
import Mathlib.Algebra.BigOperators.Group.Finset
import Mathlib.MeasureTheory.Measure.MeasureSpace

/-!
# Union Bound (Boole's Inequality)

This file proves the union bound: the probability of a union of events
is at most the sum of their individual probabilities.

## Main results

* `union_bound_two`: Pr[A ∪ B] ≤ Pr[A] + Pr[B]
* `union_bound_finset`: Pr[⋃ᵢ∈I Aᵢ] ≤ ∑ᵢ∈I Pr[Aᵢ]

## Notes

This is Boole's inequality, fundamental in probability theory.
Mathlib likely has this already, but we prove it for completeness.

-/

namespace Probability.Unit01

open MeasureTheory Finset BigOperators

variable {α : Type*} {ι : Type*}

/-- Union bound for two sets in a measure space. -/
lemma union_bound_two [MeasurableSpace α] (μ : Measure α)
    (A B : Set α) :
    μ (A ∪ B) ≤ μ A + μ B :=
  measure_union_le A B

/-- Union bound for two sets (alternative statement). -/
lemma prob_union_le_add [MeasurableSpace α] (μ : Measure α)
    (A B : Set α) :
    μ (A ∪ B) ≤ μ A + μ B :=
  union_bound_two μ A B

/-- Union bound for finite families of sets. -/
lemma union_bound_finset [MeasurableSpace α] (μ : Measure α)
    (I : Finset ι) (A : ι → Set α) :
    μ (⋃ i ∈ I, A i) ≤ ∑ i ∈ I, μ (A i) := by
  classical
  induction I using Finset.induction with
  | empty =>
    simp
  | insert h ih =>
    simp only [iUnion_insert, sum_insert h]
    calc μ (A _ ∪ ⋃ i ∈ _, A i)
        ≤ μ (A _) + μ (⋃ i ∈ _, A i) := measure_union_le _ _
      _ ≤ μ (A _) + ∑ i ∈ _, μ (A i) := by
          apply add_le_add_left
          exact ih

/-- Union bound for finite families (indexed version). -/
lemma union_bound_finite [MeasurableSpace α] (μ : Measure α)
    [Fintype ι] (A : ι → Set α) :
    μ (⋃ i, A i) ≤ ∑ i, μ (A i) := by
  convert union_bound_finset μ univ A using 1
  · ext x; simp
  · simp

/-- If the sum of probabilities is less than 1, the complement has positive measure. -/
lemma measure_iInter_compl_pos [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    [Fintype ι] (A : ι → Set α) (h : ∑ i, μ (A i) < 1) :
    0 < μ (⋂ i, (A i)ᶜ) := by
  have key : μ (⋂ i, (A i)ᶜ) = 1 - μ (⋃ i, A i) := by
    rw [measure_iInter_compl_eq_one_sub]
  rw [key]
  have bound := union_bound_finite μ A
  linarith [measure_le_one μ (⋃ i, A i)]

/-- Union bound implies existence of element avoiding all events. -/
lemma exists_not_mem_of_sum_prob_lt_one [MeasurableSpace α] (μ : Measure α)
    [IsProbabilityMeasure μ] [Fintype ι] [Nonempty α]
    (A : ι → Set α) (h : ∑ i, μ (A i) < 1) :
    ∃ x, ∀ i, x ∉ A i := by
  have pos := measure_iInter_compl_pos μ A h
  have : (⋂ i, (A i)ᶜ).Nonempty := by
    by_contra hempty
    push_neg at hempty
    have : μ (⋂ i, (A i)ᶜ) = 0 := by
      apply measure_empty_of_not_nonempty
      exact hempty
    linarith
  obtain ⟨x, hx⟩ := this
  use x
  intro i
  exact hx i

/-- Union bound for three sets. -/
lemma union_bound_three [MeasurableSpace α] (μ : Measure α)
    (A B C : Set α) :
    μ (A ∪ B ∪ C) ≤ μ A + μ B + μ C := by
  calc μ (A ∪ B ∪ C)
      ≤ μ (A ∪ B) + μ C := measure_union_le _ _
    _ ≤ (μ A + μ B) + μ C := by
        apply add_le_add_right
        exact measure_union_le _ _
    _ = μ A + μ B + μ C := by ring

/-- Reformulation: if all individual probabilities are small, union is small. -/
lemma prob_union_le_of_all_le [MeasurableSpace α] (μ : Measure α)
    [Fintype ι] (A : ι → Set α) (ε : ℝ≥0∞) (h : ∀ i, μ (A i) ≤ ε) :
    μ (⋃ i, A i) ≤ Fintype.card ι * ε := by
  calc μ (⋃ i, A i)
      ≤ ∑ i, μ (A i) := union_bound_finite μ A
    _ ≤ ∑ i, ε := by
        apply sum_le_sum
        intro i _
        exact h i
    _ = Fintype.card ι * ε := by
        rw [sum_const, card_univ, nsmul_eq_mul]

end Probability.Unit01
