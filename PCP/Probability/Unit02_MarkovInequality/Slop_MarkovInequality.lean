import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Data.Real.Basic

/-!
# Markov's Inequality

This file states and proves Markov's inequality for non-negative random variables.

## Main results

* `markov_inequality`: Pr[X ≥ a] ≤ 𝔼[X] / a
* `markov_inequality_mul`: Pr[X ≥ t·𝔼[X]] ≤ 1/t

## Notes

Markov's inequality is fundamental in probability theory and provides
basic tail bounds for non-negative random variables.

-/

namespace Probability.Unit02

open MeasureTheory ENNReal

variable {α : Type*} {m : MeasurableSpace α}

/-- Markov's inequality: for a non-negative measurable function X and a > 0,
    μ{X ≥ a} ≤ 𝔼[X] / a. -/
lemma markov_inequality (μ : Measure α) (X : α → ℝ≥0∞)
    (a : ℝ≥0∞) (ha : a > 0) :
    μ {ω | a ≤ X ω} ≤ (∫⁻ ω, X ω ∂μ) / a :=
  meas_ge_le_lintegral_div μ X ha

/-- Alternative statement using set notation. -/
lemma markov_inequality' (μ : Measure α) (X : α → ℝ≥0∞)
    (a : ℝ≥0∞) (ha : a ≠ 0) :
    μ {ω | a ≤ X ω} * a ≤ ∫⁻ ω, X ω ∂μ :=
  meas_ge_le_lintegral_mul μ X ha

/-- Markov's inequality in multiplicative form: Pr[X ≥ t·E[X]] ≤ 1/t. -/
lemma markov_inequality_mul (μ : Measure α) [IsProbabilityMeasure μ]
    (X : α → ℝ≥0∞) (t : ℝ≥0∞) (ht : 1 < t) :
    μ {ω | t * (∫⁻ ω, X ω ∂μ) ≤ X ω} ≤ 1 / t := by
  by_cases h : ∫⁻ ω, X ω ∂μ = 0
  · simp [h]
  · have hpos : 0 < ∫⁻ ω, X ω ∂μ := h.bot_lt
    calc μ {ω | t * (∫⁻ ω, X ω ∂μ) ≤ X ω}
        ≤ (∫⁻ ω, X ω ∂μ) / (t * (∫⁻ ω, X ω ∂μ)) := by
          apply markov_inequality
          exact mul_pos (zero_lt_one.trans ht) hpos
      _ = 1 / t := by
          rw [ENNReal.div_mul_cancel (ne_of_gt hpos)]
          simp [hpos.ne']

/-- Markov's inequality for absolute value (when X : α → ℝ). -/
lemma markov_inequality_abs (μ : Measure α) (X : α → ℝ)
    (hX : Measurable X) (a : ℝ) (ha : 0 < a) :
    μ {ω | (a : ℝ≥0∞) ≤ ‖X ω‖₊} ≤ (∫⁻ ω, ‖X ω‖₊ ∂μ) / a := by
  apply markov_inequality
  exact ENNReal.coe_pos.mpr ha

/-- Variant: if E[X] ≤ b, then Pr[X ≥ a] ≤ b/a. -/
lemma prob_ge_le_div_of_lintegral_le (μ : Measure α) (X : α → ℝ≥0∞)
    (a b : ℝ≥0∞) (ha : a > 0) (hb : ∫⁻ ω, X ω ∂μ ≤ b) :
    μ {ω | a ≤ X ω} ≤ b / a := by
  calc μ {ω | a ≤ X ω}
      ≤ (∫⁻ ω, X ω ∂μ) / a := markov_inequality μ X a ha
    _ ≤ b / a := by
        apply ENNReal.div_le_div_right
        exact hb

/-- Markov's inequality with probability notation. -/
lemma markov_prob (μ : Measure α) [IsProbabilityMeasure μ]
    (X : α → ℝ≥0∞) (a : ℝ≥0∞) (ha : a > 0) :
    μ {ω | a ≤ X ω} ≤ (∫⁻ ω, X ω ∂μ) / a :=
  markov_inequality μ X a ha

/-- Simple form: Pr[X ≥ 2·E[X]] ≤ 1/2. -/
lemma markov_double (μ : Measure α) [IsProbabilityMeasure μ]
    (X : α → ℝ≥0∞) :
    μ {ω | 2 * (∫⁻ ω, X ω ∂μ) ≤ X ω} ≤ 1 / 2 := by
  by_cases h : ∫⁻ ω, X ω ∂μ = 0
  · simp [h]
  · apply markov_inequality_mul
    norm_num

end Probability.Unit02
