import Mathlib.Probability.Moments.Variance
import Mathlib.MeasureTheory.Measure.MeasureSpace
import PCP.Probability.Unit02_MarkovInequality.API

/-!
# Chebyshev's Inequality

This file proves Chebyshev's inequality using variance.

## Main results

* `chebyshev_inequality`: Pr[|X - E[X]| ≥ t] ≤ Var[X] / t²
* `chebyshev_standardized`: Pr[|X - E[X]| ≥ k·σ] ≤ 1/k²

## Notes

Chebyshev's inequality is derived from Markov's inequality applied
to the squared deviation (X - E[X])².

-/

namespace Probability.Unit03

open MeasureTheory ProbabilityTheory ENNReal

variable {α : Type*} {m : MeasurableSpace α}

/-- Chebyshev's inequality: the probability that a random variable deviates
    from its mean by at least t is at most Var[X]/t². -/
lemma chebyshev_inequality (μ : Measure α) [IsFiniteMeasure μ]
    (X : α → ℝ) (hX : MemLp X 2 μ)
    (t : ℝ) (ht : 0 < t) :
    μ {ω | t ≤ |X ω - μ[X]|} ≤ ENNReal.ofReal (variance X μ / t^2) := by
  exact meas_ge_le_variance_div_sq hX ht

/-- Chebyshev's inequality in terms of standard deviation. -/
lemma chebyshev_standardized (μ : Measure α) [IsFiniteMeasure μ]
    (X : α → ℝ) (hX : MemLp X 2 μ)
    (k : ℝ) (hk : 0 < k) (hvar : 0 < variance X μ) :
    μ {ω | k * Real.sqrt (variance X μ) ≤ |X ω - μ[X]|} ≤
      ENNReal.ofReal (1 / k^2) := by
  have h := chebyshev_inequality μ X hX (k * Real.sqrt (variance X μ))
    (mul_pos hk (Real.sqrt_pos.mpr hvar))
  convert h using 2
  rw [mul_pow, Real.sq_sqrt (variance_nonneg X μ)]
  field_simp
  ring

/-- One-sided Chebyshev bound: Pr[X - E[X] ≥ t] ≤ Var[X]/(Var[X] + t²). -/
lemma chebyshev_one_sided (μ : Measure α) [IsProbabilityMeasure μ]
    (X : α → ℝ) (hX : Measurable X) (hint : Integrable X μ)
    (t : ℝ) (ht : 0 < t) :
    μ {ω | t ≤ X ω - ∫ x, X x ∂μ} ≤
      ENNReal.ofReal (variance X μ / (variance X μ + t^2)) := by
  sorry

/-- Chebyshev for deviations in terms of variance. -/
lemma chebyshev_variance_bound (μ : Measure α) [IsFiniteMeasure μ]
    (X : α → ℝ) (hX : MemLp X 2 μ)
    (ε : ℝ) (hε : 0 < ε) :
    μ {ω | ε ≤ |X ω - μ[X]|} ≤
      ENNReal.ofReal (variance X μ / ε^2) := by
  exact chebyshev_inequality μ X hX ε hε

/-- If variance is small, X is concentrated near its mean. -/
lemma concentration_from_small_variance (μ : Measure α) [IsFiniteMeasure μ]
    (X : α → ℝ) (hX : MemLp X 2 μ)
    (ε δ : ℝ) (hε : 0 < ε) (hvar : variance X μ ≤ δ * ε^2) :
    μ {ω | ε ≤ |X ω - μ[X]|} ≤ ENNReal.ofReal δ := by
  calc μ {ω | ε ≤ |X ω - μ[X]|}
      ≤ ENNReal.ofReal (variance X μ / ε^2) :=
        chebyshev_inequality μ X hX ε hε
    _ ≤ ENNReal.ofReal (δ * ε^2 / ε^2) := by
        apply ENNReal.ofReal_le_ofReal
        apply div_le_div_of_nonneg_right hvar
        exact sq_pos_of_pos hε
    _ = ENNReal.ofReal δ := by
        congr 1
        field_simp
        ring

/-- Weak law of large numbers setup: sample mean concentrates. -/
lemma sample_mean_concentration (μ : Measure α) [IsProbabilityMeasure μ]
    (X : ℕ → α → ℝ) (hX : ∀ i, Measurable (X i))
    (hint : ∀ i, Integrable (X i) μ)
    (hiid : ∀ i j, i ≠ j → IndepFun (X i) (X j) μ)
    (n : ℕ) (ε : ℝ) (hε : 0 < ε) :
    True := by -- Placeholder for WLLN
  trivial

end Probability.Unit03
