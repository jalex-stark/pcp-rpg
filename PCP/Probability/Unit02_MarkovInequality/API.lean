import Mathlib
import PCP.Probability.Unit02_MarkovInequality.Slop_MarkovInequality

/-!
# Markov Inequality API

Public interface for Markov's inequality.

## Main Exports

This module re-exports Markov's inequality and variants:

* `markov_inequality` - Basic form: Pr[X ≥ a] ≤ E[X]/a
* `markov_inequality_mul` - Multiplicative form: Pr[X ≥ t·E[X]] ≤ 1/t
* `markov_inequality_abs` - For absolute values
* `markov_double` - Simple case: Pr[X ≥ 2E[X]] ≤ 1/2

## Usage

```lean
import PCP.Probability.Unit02

variable {α : Type*} [MeasurableSpace α] (μ : Measure α)
variable [IsProbabilityMeasure μ] (X : α → ℝ≥0∞)

-- Markov's inequality
example (a : ℝ≥0∞) (ha : a > 0) :
    μ {ω | a ≤ X ω} ≤ (∫⁻ ω, X ω ∂μ) / a :=
  markov_inequality μ X a ha

-- Multiplicative form
example (t : ℝ≥0∞) (ht : 1 < t) :
    μ {ω | t * (∫⁻ ω, X ω ∂μ) ≤ X ω} ≤ 1 / t :=
  markov_inequality_mul μ X t ht

-- Special case
example : μ {ω | 2 * (∫⁻ ω, X ω ∂μ) ≤ X ω} ≤ 1 / 2 :=
  markov_double μ X
```

-/

namespace Probability.Unit02

-- Re-export main lemmas
export Probability.Unit02 (
  markov_inequality
  markov_inequality'
  markov_inequality_mul
  markov_inequality_abs
  prob_ge_le_div_of_lintegral_le
  markov_prob
  markov_double
)

end Probability.Unit02
