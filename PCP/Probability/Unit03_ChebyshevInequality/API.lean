import Mathlib
import PCP.Probability.Unit03_ChebyshevInequality.Slop_ChebyshevInequality

/-!
# Chebyshev Inequality API

Public interface for Chebyshev's inequality.

## Main Exports

This module re-exports Chebyshev's inequality and variants:

* `chebyshev_inequality` - Basic form: Pr[|X - E[X]| ≥ t] ≤ Var[X]/t²
* `chebyshev_standardized` - In terms of standard deviations
* `chebyshev_one_sided` - One-sided bound
* `concentration_from_small_variance` - Small variance implies concentration

## Usage

```lean
import PCP.Probability.Unit03

variable {α : Type*} [MeasurableSpace α] (μ : Measure α)
variable [IsProbabilityMeasure μ] (X : α → ℝ)
variable (hX : Measurable X) (hint : Integrable X μ)

-- Chebyshev's inequality
example (t : ℝ) (ht : 0 < t) :
    μ {ω | t ≤ |X ω - ∫ x, X x ∂μ|} ≤
      ENNReal.ofReal (variance X μ / t^2) :=
  chebyshev_inequality μ X hX hint t ht

-- Standardized form
example (k : ℝ) (hk : 0 < k) :
    μ {ω | k * Real.sqrt (variance X μ) ≤ |X ω - ∫ x, X x ∂μ|} ≤
      ENNReal.ofReal (1 / k^2) :=
  chebyshev_standardized μ X hX hint k hk
```

-/

namespace Probability.Unit03

-- Re-export main lemmas
export Probability.Unit03 (
  chebyshev_inequality
  chebyshev_standardized
  chebyshev_one_sided
  chebyshev_variance_bound
  concentration_from_small_variance
)

end Probability.Unit03
