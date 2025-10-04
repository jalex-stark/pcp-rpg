import Mathlib
import PCP.Probability.Unit01_UnionBound.Slop_UnionBound

/-!
# Union Bound API

Public interface for the union bound (Boole's inequality).

## Main Exports

This module re-exports the union bound and variants:

* `union_bound_two` - For two events
* `union_bound_finset` - For finite families
* `union_bound_finite` - For fintype-indexed families
* `exists_not_mem_of_sum_prob_lt_one` - Probabilistic existence

## Usage

```lean
import PCP.Probability.Unit01

variable {α : Type*} [MeasurableSpace α] (μ : Measure α)

-- Union of two events
example (A B : Set α) : μ (A ∪ B) ≤ μ A + μ B :=
  union_bound_two μ A B

-- Finite union
example [Fintype ι] (A : ι → Set α) : μ (⋃ i, A i) ≤ ∑ i, μ (A i) :=
  union_bound_finite μ A

-- Probabilistic method: if sum < 1, there exists element avoiding all events
example [IsProbabilityMeasure μ] [Fintype ι] [Nonempty α]
    (A : ι → Set α) (h : ∑ i, μ (A i) < 1) :
    ∃ x, ∀ i, x ∉ A i :=
  exists_not_mem_of_sum_prob_lt_one μ A h
```

-/

namespace Probability.Unit01

-- Re-export main lemmas
export Probability.Unit01 (
  union_bound_two
  prob_union_le_add
  union_bound_finset
  union_bound_finite
  measure_iInter_compl_pos
  exists_not_mem_of_sum_prob_lt_one
  union_bound_three
  prob_union_le_of_all_le
)

end Probability.Unit01
