import Mathlib
import PCP.Expander.Unit02_CheegerEasy.Slop_CheegerEasy

/-!
# Cheeger Easy Direction API

Public interface for the easy direction of Cheeger's inequality.

## Main Exports

This module re-exports the easy direction result:

* `cheeger_easy` - h(G) ≥ (d - λ₂) / 2
* `expansion_bounds_eigenvalue` - Expansion implies bounded eigenvalue
* `good_expansion_implies_small_gap` - Good expansion → small spectral gap

## Usage

```lean
import PCP.Expander.Unit02

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]
variable (d : ℕ) (hd : 0 < d) (hreg : Expander.IsRegular G d)

-- Easy direction
example : ∃ (h : ℚ), h = edgeExpansion G ∧
    (h : ℝ) ≥ ((d : ℝ) - spectralGap G d) / 2 :=
  cheeger_easy G d hd hreg
```

-/

namespace Expander.Unit02

-- Re-export main lemmas
export Expander.Unit02 (
  spectralGap
  cheeger_easy
  expansion_bounds_eigenvalue
  good_expansion_implies_small_gap
  spectral_gap_le_of_expansion
)

end Expander.Unit02
