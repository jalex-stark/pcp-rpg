import Mathlib
import PCP.Expander.Unit01_EdgeExpansion.Slop_EdgeExpansion

/-!
# Edge Expansion API

Public interface for edge expansion definitions and properties.

## Main Exports

This module re-exports key definitions and lemmas:

* `edgeBoundary G S` - Edges crossing from S to its complement
* `setExpansion G S` - Expansion ratio for a single set
* `edgeExpansion G` - Minimum expansion over all small sets
* `edgeExpansion_nonneg` - Non-negativity property

## Usage

```lean
import PCP.Expander.Unit01

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

-- Edge expansion is non-negative
example : 0 ≤ edgeExpansion G := edgeExpansion_nonneg G

-- Boundary of empty set is empty
example : edgeBoundary G ∅ = ∅ := edgeBoundary_empty G

-- Edge expansion bounds set expansion
example (S : Finset V) (h1 : S.card > 0) (h2 : 2 * S.card ≤ Fintype.card V) :
    edgeExpansion G ≤ setExpansion G S :=
  edgeExpansion_le_setExpansion G S h1 h2
```

-/

namespace Expander.Unit01

-- Re-export main definitions
export Expander.Unit01 (
  edgeBoundary
  setExpansion
  edgeExpansion
)

-- Re-export key lemmas
export Expander.Unit01 (
  edgeBoundary_empty
  edgeBoundary_univ
  edgeBoundary_compl
  setExpansion_empty
  setExpansion_nonneg
  edgeExpansion_nonneg
  edgeExpansion_le_setExpansion
)

end Expander.Unit01
