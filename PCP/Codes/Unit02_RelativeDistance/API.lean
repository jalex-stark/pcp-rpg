import Mathlib
import PCP.Codes.Unit02_RelativeDistance.Slop_RelativeDistance

/-!
# Relative Distance API

Public interface for relative (normalized) Hamming distance.

## Main Exports

This module re-exports key definitions and lemmas:

* `relativeDistance x y` - Normalized Hamming distance in [0,1]
* `relativeDistance_mem_unit_interval` - Bounds in [0,1]
* `relativeDistance_comm` - Symmetry
* `relativeDistance_eq_zero_iff` - Zero distance characterization
* `relativeDistance_triangle` - Triangle inequality

## Usage

```lean
import PCP.Codes.Unit02

variable {n : ℕ} {α : Type*} [DecidableEq α]
variable (x y : Fin n → α)

-- Relative distance is in [0,1]
example : 0 ≤ relativeDistance x y ∧ relativeDistance x y ≤ 1 :=
  relativeDistance_mem_unit_interval x y

-- Symmetric
example : relativeDistance x y = relativeDistance y x :=
  relativeDistance_comm x y

-- Zero iff equal (when n > 0)
example (hn : 0 < n) : relativeDistance x y = 0 ↔ x = y :=
  relativeDistance_eq_zero_iff x y hn

-- Triangle inequality
example (z : Fin n → α) :
    relativeDistance x z ≤ relativeDistance x y + relativeDistance y z :=
  relativeDistance_triangle x y z
```

-/

namespace Codes.Unit02

-- Re-export main definition
export Codes.Unit02 (relativeDistance)

-- Re-export key lemmas
export Codes.Unit02 (
  relativeDistance_nonneg
  relativeDistance_le_one
  relativeDistance_mem_unit_interval
  relativeDistance_self
  relativeDistance_comm
  relativeDistance_symm
  relativeDistance_eq_zero_iff
  eq_of_relativeDistance_eq_zero
  relativeDistance_triangle
  relativeDistance_eq_one_iff
)

end Codes.Unit02
