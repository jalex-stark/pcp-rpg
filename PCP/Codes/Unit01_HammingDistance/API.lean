import Mathlib
import PCP.Codes.Unit01_HammingDistance.Slop_HammingDistance

/-!
# Hamming Distance API

Public interface for Hamming distance definitions and properties.

## Main Exports

This module re-exports key definitions and lemmas:

* `hammingDist x y` - Hamming distance between vectors
* `hammingDist_self` - Distance to self is zero
* `hammingDist_comm` - Symmetry
* `hammingDist_triangle` - Triangle inequality
* `hammingDist_eq_zero_iff` - Zero distance characterization

## Usage

```lean
import PCP.Codes.Unit01

variable {n : ℕ} {α : Type*} [DecidableEq α]
variable (x y : Fin n → α)

-- Distance to self is zero
example : hammingDist x x = 0 := hammingDist_self x

-- Hamming distance is symmetric
example : hammingDist x y = hammingDist y x := hammingDist_comm x y

-- Triangle inequality
example (z : Fin n → α) :
    hammingDist x z ≤ hammingDist x y + hammingDist y z :=
  hammingDist_triangle x y z

-- Zero distance iff equal
example : hammingDist x y = 0 ↔ x = y := hammingDist_eq_zero_iff x y
```

-/

namespace Codes.Unit01

-- Re-export main definition
export Codes.Unit01 (hammingDist)

-- Re-export key lemmas
export Codes.Unit01 (
  hammingDist_self
  hammingDist_comm
  hammingDist_symm
  hammingDist_triangle
  hammingDist_eq_zero_iff
  hammingDist_le_length
  hammingDist_pos_of_ne
  eq_of_hammingDist_eq_zero
)

end Codes.Unit01
