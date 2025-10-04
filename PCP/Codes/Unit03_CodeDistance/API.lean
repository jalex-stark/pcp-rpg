import Mathlib
import PCP.Codes.Unit03_CodeDistance.Slop_CodeDistance

/-!
# Code Distance API

Public interface for code distance definitions.

## Main Exports

This module re-exports code distance and properties:

* `codeDistance C` - Minimum distance of a code
* `codeDistance_pos_of_two_distinct` - Positive for non-trivial codes
* `all_pairs_ge_codeDistance` - All pairs separated by at least d
* `can_detect_errors` - Error detection capability
* `can_correct_errors` - Error correction capability

## Usage

```lean
import PCP.Codes.Unit03

variable {n : ℕ} {α : Type*} [DecidableEq α]
variable (C : Finset (Fin n → α))

-- Minimum distance
def d := codeDistance C

-- Distance bounds codeword separation
example (x y : Fin n → α) (hx : x ∈ C) (hy : y ∈ C) (hne : x ≠ y) :
    codeDistance C ≤ hammingDist x y :=
  all_pairs_ge_codeDistance C x y hx hy hne

-- Error detection
example (t : ℕ) (hd : t + 1 ≤ codeDistance C)
    (x y : Fin n → α) (hx : x ∈ C) (hy : y ∈ C)
    (hdist : hammingDist x y ≤ t) :
    x = y :=
  can_detect_errors C t hd x y hx hy hdist
```

-/

namespace Codes.Unit03

-- Re-export main definition
export Codes.Unit03 (codeDistance)

-- Re-export key lemmas
export Codes.Unit03 (
  codeDistance_singleton
  codeDistance_empty
  codeDistance_le_length
  codeDistance_pos_of_two_distinct
  all_pairs_ge_codeDistance
  codeDistance_le_iff
  can_detect_errors
  can_correct_errors
)

end Codes.Unit03
