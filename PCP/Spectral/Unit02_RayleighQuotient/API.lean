import Mathlib
import PCP.Spectral.Unit02_RayleighQuotient.Slop_RayleighQuotient

/-!
# Rayleigh Quotient API

Public interface for Rayleigh quotient definitions.

## Main Exports

This module re-exports key definitions and lemmas:

* `rayleighQuotient A v` - Rayleigh quotient ⟨Av, v⟩ / ⟨v, v⟩
* `rayleighQuotient_smul` - Scale invariance
* `rayleighQuotient_nonneg_of_posSemidef` - Non-negativity for PSD matrices
* `rayleighQuotient_one` - Identity matrix case
* `rayleighQuotient_smul_matrix` - Matrix scaling

## Usage

```lean
import PCP.Spectral.Unit02

variable {n : Type*} [Fintype n] [DecidableEq n]
variable (A : Matrix n n ℝ) (v : n → ℝ)

-- Define Rayleigh quotient
def R := rayleighQuotient A v

-- Scale invariance
example (c : ℝ) (hc : c ≠ 0) :
    rayleighQuotient A (c • v) = rayleighQuotient A v :=
  rayleighQuotient_smul A v c hc

-- For PSD matrices, quotient is non-negative
example (hA : A.PosSemidef) (hv : v ⬝ᵥ v ≠ 0) :
    0 ≤ rayleighQuotient A v :=
  rayleighQuotient_nonneg_of_posSemidef A v hA hv

-- Identity matrix gives 1
example : rayleighQuotient (1 : Matrix n n ℝ) v = 1 :=
  rayleighQuotient_one v
```

-/

namespace Spectral.Unit02

-- Re-export main definition
export Spectral.Unit02 (rayleighQuotient)

-- Re-export key lemmas
export Spectral.Unit02 (
  rayleighQuotient_of_ne_zero
  rayleighQuotient_zero
  rayleighQuotient_smul
  rayleighQuotient_nonneg_of_posSemidef
  rayleighQuotient_neg
  rayleighQuotient_one
  rayleighQuotient_zero_matrix
  rayleighQuotient_add_matrix
  rayleighQuotient_smul_matrix
  dotProduct_self_pos_of_ne_zero
)

end Spectral.Unit02
