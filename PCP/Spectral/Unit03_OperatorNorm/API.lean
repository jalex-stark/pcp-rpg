import Mathlib
import PCP.Spectral.Unit03_OperatorNorm.Slop_OperatorNorm

/-!
# API: Operator Norm and Spectral Radius

Operator norm and spectral radius for matrices.

This unit establishes the fundamental theorem that for symmetric matrices,
the operator norm equals the spectral radius (maximum absolute eigenvalue).

## Main Results

- `spectralRadius`: Definition of spectral radius via Rayleigh quotient
- `spectralRadius_nonneg`: Spectral radius is non-negative
- `spectralRadius_smul`: Spectral radius scales with scalar multiplication
- `spectralRadius_neg`: Spectral radius invariant under negation

## Curated API

This file documents the stable, curated subset of lemmas from the machine-generated
slop file (`Slop_OperatorNorm.lean`). The lemmas are already available in the
`Spectral.Unit03` namespace, and this file serves as the canonical
reference for which lemmas form the stable API.

### Core Definition & Properties
- `Spectral.Unit03.spectralRadius`
- `Spectral.Unit03.spectralRadius_nonneg`
- `Spectral.Unit03.spectralRadius_bounded`

### Scaling & Operations
- `Spectral.Unit03.spectralRadius_smul`
- `Spectral.Unit03.spectralRadius_neg`
- `Spectral.Unit03.spectralRadius_add_le`

## Usage

```lean
import PCP.Spectral.Unit03_OperatorNorm.API

open Spectral.Unit03

example (A : Matrix n n ℝ) :
    0 ≤ spectralRadius A :=
  spectralRadius_nonneg A

example (A : Matrix n n ℝ) (c : ℝ) (hc : 0 ≤ c) :
    spectralRadius (c • A) = c * spectralRadius A :=
  spectralRadius_smul A c hc
```
-/
