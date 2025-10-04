import Mathlib
import PCP.ConstraintGraph.Unit01_BasicBounds.Slop_Bounds

/-!
# API: Basic Bounds on Satisfaction and UNSAT

Basic bounds on satisfaction fractions and UNSAT values.

These are foundational lemmas used throughout the PCP formalization. They establish
that satisfaction fractions, maximum satisfaction, and UNSAT values all lie in the
unit interval [0,1].

## Main Results

### Satisfaction Fraction Bounds
- `satFrac_nonneg`: Satisfaction fraction is non-negative
- `satFrac_le_one`: Satisfaction fraction is at most one
- `satFrac_in_unit`: Combined bound (satFrac ∈ [0,1])

### Maximum Satisfaction Bounds
- `maxSat_nonneg`: Maximum satisfaction is non-negative
- `maxSat_le_one`: Maximum satisfaction is at most one

### UNSAT Value Bounds
- `unsat_nonneg`: UNSAT is non-negative
- `unsat_le_one`: UNSAT is at most one
- `unsat_in_unit`: Combined bound (unsat ∈ [0,1])

### Key Characterizations
- `unsat_eq_zero_iff`: UNSAT is zero iff maximum satisfaction is one

## Curated API

This file documents the stable, curated subset of lemmas from the machine-generated
slop file (`Slop_Bounds.lean`). The lemmas are already available in the
`ConstraintGraph.Unit01` namespace, and this file serves as the canonical
reference for which lemmas form the stable API.

### Satisfaction Fraction Bounds
- `ConstraintGraph.Unit01.satFrac_nonneg`
- `ConstraintGraph.Unit01.satFrac_le_one`
- `ConstraintGraph.Unit01.satFrac_in_unit`

### Maximum Satisfaction Bounds
- `ConstraintGraph.Unit01.maxSat_nonneg`
- `ConstraintGraph.Unit01.maxSat_le_one`

### UNSAT Value Bounds
- `ConstraintGraph.Unit01.unsat_nonneg`
- `ConstraintGraph.Unit01.unsat_le_one`
- `ConstraintGraph.Unit01.unsat_in_unit`

### Key Characterizations
- `ConstraintGraph.Unit01.unsat_eq_zero_iff`

## Usage

```lean
import PCP.ConstraintGraph.Unit01_BasicBounds.API

open ConstraintGraph.Unit01

example {V α : Type*} [Fintype V] [Fintype α] [DecidableEq V]
    (G : BinaryCSP V α) (σ : Assignment V α) :
    0 ≤ BinaryCSP.satFrac G σ ∧ BinaryCSP.satFrac G σ ≤ 1 :=
  satFrac_in_unit G σ

example {V α : Type*} [Fintype V] [Fintype α] [DecidableEq V]
    (G : BinaryCSP V α) :
    0 ≤ BinaryCSP.unsat G ∧ BinaryCSP.unsat G ≤ 1 :=
  unsat_in_unit G

example {V α : Type*} [Fintype V] [Fintype α] [DecidableEq V]
    (G : BinaryCSP V α) (h : BinaryCSP.unsat G = 0) :
    BinaryCSP.maxSat G = 1 :=
  (unsat_eq_zero_iff G).mp h
```
-/
