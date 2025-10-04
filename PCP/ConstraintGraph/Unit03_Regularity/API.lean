import Mathlib
import PCP.ConstraintGraph.Unit03_Regularity.Slop_Regular

/-!
# API: Regularity Properties

Properties of d-regular constraint graphs.

A d-regular CSP has all vertices with degree exactly d, which provides
useful structural properties for graph algorithms and analysis.

## Main Results

- `regular_degree_eq`: Every vertex in a d-regular graph has degree d
- `regular_uniform`: All vertices in a regular graph have the same degree
- `regular_deg_pos`: In a d-regular graph with d > 0, all degrees are positive
- `isRegular_of_uniform_degree`: If all vertices have degree d, the graph is d-regular

## Curated API

This file documents the stable, curated subset of lemmas from the machine-generated
slop file (`Slop_Regular.lean`). The lemmas are already available in the
`ConstraintGraph.Unit03` namespace, and this file serves as the canonical
reference for which lemmas form the stable API.

### Core Properties
- `ConstraintGraph.Unit03.regular_degree_eq`
- `ConstraintGraph.Unit03.regular_uniform`
- `ConstraintGraph.Unit03.regular_deg_pos`

### Characterizations
- `ConstraintGraph.Unit03.isRegular_of_uniform_degree`

## Usage

```lean
import PCP.ConstraintGraph.Unit03_Regularity.API

open ConstraintGraph.Unit03

example {V α : Type*} [Fintype V] [Fintype α] [DecidableEq V]
    (G : BinaryCSP V α) (d : ℕ) (h : BinaryCSP.IsRegular G d) (v : V) :
    BinaryCSP.degree G v = d :=
  regular_degree_eq G d h v

example {V α : Type*} [Fintype V] [Fintype α] [DecidableEq V]
    (G : BinaryCSP V α) (d : ℕ) (h : BinaryCSP.IsRegular G d) (u v : V) :
    BinaryCSP.degree G u = BinaryCSP.degree G v :=
  regular_uniform G d h u v
```
-/
