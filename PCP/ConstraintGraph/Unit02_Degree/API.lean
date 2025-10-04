import Mathlib
import PCP.ConstraintGraph.Unit02_Degree.Slop_Degree
import PCP.ConstraintGraph.Unit02_Degree.Slop_Size

/-!
# API: Degree and Size Properties

Degree and size properties for constraint graphs.

These lemmas establish basic facts about the structure of binary CSPs,
including vertex degrees and edge counts.

## Main Results

- `size_pos`: Every CSP has positive size (at least one edge)
- `edges_nonempty`: Edge set of a CSP is nonempty
- `degree_pos_of_incident`: If a vertex is incident to an edge, its degree is positive
- `exists_incident_of_degree_pos`: If degree is positive, the vertex is incident to some edge
- `degree_le_size`: Vertex degree is bounded by the total number of edges

## Curated API

This file documents the stable, curated subset of lemmas from the machine-generated
slop files (`Slop_Size.lean`, `Slop_Degree.lean`). The lemmas are already available
in the `ConstraintGraph.Unit02` namespace, and this file serves as the canonical
reference for which lemmas form the stable API.

### Size Properties
- `ConstraintGraph.Unit02.size_pos`
- `ConstraintGraph.Unit02.edges_nonempty`

### Degree Properties
- `ConstraintGraph.Unit02.degree_pos_of_incident`
- `ConstraintGraph.Unit02.exists_incident_of_degree_pos`
- `ConstraintGraph.Unit02.degree_le_size`

## Usage

```lean
import PCP.ConstraintGraph.Unit02_Degree.API

open ConstraintGraph.Unit02

example {V α : Type*} [Fintype V] [Fintype α] [DecidableEq V]
    (G : BinaryCSP V α) :
    0 < BinaryCSP.size G :=
  size_pos G

example {V α : Type*} [Fintype V] [Fintype α] [DecidableEq V]
    (G : BinaryCSP V α) (v : V)
    (h : ∃ ec ∈ G.E, ∃ u, ec.e = s(v, u)) :
    0 < BinaryCSP.degree G v :=
  degree_pos_of_incident G v h
```
-/
