import Mathlib
import PCP.Spectral.Unit01_AdjacencyMatrix.Slop_AdjacencyMatrix

/-!
# Adjacency Matrix API

Public interface for adjacency matrix definitions and properties.

## Main Exports

This module re-exports key definitions and lemmas from the adjacency matrix unit:

* `adjacencyMatrix G` - The adjacency matrix of graph G
* `adjacencyMatrix_symm` - Symmetry property
* `adjacencyMatrix_diag` - Diagonal zeros (no self-loops)
* `adjacencyMatrix_eq_one_iff` - Characterization of adjacency

## Usage

```lean
import PCP.Spectral.Unit01_AdjacencyMatrix

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

-- The adjacency matrix is symmetric
example : (adjacencyMatrix G)ᵀ = adjacencyMatrix G :=
  adjacencyMatrix_symm G

-- Diagonal entries are zero
example (v : V) : adjacencyMatrix G v v = 0 :=
  adjacencyMatrix_diag G v

-- Entry is 1 iff vertices are adjacent
example (u v : V) : adjacencyMatrix G u v = 1 ↔ G.Adj u v :=
  adjacencyMatrix_eq_one_iff G u v
```

-/

namespace Spectral.Unit01

-- Re-export main definition (defined in PCP.Spectral.Matrix)
open Spectral (adjacencyMatrix)

-- Re-export key lemmas
export Spectral.Unit01 (
  adjacencyMatrix_of_adj
  adjacencyMatrix_of_not_adj
  adjacencyMatrix_diag
  adjacencyMatrix_symm
  adjacencyMatrix_symm_apply
  adjacencyMatrix_range
  adjacencyMatrix_nonneg
  adjacencyMatrix_le_one
  adjacencyMatrix_eq_one_iff
  adjacencyMatrix_eq_zero_iff
)

end Spectral.Unit01
