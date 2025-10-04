import Mathlib
import PCP.Expander.Unit01_RegularGraphs.Slop_Regular
import PCP.Expander.Unit01_RegularGraphs.Slop_Boundary

/-!
# API: Regular Graph Properties

Regular graph and expansion properties for expander graph theory.

A d-regular graph has all vertices with degree exactly d. The vertex boundary
measures connectivity between sets, and expansion ratios quantify how well
sets expand into their neighborhoods.

## Main Results

### Regularity
- `IsRegular`: Definition of d-regular graphs
- `IsRegular_degree`: All vertices in a d-regular graph have degree d
- `IsRegular_unique`: The regularity parameter d is unique
- `sum_degrees_IsRegular`: Sum of degrees equals d × |V|

### Vertex Boundary
- `vertexBoundary`: Vertices outside S adjacent to vertices in S
- `vertexBoundary_subset`: Boundary is subset of Sᶜ
- `vertexExpansionRatio`: |∂S| / |S| for non-empty sets
- `vertexExpansionRatio_nonneg`: Expansion ratio is non-negative

### Edge Boundary
- `edgeBoundary`: Edges with exactly one endpoint in S
- `edgeBoundary_symm`: Edge boundary respects Sym2 symmetry
- `edgeExpansionRatio`: |∂_E(S)| / |S| for non-empty sets
- `edgeExpansionRatio_nonneg`: Edge expansion ratio is non-negative

## Curated API

This file documents the stable, curated subset of lemmas from the machine-generated
slop files. The lemmas are already available in the `Expander.Unit01` namespace.

### Core Regularity
- `Expander.Unit01.IsRegular`
- `Expander.Unit01.IsRegular_degree`
- `Expander.Unit01.IsRegular_unique`
- `Expander.Unit01.sum_degrees_IsRegular`

### Vertex Boundary
- `Expander.Unit01.vertexBoundary`
- `Expander.Unit01.vertexBoundary_subset`
- `Expander.Unit01.vertexExpansionRatio`
- `Expander.Unit01.vertexExpansionRatio_nonneg`
- `Expander.Unit01.mem_vertexBoundary_iff`

### Edge Boundary
- `Expander.Unit01.edgeBoundary`
- `Expander.Unit01.edgeBoundary_symm`
- `Expander.Unit01.edgeExpansionRatio`
- `Expander.Unit01.edgeExpansionRatio_nonneg`
- `Expander.Unit01.mem_edgeBoundary_iff`

## Usage

```lean
import PCP.Expander.Unit01_RegularGraphs.API

open Expander.Unit01

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [∀ v, Fintype (G.neighborSet v)]

-- Regular graphs
example (d : ℕ) (h : IsRegular G d) (v : V) :
    G.degree v = d :=
  h v

-- Vertex expansion
example (S : Set V) (v : V) (h : v ∈ vertexBoundary G S) :
    v ∉ S ∧ ∃ u ∈ S, G.Adj u v :=
  mem_vertexBoundary_iff.mp h
```
-/
