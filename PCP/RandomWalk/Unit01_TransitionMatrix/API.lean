import Mathlib
import PCP.Spectral.Matrix
import PCP.RandomWalk.Unit01_TransitionMatrix.Slop_TransitionMatrix
import PCP.RandomWalk.Unit01_TransitionMatrix.Slop_Distribution

/-!
# API: Transition Matrix and Distribution Properties

Transition matrix and distribution properties for random walks on graphs.

The transition matrix of a d-regular graph has entry 1/d for adjacent vertices,
0 otherwise. This gives a stochastic matrix (rows sum to 1).

## Main Results

### Transition Matrix
- `transitionMatrix`: Entry is 1/d for adjacent vertices, 0 otherwise
- `transitionMatrix_entry_nonneg`: All entries are non-negative
- `transitionMatrix_entry_le_one`: All entries are at most 1
- `transitionMatrix_symm`: Matrix is symmetric for undirected graphs
- `transitionMatrix_row_sum`: Rows sum to 1 for d-regular graphs

### Distributions
- `uniformDistribution`: Uniform distribution with all entries equal to 1/|V|
- `uniformDistribution_valid`: Uniform distribution is a valid probability distribution
- `uniformDistribution_sum`: Uniform distribution sums to 1
- `Distribution_isValid`: Characterization of valid distributions

## Curated API

This file documents the stable, curated subset of lemmas from the machine-generated
slop files. The lemmas are already available in the `RandomWalk.Unit01` namespace.

### Transition Matrix Core
- `RandomWalk.Unit01.transitionMatrix_def`
- `RandomWalk.Unit01.transitionMatrix_entry_nonneg`
- `RandomWalk.Unit01.transitionMatrix_of_adj`
- `RandomWalk.Unit01.transitionMatrix_of_not_adj`
- `RandomWalk.Unit01.transitionMatrix_symm`
- `RandomWalk.Unit01.transitionMatrix_row_sum`

### Distribution Properties
- `RandomWalk.Unit01.uniformDistribution_valid`
- `RandomWalk.Unit01.uniformDistribution_sum`
- `RandomWalk.Unit01.uniformDistribution_pos`
- `RandomWalk.Unit01.Distribution_isValid_def`

## Usage

```lean
import PCP.RandomWalk.Unit01_TransitionMatrix.API

open RandomWalk.Unit01

variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
variable (G : SimpleGraph V) [DecidableRel G.Adj] (d : ℕ) (h : d > 0)

-- Transition matrix for d-regular graphs
example (regular : ∀ v, G.degree v = d) (u : V) :
    Finset.univ.sum (transitionMatrix G d h u) = 1 :=
  transitionMatrix_row_sum G d h regular u

-- Uniform distribution
example : (uniformDistribution V).isValid :=
  uniformDistribution_valid
```
-/
