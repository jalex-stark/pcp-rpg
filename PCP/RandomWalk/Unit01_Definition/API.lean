import Mathlib
import PCP.RandomWalk.Unit01_Definition.Slop_RandomWalk

/-!
# Random Walk API

Public interface for random walk definitions.

## Main Exports

This module re-exports key definitions and lemmas:

* `transitionMatrix G d` - Transition matrix for d-regular graph
* `randomWalk G d t` - t-step random walk probabilities
* `transitionMatrix_row_sum` - Stochastic property
* `randomWalk_zero` - Identity at time 0
* `randomWalk_add` - Composition property

## Usage

```lean
import PCP.RandomWalk.Unit01

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]
variable (d : ℕ) (hd : 0 < d)

-- Transition matrix
def P := transitionMatrix G d hd

-- Row sums equal 1 (for regular graphs)
example [∀ v, Fintype (G.neighborSet v)] (hreg : Expander.IsRegular G d) (u : V) :
    ∑ v, P u v = 1 :=
  transitionMatrix_row_sum G d hd hreg u

-- t-step random walk
example (t : ℕ) : Matrix V V ℚ := randomWalk G d hd t

-- Composition property
example (s t : ℕ) :
    randomWalk G d hd (s + t) = randomWalk G d hd s * randomWalk G d hd t :=
  randomWalk_add G d hd s t
```

-/

namespace RandomWalk.Unit01

-- Re-export main definitions
export RandomWalk.Unit01 (
  transitionMatrix
  randomWalk
)

-- Re-export key lemmas
export RandomWalk.Unit01 (
  transitionMatrix_of_adj
  transitionMatrix_of_not_adj
  transitionMatrix_nonneg
  transitionMatrix_row_sum
  randomWalk_zero
  randomWalk_one
  randomWalk_succ
  randomWalk_add
  randomWalk_nonneg
)

end RandomWalk.Unit01
