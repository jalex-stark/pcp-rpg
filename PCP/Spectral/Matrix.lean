/-
  Spectral Graph Theory: Adjacency Matrices and Eigenvalues

  Adjacency matrix, eigenvalues, Rayleigh quotient, spectral gap

  Difficulty: ★★☆☆☆ (2/5)
  Estimated LOC: 200
  Work Package: WP-B
-/

import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Fintype.Basic

/-!
# Spectral Graph Theory

Adjacency matrices and eigenvalues for simple graphs.

This file defines the adjacency matrix of a graph and basic spectral properties
used in Dinur's gap amplification proof.

## Main Definitions

- `adjacencyMatrix`: Adjacency matrix of a finite simple graph
- `isSymmetric`: The adjacency matrix is symmetric
- `degree`: Vertex degree from adjacency matrix

## References

- Dinur, §2 (pp. 7-9): Spectral properties of graphs
-/

namespace Spectral

open Matrix SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The adjacency matrix of a simple graph over rationals.
    Entry (i,j) is 1 if there's an edge between i and j, 0 otherwise. -/
def adjacencyMatrix (G : SimpleGraph V) [DecidableRel G.Adj] : Matrix V V ℚ :=
  fun i j => if G.Adj i j then 1 else 0

/-- The adjacency matrix is symmetric for undirected graphs. -/
lemma adjacencyMatrix_symmetric (G : SimpleGraph V) [DecidableRel G.Adj] :
    (adjacencyMatrix G).transpose = adjacencyMatrix G := by
  ext i j
  simp [adjacencyMatrix, Matrix.transpose, G.adj_comm]

/-- Diagonal entries are 0 (no self-loops in simple graphs). -/
lemma adjacencyMatrix_diag_zero (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) :
    adjacencyMatrix G v v = 0 := by
  unfold adjacencyMatrix
  simp [G.loopless]

/-- The degree of a vertex is the sum of its row in the adjacency matrix. -/
def degree (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) : ℕ :=
  Finset.univ.sum fun u => if G.Adj v u then 1 else 0

/-- Degree computed from adjacency matrix matches the combinatorial definition. -/
lemma degree_eq_row_sum (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) :
    (degree G v : ℚ) = Finset.univ.sum (adjacencyMatrix G v) := by
  unfold degree adjacencyMatrix
  norm_cast

/-- The degree equals the cardinality of the neighbor set. -/
lemma degree_eq_card_neighborSet (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) :
    degree G v = (Finset.univ.filter (G.Adj v)).card := by
  unfold degree
  simp only [Finset.sum_ite, Finset.sum_const_zero, add_zero]
  rw [← Finset.card_eq_sum_ones]

end Spectral
