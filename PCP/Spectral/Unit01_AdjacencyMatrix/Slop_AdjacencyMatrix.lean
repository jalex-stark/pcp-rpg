import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Fintype.Basic
import PCP.Spectral.Matrix
import LeanCopilot
namespace Spectral.Unit01

open Matrix SimpleGraph Spectral

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Adjacency matrix is a well-defined function. -/
lemma adjacencyMatrix_def (u v : V) :
    adjacencyMatrix G u v = if G.Adj u v then 1 else 0 := rfl

/-- If vertices are adjacent, the adjacency matrix entry is 1. -/
lemma adjacencyMatrix_of_adj (u v : V) (h : G.Adj u v) :
    adjacencyMatrix G u v = 1 := by
  unfold adjacencyMatrix
  simp [h]

/-- If vertices are not adjacent, the adjacency matrix entry is 0. -/
lemma adjacencyMatrix_of_not_adj (u v : V) (h : ¬G.Adj u v) :
    adjacencyMatrix G u v = 0 := by
  unfold adjacencyMatrix
  simp [h]

/-- Diagonal entries are zero. -/
lemma adjacencyMatrix_diag (v : V) :
    adjacencyMatrix G v v = 0 := by
  apply adjacencyMatrix_of_not_adj
  exact G.loopless v

/-- Adjacency matrix is symmetric. -/
lemma adjacencyMatrix_symm :
    (adjacencyMatrix G)ᵀ = adjacencyMatrix G := by
  ext i j
  simp [adjacencyMatrix, transpose, G.adj_comm]

/-- Adjacency matrix symmetry (pointwise). -/
lemma adjacencyMatrix_symm_apply (u v : V) :
    adjacencyMatrix G u v = adjacencyMatrix G v u := by
  unfold adjacencyMatrix
  simp [G.adj_comm]

/-- Adjacency matrix entries are in {0, 1}. -/
lemma adjacencyMatrix_range (u v : V) :
    adjacencyMatrix G u v = 0 ∨ adjacencyMatrix G u v = 1 := by
  unfold adjacencyMatrix
  split_ifs <;> simp

/-- Adjacency matrix entries are non-negative. -/
lemma adjacencyMatrix_nonneg (u v : V) :
    0 ≤ adjacencyMatrix G u v := by
  unfold adjacencyMatrix
  split_ifs <;> decide

/-- Adjacency matrix entries are at most 1. -/
lemma adjacencyMatrix_le_one (u v : V) :
    adjacencyMatrix G u v ≤ 1 := by
  unfold adjacencyMatrix
  split_ifs <;> decide

/-- Adjacency matrix is in [0,1] range. -/
lemma adjacencyMatrix_in_unit_interval (u v : V) :
    0 ≤ adjacencyMatrix G u v ∧ adjacencyMatrix G u v ≤ 1 :=
  ⟨adjacencyMatrix_nonneg G u v, adjacencyMatrix_le_one G u v⟩

/-- Adjacency implies non-zero entry. -/
lemma adjacencyMatrix_ne_zero_of_adj (u v : V) (h : G.Adj u v) :
    adjacencyMatrix G u v ≠ 0 := by
  rw [adjacencyMatrix_of_adj G u v h]
  decide

/-- Zero entry implies non-adjacency. -/
lemma not_adj_of_adjacencyMatrix_eq_zero (u v : V)
    (h : adjacencyMatrix G u v = 0) :
    ¬G.Adj u v := by
  intro hadj
  have : adjacencyMatrix G u v = 1 := adjacencyMatrix_of_adj G u v hadj
  rw [this] at h
  contradiction

/-- Non-zero entry implies adjacency. -/
lemma adj_of_adjacencyMatrix_ne_zero (u v : V)
    (h : adjacencyMatrix G u v ≠ 0) :
    G.Adj u v := by
  by_contra hna
  have : adjacencyMatrix G u v = 0 := adjacencyMatrix_of_not_adj G u v hna
  contradiction

/-- Entry is 1 iff vertices are adjacent. -/
lemma adjacencyMatrix_eq_one_iff (u v : V) :
    adjacencyMatrix G u v = 1 ↔ G.Adj u v := by
  constructor
  · intro h
    apply adj_of_adjacencyMatrix_ne_zero
    rw [h]
    decide
  · exact adjacencyMatrix_of_adj G u v

/-- Entry is 0 iff vertices are not adjacent. -/
lemma adjacencyMatrix_eq_zero_iff (u v : V) :
    adjacencyMatrix G u v = 0 ↔ ¬G.Adj u v := by
  constructor
  · exact not_adj_of_adjacencyMatrix_eq_zero G u v
  · exact adjacencyMatrix_of_not_adj G u v

/-- Transpose entry equals original entry. -/
lemma adjacencyMatrix_transpose_apply (u v : V) :
    (adjacencyMatrix G)ᵀ u v = adjacencyMatrix G u v := by
  rw [adjacencyMatrix_symm]

/-- Adjacency matrix squared has non-negative entries. -/
lemma adjacencyMatrix_sq_nonneg (u v : V) :
    0 ≤ (adjacencyMatrix G * adjacencyMatrix G) u v := by
  unfold Matrix.mul
  simp
  apply Finset.sum_nonneg
  intro i _
  apply mul_nonneg
  · exact adjacencyMatrix_nonneg G u i
  · exact adjacencyMatrix_nonneg G i v

/-- Alternative diagonal zero formulation. -/
lemma adjacencyMatrix_diag_eq_zero :
    ∀ v : V, adjacencyMatrix G v v = 0 :=
  adjacencyMatrix_diag G

end Spectral.Unit01
