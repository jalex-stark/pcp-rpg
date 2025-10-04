import Mathlib.Data.Matrix.Basic
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Algebra.Order.Field.Defs
import Mathlib.Tactic
import PCP.Spectral.Matrix
import PCP.RandomWalk.Defs

namespace RandomWalk.Unit01

open Matrix SimpleGraph Spectral RandomWalk

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj] (d : ℕ) (h : d > 0)

/-- Transition matrix entry definition. -/
lemma transitionMatrix_def (u v : V) :
    transitionMatrix G d h u v = if G.Adj u v then (1 : ℚ) / d else 0 := rfl

/-- Transition matrix entries are non-negative. -/
lemma transitionMatrix_entry_nonneg (u v : V) :
    0 ≤ transitionMatrix G d h u v := by
  unfold transitionMatrix
  split_ifs
  · positivity
  · norm_num

/-- Transition matrix entries are at most 1 (when d ≥ 1). -/
lemma transitionMatrix_entry_le_one (u v : V) :
    transitionMatrix G d h u v ≤ 1 := by
  unfold transitionMatrix
  split_ifs
  · sorry
  · norm_num

/-- Entry is 1/d when vertices are adjacent. -/
lemma transitionMatrix_of_adj (u v : V) (hadj : G.Adj u v) :
    transitionMatrix G d h u v = (1 : ℚ) / d := by
  unfold transitionMatrix
  simp [hadj]

/-- Entry is 0 when vertices are not adjacent. -/
lemma transitionMatrix_of_not_adj (u v : V) (hna : ¬G.Adj u v) :
    transitionMatrix G d h u v = 0 := by
  unfold transitionMatrix
  simp [hna]

/-- Transition matrix is symmetric for undirected graphs. -/
lemma transitionMatrix_symm (u v : V) :
    transitionMatrix G d h u v = transitionMatrix G d h v u := by
  unfold transitionMatrix
  simp [G.adj_comm]

/-- Diagonal entries depend on self-loops (which don't exist in SimpleGraph). -/
lemma transitionMatrix_diag (v : V) :
    transitionMatrix G d h v v = 0 := by
  apply transitionMatrix_of_not_adj
  exact G.loopless v

/-- Alternative form: entries are either 0 or 1/d. -/
lemma transitionMatrix_entry_dichotomy (u v : V) :
    transitionMatrix G d h u v = 0 ∨ transitionMatrix G d h u v = (1 : ℚ) / d := by
  unfold transitionMatrix
  split_ifs <;> simp

/-- Row sum equals 1 for d-regular graphs. -/
lemma transitionMatrix_row_sum (regular : ∀ v, degree G v = d) (u : V) :
    Finset.univ.sum (transitionMatrix G d h u) = 1 := by
  sorry

/-- Non-zero entry implies adjacency. -/
lemma adj_of_transitionMatrix_ne_zero (u v : V)
    (hne : transitionMatrix G d h u v ≠ 0) :
    G.Adj u v := by
  by_contra hna
  have : transitionMatrix G d h u v = 0 := transitionMatrix_of_not_adj G d h u v hna
  contradiction

/-- Zero entry implies non-adjacency. -/
lemma not_adj_of_transitionMatrix_eq_zero (u v : V)
    (hz : transitionMatrix G d h u v = 0) :
    ¬G.Adj u v := by
  intro hadj
  have : transitionMatrix G d h u v = (1 : ℚ) / d := transitionMatrix_of_adj G d h u v hadj
  rw [this] at hz
  have : (0 : ℚ) < d := by simp only [Nat.cast_pos]; omega
  have : (0 : ℚ) < (1 : ℚ) / d := div_pos (by norm_num) this
  linarith

end RandomWalk.Unit01
