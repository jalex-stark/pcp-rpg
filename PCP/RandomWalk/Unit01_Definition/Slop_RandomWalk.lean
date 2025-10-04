import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Fintype.Basic
import PCP.Spectral.Matrix

/-!
# Random Walks on Graphs

This file defines random walks on finite regular graphs.

## Main definitions

* `transitionMatrix G d`: Transition matrix for d-regular graph
* `randomWalk G d t`: t-step random walk probabilities

## Main results

* `transitionMatrix_row_sum`: Rows sum to 1 (stochastic)
* `transitionMatrix_nonneg`: Non-negative entries
* `randomWalk_zero`: P^0 = I
* `randomWalk_succ`: P^(t+1) = P * P^t

## References

* Dinur §2.3 (pp. 8-9): Random walks and mixing

-/

namespace RandomWalk.Unit01

open Matrix SimpleGraph Spectral Finset BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The transition matrix for a d-regular graph.
    Entry (u,v) is 1/d if u~v, else 0. -/
def transitionMatrix (G : SimpleGraph V) [DecidableRel G.Adj]
    (d : ℕ) (hd : 0 < d) : Matrix V V ℚ :=
  fun u v => if G.Adj u v then (1 : ℚ) / d else 0

/-- Transition matrix definition. -/
lemma transitionMatrix_def (G : SimpleGraph V) [DecidableRel G.Adj]
    (d : ℕ) (hd : 0 < d) (u v : V) :
    transitionMatrix G d hd u v = if G.Adj u v then (1 : ℚ) / d else 0 := rfl

/-- Transition matrix entry when adjacent. -/
lemma transitionMatrix_of_adj (G : SimpleGraph V) [DecidableRel G.Adj]
    (d : ℕ) (hd : 0 < d) {u v : V} (h : G.Adj u v) :
    transitionMatrix G d hd u v = (1 : ℚ) / d := by
  unfold transitionMatrix
  simp [h]

/-- Transition matrix entry when not adjacent. -/
lemma transitionMatrix_of_not_adj (G : SimpleGraph V) [DecidableRel G.Adj]
    (d : ℕ) (hd : 0 < d) {u v : V} (h : ¬G.Adj u v) :
    transitionMatrix G d hd u v = 0 := by
  unfold transitionMatrix
  simp [h]

/-- Transition matrix has non-negative entries. -/
lemma transitionMatrix_nonneg (G : SimpleGraph V) [DecidableRel G.Adj]
    (d : ℕ) (hd : 0 < d) (u v : V) :
    0 ≤ transitionMatrix G d hd u v := by
  unfold transitionMatrix
  split_ifs
  · apply div_nonneg <;> norm_num
    exact Nat.cast_pos.mpr hd
  · rfl

/-- For a d-regular graph, each row of the transition matrix sums to 1. -/
lemma transitionMatrix_row_sum (G : SimpleGraph V) [DecidableRel G.Adj]
    [∀ v, Fintype (G.neighborSet v)] (d : ℕ) (hd : 0 < d)
    (hreg : Expander.IsRegular G d) (u : V) :
    ∑ v, transitionMatrix G d hd u v = 1 := by
  unfold transitionMatrix
  calc ∑ v, (if G.Adj u v then (1 : ℚ) / d else 0)
      = ∑ v ∈ univ.filter (G.Adj u), (1 : ℚ) / d := by
        rw [sum_filter]
        congr
        ext v
        split_ifs <;> simp
    _ = (univ.filter (G.Adj u)).card * ((1 : ℚ) / d) := by
        rw [sum_const]
        norm_cast
    _ = d * ((1 : ℚ) / d) := by
        congr 1
        norm_cast
        rw [card_filter_univ_eq_of_finite]
        exact hreg u
    _ = 1 := by
        field_simp
        norm_cast

/-- Transition matrix entries are at most 1. -/
lemma transitionMatrix_le_one (G : SimpleGraph V) [DecidableRel G.Adj]
    (d : ℕ) (hd : 0 < d) (u v : V) :
    transitionMatrix G d hd u v ≤ 1 := by
  unfold transitionMatrix
  split_ifs
  · apply div_le_one_of_le
    · norm_num
    · exact Nat.one_le_cast.mpr hd

/-- The t-step random walk on a d-regular graph. -/
def randomWalk (G : SimpleGraph V) [DecidableRel G.Adj]
    (d : ℕ) (hd : 0 < d) (t : ℕ) : Matrix V V ℚ :=
  (transitionMatrix G d hd) ^ t

/-- Random walk definition. -/
lemma randomWalk_def (G : SimpleGraph V) [DecidableRel G.Adj]
    (d : ℕ) (hd : 0 < d) (t : ℕ) :
    randomWalk G d hd t = (transitionMatrix G d hd) ^ t := rfl

/-- 0-step random walk is the identity matrix. -/
lemma randomWalk_zero (G : SimpleGraph V) [DecidableRel G.Adj]
    (d : ℕ) (hd : 0 < d) :
    randomWalk G d hd 0 = 1 := by
  unfold randomWalk
  simp

/-- 0-step random walk value. -/
lemma randomWalk_zero_apply (G : SimpleGraph V) [DecidableRel G.Adj]
    (d : ℕ) (hd : 0 < d) (u v : V) :
    randomWalk G d hd 0 u v = if u = v then 1 else 0 := by
  rw [randomWalk_zero]
  rfl

/-- 1-step random walk is the transition matrix. -/
lemma randomWalk_one (G : SimpleGraph V) [DecidableRel G.Adj]
    (d : ℕ) (hd : 0 < d) :
    randomWalk G d hd 1 = transitionMatrix G d hd := by
  unfold randomWalk
  simp

/-- Composition: (t+1)-step walk equals transition matrix times t-step walk. -/
lemma randomWalk_succ (G : SimpleGraph V) [DecidableRel G.Adj]
    (d : ℕ) (hd : 0 < d) (t : ℕ) :
    randomWalk G d hd (t + 1) = transitionMatrix G d hd * randomWalk G d hd t := by
  unfold randomWalk
  rw [pow_succ]

/-- Alternative composition: (t+s)-step walk equals composition of t and s steps. -/
lemma randomWalk_add (G : SimpleGraph V) [DecidableRel G.Adj]
    (d : ℕ) (hd : 0 < d) (t s : ℕ) :
    randomWalk G d hd (t + s) = randomWalk G d hd t * randomWalk G d hd s := by
  unfold randomWalk
  exact pow_add _ _ _

/-- Random walk entries are non-negative (by induction). -/
lemma randomWalk_nonneg (G : SimpleGraph V) [DecidableRel G.Adj]
    (d : ℕ) (hd : 0 < d) (t : ℕ) (u v : V) :
    0 ≤ randomWalk G d hd t u v := by
  induction t with
  | zero =>
    rw [randomWalk_zero_apply]
    split_ifs <;> norm_num
  | succ t ih =>
    rw [randomWalk_succ]
    unfold Matrix.mul
    simp
    apply sum_nonneg
    intro w _
    apply mul_nonneg
    · exact transitionMatrix_nonneg G d hd u w
    · exact ih w v

/-- Successor form for random walk. -/
lemma randomWalk_succ' (G : SimpleGraph V) [DecidableRel G.Adj]
    (d : ℕ) (hd : 0 < d) (t : ℕ) :
    randomWalk G d hd (t + 1) = randomWalk G d hd t * transitionMatrix G d hd := by
  rw [randomWalk_add, randomWalk_one]

/-- Random walk is well-defined as matrix power. -/
lemma randomWalk_pow (G : SimpleGraph V) [DecidableRel G.Adj]
    (d : ℕ) (hd : 0 < d) (t : ℕ) :
    randomWalk G d hd t = (transitionMatrix G d hd) ^ t := rfl

end RandomWalk.Unit01
