-- Regularity properties for constraint graphs
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Sym.Sym2
import PCP.ConstraintGraph.Defs

namespace ConstraintGraph.Unit03

variable {V α : Type*} [Fintype V] [Fintype α] [DecidableEq V]

/-- A d-regular graph has all vertices with degree d (definitional). -/
lemma regular_iff (G : BinaryCSP V α) (d : ℕ) :
    BinaryCSP.IsRegular G d ↔ ∀ v : V, BinaryCSP.degree G v = d := by
  rfl

/-- If G is d-regular, then every vertex has degree d. -/
lemma regular_degree_eq (G : BinaryCSP V α) (d : ℕ)
    (h : BinaryCSP.IsRegular G d) (v : V) :
    BinaryCSP.degree G v = d := by
  exact h v

/-- In a regular graph, all degrees are equal. -/
lemma regular_uniform (G : BinaryCSP V α) (d : ℕ)
    (h : BinaryCSP.IsRegular G d) (v w : V) :
    BinaryCSP.degree G v = BinaryCSP.degree G w := by
  rw [h v, h w]

/-- A regular graph is nonempty (trivial, as all CSPs are nonempty). -/
lemma regular_nonempty (G : BinaryCSP V α) (d : ℕ)
    (_h : BinaryCSP.IsRegular G d) :
    0 < BinaryCSP.size G := by
  exact G.nonempty

/-- If G is d-regular with d > 0, all degrees are positive. -/
lemma regular_deg_pos (G : BinaryCSP V α) (d : ℕ)
    (h : BinaryCSP.IsRegular G d) (hd : 0 < d) (v : V) :
    0 < BinaryCSP.degree G v := by
  rw [h v]
  exact hd

/-- In a d-regular graph, all degrees are at least d. -/
lemma regular_deg_ge (G : BinaryCSP V α) (d : ℕ)
    (h : BinaryCSP.IsRegular G d) (v : V) :
    d ≤ BinaryCSP.degree G v := by
  rw [h v]

/-- In a d-regular graph, all degrees are at most d. -/
lemma regular_deg_le (G : BinaryCSP V α) (d : ℕ)
    (h : BinaryCSP.IsRegular G d) (v : V) :
    BinaryCSP.degree G v ≤ d := by
  rw [h v]

/-- Two vertices in a regular graph have the same degree. -/
lemma regular_deg_eq_of_regular (G : BinaryCSP V α) (d : ℕ)
    (h : BinaryCSP.IsRegular G d) (u v : V) :
    BinaryCSP.degree G u = BinaryCSP.degree G v := by
  simp [h u, h v]

/-- If all vertices have the same degree d, the graph is d-regular. -/
lemma isRegular_of_uniform_degree (G : BinaryCSP V α) (d : ℕ)
    (h : ∀ v : V, BinaryCSP.degree G v = d) :
    BinaryCSP.IsRegular G d := by
  exact h

/-- A 0-regular graph has all vertices with degree 0. -/
lemma zero_regular_deg_zero (G : BinaryCSP V α)
    (h : BinaryCSP.IsRegular G 0) (v : V) :
    BinaryCSP.degree G v = 0 := by
  exact h v

end ConstraintGraph.Unit03
