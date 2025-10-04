-- Size properties for constraint graphs
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Basic
import PCP.ConstraintGraph.Defs

namespace ConstraintGraph.Unit02

variable {V α : Type*} [Fintype V] [Fintype α] [DecidableEq V]

/-- Size of a CSP equals its edge cardinality (definitional). -/
lemma size_eq_card (G : BinaryCSP V α) :
    BinaryCSP.size G = G.E.card := rfl

/-- Every CSP has positive size. -/
lemma size_pos (G : BinaryCSP V α) :
    0 < BinaryCSP.size G := by
  exact G.nonempty

/-- Size is positive (alternative form). -/
lemma size_pos' (G : BinaryCSP V α) :
    BinaryCSP.size G > 0 := by
  exact G.nonempty

/-- Edge set cardinality is positive. -/
lemma card_edges_pos (G : BinaryCSP V α) :
    0 < G.E.card := by
  exact G.nonempty

/-- Size is non-zero. -/
lemma size_ne_zero (G : BinaryCSP V α) :
    BinaryCSP.size G ≠ 0 := by
  apply Nat.pos_iff_ne_zero.mp
  exact G.nonempty

/-- Edge set is nonempty. -/
lemma edges_nonempty (G : BinaryCSP V α) :
    G.E.Nonempty := by
  apply Finset.card_pos.mp
  exact G.nonempty

end ConstraintGraph.Unit02
