-- Degree properties for constraint graphs
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Sym.Sym2
import PCP.ConstraintGraph.Defs

namespace ConstraintGraph.Unit02

variable {V α : Type*} [Fintype V] [Fintype α] [DecidableEq V]

/-- Degree of a vertex is non-negative. -/
lemma degree_nonneg (G : BinaryCSP V α) (v : V) :
    0 ≤ BinaryCSP.degree G v := by
  exact Nat.zero_le _

/-- Degree equals the cardinality of incident edges. -/
lemma degree_eq_card_incident (G : BinaryCSP V α) (v : V) :
    BinaryCSP.degree G v = (G.E.filter (fun ec => ∃ u, ec.e = s(v, u))).card := rfl

/-- If degree is zero, then no edge is incident to the vertex. -/
lemma degree_eq_zero_of_not_incident (G : BinaryCSP V α) (v : V)
    (h : ∀ ec ∈ G.E, ∀ u, ec.e ≠ s(v, u)) :
    BinaryCSP.degree G v = 0 := by
  unfold BinaryCSP.degree
  rw [Finset.card_eq_zero]
  ext ec
  simp only [Finset.mem_filter, Finset.notMem_empty, iff_false]
  intro ⟨hec, ⟨u, heq⟩⟩
  exact h ec hec u heq

/-- If vertex has positive degree, then some edge is incident to it. -/
lemma exists_incident_of_degree_pos (G : BinaryCSP V α) (v : V)
    (h : 0 < BinaryCSP.degree G v) :
    ∃ ec ∈ G.E, ∃ u, ec.e = s(v, u) := by
  unfold BinaryCSP.degree at h
  have : (G.E.filter (fun ec => ∃ u, ec.e = s(v, u))).Nonempty := by
    apply Finset.card_pos.mp h
  obtain ⟨ec, hec⟩ := this
  simp only [Finset.mem_filter] at hec
  exact ⟨ec, hec.1, hec.2⟩

/-- If an edge is incident to a vertex, then degree is positive. -/
lemma degree_pos_of_incident (G : BinaryCSP V α) (v : V)
    (h : ∃ ec ∈ G.E, ∃ u, ec.e = s(v, u)) :
    0 < BinaryCSP.degree G v := by
  unfold BinaryCSP.degree
  apply Finset.card_pos.mpr
  obtain ⟨ec, hec, u, heq⟩ := h
  use ec
  simp only [Finset.mem_filter]
  exact ⟨hec, u, heq⟩

/-- The set of incident edges is a subset of all edges. -/
lemma incident_edges_subset (G : BinaryCSP V α) (v : V) :
    G.E.filter (fun ec => ∃ u, ec.e = s(v, u)) ⊆ G.E := by
  exact Finset.filter_subset _ _

/-- Cardinality of incident edges is bounded. -/
lemma incident_edges_card_le (G : BinaryCSP V α) (v : V) :
    (G.E.filter (fun ec => ∃ u, ec.e = s(v, u))).card ≤ G.E.card := by
  exact Finset.card_filter_le _ _

/-- Degree is bounded by total number of edges. -/
lemma degree_le_size (G : BinaryCSP V α) (v : V) :
    BinaryCSP.degree G v ≤ BinaryCSP.size G := by
  unfold BinaryCSP.degree BinaryCSP.size
  exact Finset.card_filter_le _ _

/-- Alternative characterization of incident edges using Sym2 membership. -/
lemma incident_iff_exists_pair (G : BinaryCSP V α) (v : V) (ec : EdgeC V α) :
    ec ∈ G.E.filter (fun ec => ∃ u, ec.e = s(v, u)) ↔
    ec ∈ G.E ∧ ∃ u, ec.e = s(v, u) := by
  simp only [Finset.mem_filter]

end ConstraintGraph.Unit02
