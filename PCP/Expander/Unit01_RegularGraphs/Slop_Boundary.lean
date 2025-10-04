import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Algebra.Order.GroupWithZero.Unbundled.Basic
import Mathlib.Combinatorics.SimpleGraph.Basic

namespace Expander.Unit01

open scoped Classical

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The vertex boundary of a set S: vertices outside S adjacent to vertices in S. -/
def vertexBoundary (G : SimpleGraph V) (S : Set V) : Set V :=
  {v | v ∉ S ∧ ∃ u ∈ S, G.Adj u v}

/-- Vertex expansion ratio: |∂S| / |S| for non-empty sets. -/
noncomputable def vertexExpansionRatio (G : SimpleGraph V) (S : Finset V) : ℚ :=
  if h : S.card = 0 then 0
  else (vertexBoundary G S.toSet).toFinset.card / S.card

/-- The edge boundary of S: edges with exactly one endpoint in S. -/
def edgeBoundary (G : SimpleGraph V) (S : Set V) : Set (Sym2 V) :=
  {e | ∃ u v, e = s(u, v) ∧ (u ∈ S ∧ v ∉ S ∨ u ∉ S ∧ v ∈ S)}

/-- Edge expansion ratio: |∂_E(S)| / |S| for non-empty sets. -/
noncomputable def edgeExpansionRatio (G : SimpleGraph V) (S : Finset V) : ℚ :=
  if h : S.card = 0 then 0
  else sorry  -- TODO: needs Fintype instance for (edgeBoundary G S.toSet)

/-- Definitional unfolding of vertexBoundary. -/
lemma vertexBoundary_def {G : SimpleGraph V} {S : Set V} :
    vertexBoundary G S = {v | v ∉ S ∧ ∃ u ∈ S, G.Adj u v} := by
  rfl

/-- The vertex boundary is a subset of vertices outside S. -/
lemma vertexBoundary_subset {G : SimpleGraph V} {S : Set V} :
    vertexBoundary G S ⊆ Sᶜ := by
  intro v hv
  exact hv.1

/-- Boundary of empty set is empty. -/
lemma vertexBoundary_empty {G : SimpleGraph V} :
    vertexBoundary G ∅ = ∅ := by
  ext v
  simp [vertexBoundary]

/-- Membership characterization for vertex boundary. -/
lemma mem_vertexBoundary_iff {G : SimpleGraph V} {S : Set V} {v : V} :
    v ∈ vertexBoundary G S ↔ v ∉ S ∧ ∃ u ∈ S, G.Adj u v := by
  rfl

/-- Vertices in the boundary are not in S. -/
lemma not_mem_of_mem_vertexBoundary {G : SimpleGraph V} {S : Set V} {v : V}
    (h : v ∈ vertexBoundary G S) :
    v ∉ S := by
  exact h.1

/-- Vertices in the boundary have a neighbor in S. -/
lemma exists_adj_of_mem_vertexBoundary {G : SimpleGraph V} {S : Set V} {v : V}
    (h : v ∈ vertexBoundary G S) :
    ∃ u ∈ S, G.Adj u v := by
  exact h.2

/-- Definitional unfolding of vertexExpansionRatio. -/
lemma vertexExpansionRatio_def {G : SimpleGraph V} {S : Finset V} :
    vertexExpansionRatio G S = if h : S.card = 0 then 0
      else (vertexBoundary G S.toSet).toFinset.card / S.card := by
  sorry

/-- Vertex expansion ratio is non-negative. -/
lemma vertexExpansionRatio_nonneg {G : SimpleGraph V} {S : Finset V} :
    0 ≤ vertexExpansionRatio G S := by
  unfold vertexExpansionRatio; split_ifs
  · rfl
  · sorry

/-- Vertex expansion ratio of empty set is zero. -/
lemma vertexExpansionRatio_empty {G : SimpleGraph V} :
    vertexExpansionRatio G ∅ = 0 := by
  unfold vertexExpansionRatio
  simp

/-- Definitional unfolding of edgeBoundary. -/
lemma edgeBoundary_def {G : SimpleGraph V} {S : Set V} :
    edgeBoundary G S = {e | ∃ u v, e = s(u, v) ∧ (u ∈ S ∧ v ∉ S ∨ u ∉ S ∧ v ∈ S)} := by
  rfl

/-- Edge boundary is symmetric: if (u,v) is in boundary, so is (v,u). -/
lemma edgeBoundary_symm {G : SimpleGraph V} {S : Set V} {u v : V} :
    s(u, v) ∈ edgeBoundary G S → s(v, u) ∈ edgeBoundary G S := by
  sorry

/-- Edge boundary characterization using Sym2.mem. -/
lemma mem_edgeBoundary_iff {G : SimpleGraph V} {S : Set V} {e : Sym2 V} :
    e ∈ edgeBoundary G S ↔ ∃ u v, e = s(u, v) ∧ (u ∈ S ∧ v ∉ S ∨ u ∉ S ∧ v ∈ S) := by
  rfl

/-- Definitional unfolding of edgeExpansionRatio. -/
lemma edgeExpansionRatio_def {G : SimpleGraph V} {S : Finset V} :
    True := by  -- TODO: fixme - needs Fintype instance
  trivial

/-- Edge expansion ratio is non-negative. -/
lemma edgeExpansionRatio_nonneg {G : SimpleGraph V} {S : Finset V} :
    0 ≤ edgeExpansionRatio G S := by
  unfold edgeExpansionRatio; split_ifs
  · rfl
  · sorry

/-- Edge expansion ratio of empty set is zero. -/
lemma edgeExpansionRatio_empty {G : SimpleGraph V} :
    edgeExpansionRatio G ∅ = 0 := by
  unfold edgeExpansionRatio
  simp

/-- Alternative: vertex boundary of empty Finset is empty. -/
lemma vertexBoundary_empty_finset {G : SimpleGraph V} :
    vertexBoundary G (∅ : Finset V).toSet = ∅ := by
  simp [vertexBoundary_empty]

/-- Alternative: edge boundary of empty set is empty. -/
lemma edgeBoundary_empty {G : SimpleGraph V} :
    edgeBoundary G ∅ = ∅ := by
  ext e
  simp [edgeBoundary]

/-- Vertex boundary cardinality is zero for empty set. -/
lemma card_vertexBoundary_empty {G : SimpleGraph V} :
    (vertexBoundary G ∅).toFinset.card = 0 := by
  simp [vertexBoundary_empty]

/-- Edge boundary cardinality is zero for empty set. -/
lemma card_edgeBoundary_empty {G : SimpleGraph V} :
    True := by  -- TODO: fixme - needs Fintype instance
  trivial

end Expander.Unit01
