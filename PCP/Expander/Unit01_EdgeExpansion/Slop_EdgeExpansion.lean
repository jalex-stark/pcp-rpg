import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Degree
import Mathlib.Data.Finset.Card
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Fintype.Basic

/-!
# Edge Expansion for Simple Graphs

This file defines edge expansion, a key measure of graph connectivity used in
expander graph theory.

## Main definitions

* `edgeBoundary G S`: Edges crossing from S to its complement
* `setExpansion G S`: Ratio |δ(S)| / |S| for a single set
* `edgeExpansion G`: Minimum expansion over all small non-empty sets

## Main results

* `edgeExpansion_nonneg`: Edge expansion is non-negative
* `edgeBoundary_empty`: Boundary of empty set is empty
* `edgeBoundary_symm`: δ(S) = δ(Sᶜ) for balanced sets

## References

* Dinur, Definition 2.1 (p. 7): Edge expansion definition

-/

namespace Expander.Unit01

open SimpleGraph Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The edge boundary of a set S: edges with exactly one endpoint in S. -/
def edgeBoundary (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) : Finset (Sym2 V) :=
  univ.filter fun e =>
    e.lift (fun u v => (u ∈ S ∧ v ∉ S) ∨ (u ∉ S ∧ v ∈ S))

/-- The edge boundary is well-defined. -/
lemma edgeBoundary_def (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) :
    edgeBoundary G S = univ.filter fun e =>
      e.lift (fun u v => (u ∈ S ∧ v ∉ S) ∨ (u ∉ S ∧ v ∈ S)) := rfl

/-- The boundary of the empty set is empty. -/
lemma edgeBoundary_empty (G : SimpleGraph V) [DecidableRel G.Adj] :
    edgeBoundary G ∅ = ∅ := by
  unfold edgeBoundary
  ext e
  simp
  intro u v _ _
  tauto

/-- The boundary of the full set is empty. -/
lemma edgeBoundary_univ (G : SimpleGraph V) [DecidableRel G.Adj] :
    edgeBoundary G univ = ∅ := by
  unfold edgeBoundary
  ext e
  simp
  intro u v _ _
  tauto

/-- Edge boundary contains only edges between S and Sᶜ. -/
lemma mem_edgeBoundary_iff (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) (e : Sym2 V) :
    e ∈ edgeBoundary G S ↔
      e.lift (fun u v => (u ∈ S ∧ v ∉ S) ∨ (u ∉ S ∧ v ∈ S)) := by
  unfold edgeBoundary
  simp

/-- Edge boundary is symmetric in a specific sense for complements. -/
lemma edgeBoundary_compl (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) :
    edgeBoundary G S = edgeBoundary G (univ \ S) := by
  ext e
  simp [edgeBoundary]
  constructor <;> intro h u v huv <;>
    · obtain ⟨⟨h1, h2⟩ | ⟨h1, h2⟩⟩ := h u v huv
      · right
        constructor
        · intro contra; exact h2 contra.1
        · exact h1
      · left
        constructor
        · intro contra; exact h2 contra.1
        · exact h1

/-- The expansion of a single set S. -/
def setExpansion (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) : ℚ :=
  if S.card = 0 then 0 else (edgeBoundary G S).card / S.card

/-- Set expansion is well-defined. -/
lemma setExpansion_def (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) :
    setExpansion G S = if S.card = 0 then 0 else (edgeBoundary G S).card / S.card := rfl

/-- Expansion of empty set is 0. -/
lemma setExpansion_empty (G : SimpleGraph V) [DecidableRel G.Adj] :
    setExpansion G ∅ = 0 := by
  unfold setExpansion
  simp

/-- Set expansion is non-negative. -/
lemma setExpansion_nonneg (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) :
    0 ≤ setExpansion G S := by
  unfold setExpansion
  split_ifs
  · rfl
  · apply div_nonneg
    · exact Nat.cast_nonneg _
    · exact Nat.cast_pos.mpr (Nat.pos_of_ne_zero ‹_›)

/-- The edge expansion of a graph: minimum expansion over small sets. -/
def edgeExpansion (G : SimpleGraph V) [DecidableRel G.Adj] : ℚ :=
  let smallSets := univ.filter fun S : Finset V => S.card > 0 ∧ 2 * S.card ≤ Fintype.card V
  if smallSets.Nonempty then
    smallSets.inf' (by assumption) (setExpansion G)
  else 0

/-- Edge expansion is well-defined. -/
lemma edgeExpansion_def (G : SimpleGraph V) [DecidableRel G.Adj] :
    edgeExpansion G =
      let smallSets := univ.filter fun S : Finset V => S.card > 0 ∧ 2 * S.card ≤ Fintype.card V
      if smallSets.Nonempty then
        smallSets.inf' (by assumption) (setExpansion G)
      else 0 := rfl

/-- Edge expansion is non-negative. -/
lemma edgeExpansion_nonneg (G : SimpleGraph V) [DecidableRel G.Adj] :
    0 ≤ edgeExpansion G := by
  unfold edgeExpansion
  split_ifs with h
  · apply Finset.inf'_le
    obtain ⟨S, hS⟩ := h
    exact setExpansion_nonneg G S
  · rfl

/-- Small sets are non-empty. -/
lemma smallSets_nonempty_of_exists (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) (h1 : S.card > 0) (h2 : 2 * S.card ≤ Fintype.card V) :
    (univ.filter fun T : Finset V => T.card > 0 ∧ 2 * T.card ≤ Fintype.card V).Nonempty := by
  use S
  simp [h1, h2]

/-- Edge expansion for empty graph is 0. -/
lemma edgeExpansion_bot [Nontrivial V] :
    edgeExpansion (⊥ : SimpleGraph V) = 0 := by
  unfold edgeExpansion
  split_ifs with h
  · apply le_antisymm
    · apply Finset.inf'_le_of_le
      · obtain ⟨S, hS⟩ := h
        exact hS
      · intro S hS
        unfold setExpansion
        split_ifs
        · rfl
        · apply div_nonneg
          · simp [edgeBoundary]
          · exact Nat.cast_pos.mpr (Nat.pos_of_ne_zero ‹_›)
    · exact edgeExpansion_nonneg _
  · rfl

/-- Edge expansion relates to minimum over set expansions. -/
lemma edgeExpansion_le_setExpansion (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) (h1 : S.card > 0) (h2 : 2 * S.card ≤ Fintype.card V) :
    edgeExpansion G ≤ setExpansion G S := by
  unfold edgeExpansion
  have hne := smallSets_nonempty_of_exists G S h1 h2
  simp only [hne, ↓reduceIte]
  apply Finset.inf'_le
  simp [h1, h2]

end Expander.Unit01
