import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite

namespace Expander.Unit01

open scoped Classical

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A graph is d-regular if all vertices have degree exactly d. -/
def IsRegular (G : SimpleGraph V) [∀ v, Fintype (G.neighborSet v)] (d : ℕ) : Prop :=
  ∀ v : V, G.degree v = d

/-- Definitional unfolding of IsRegular. -/
lemma IsRegular_def {G : SimpleGraph V} [∀ v, Fintype (G.neighborSet v)] {d : ℕ} :
    IsRegular G d ↔ ∀ v : V, G.degree v = d := by
  rfl

/-- In a d-regular graph, every vertex has degree d. -/
lemma IsRegular_degree {G : SimpleGraph V} [∀ v, Fintype (G.neighborSet v)] {d : ℕ}
    (h : IsRegular G d) (v : V) :
    G.degree v = d := by
  exact h v

/-- Alternative form: degree equals d for all vertices. -/
lemma degree_eq_of_IsRegular {G : SimpleGraph V} [∀ v, Fintype (G.neighborSet v)] {d : ℕ}
    (h : IsRegular G d) (v : V) :
    G.degree v = d := by
  exact h v

/-- Regular graphs have non-negative degree (trivial, degrees are natural numbers). -/
lemma IsRegular_nonneg {G : SimpleGraph V} [∀ v, Fintype (G.neighborSet v)] {d : ℕ}
    (h : IsRegular G d) :
    0 ≤ d := by
  exact Nat.zero_le d

/-- Degree is non-negative in regular graphs. -/
lemma degree_nonneg_of_IsRegular {G : SimpleGraph V} [∀ v, Fintype (G.neighborSet v)] {d : ℕ}
    (h : IsRegular G d) (v : V) :
    0 ≤ G.degree v := by
  rw [h v]
  exact Nat.zero_le d

/-- Alternative characterization of regularity. -/
lemma IsRegular_iff {G : SimpleGraph V} [∀ v, Fintype (G.neighborSet v)] {d : ℕ} :
    IsRegular G d ↔ (∀ v : V, G.degree v = d) := by
  rfl

/-- If all vertices have degree d, the graph is d-regular. -/
lemma IsRegular_of_degree_eq {G : SimpleGraph V} [∀ v, Fintype (G.neighborSet v)] {d : ℕ}
    (h : ∀ v : V, G.degree v = d) :
    IsRegular G d := by
  exact h

/-- Degrees are equal in a regular graph. -/
lemma degree_eq_degree_of_IsRegular {G : SimpleGraph V} [∀ v, Fintype (G.neighborSet v)] {d : ℕ}
    (h : IsRegular G d) (u v : V) :
    G.degree u = G.degree v := by
  rw [h u, h v]

/-- Regular graph property is preserved under vertex reindexing. -/
lemma IsRegular_iff_forall_eq {G : SimpleGraph V} [∀ v, Fintype (G.neighborSet v)] {d : ℕ} :
    IsRegular G d ↔ ∀ u v : V, G.degree u = d ∧ G.degree v = d := by
  constructor
  · intro h u v
    exact ⟨h u, h v⟩
  · intro h v
    exact (h v v).1

/-- A 0-regular graph has all degrees equal to 0. -/
lemma IsRegular_zero_iff {G : SimpleGraph V} [∀ v, Fintype (G.neighborSet v)] :
    IsRegular G 0 ↔ ∀ v : V, G.degree v = 0 := by
  rfl

/-- In a 0-regular graph, every vertex has degree 0. -/
lemma degree_eq_zero_of_IsRegular_zero {G : SimpleGraph V} [∀ v, Fintype (G.neighborSet v)]
    (h : IsRegular G 0) (v : V) :
    G.degree v = 0 := by
  exact h v

/-- Regularity implies uniform degree function. -/
lemma IsRegular_const_degree {G : SimpleGraph V} [∀ v, Fintype (G.neighborSet v)] {d : ℕ}
    (h : IsRegular G d) :
    ∃ k : ℕ, ∀ v : V, G.degree v = k := by
  exact ⟨d, h⟩

/-- The constant degree in a regular graph is unique. -/
lemma IsRegular_unique {G : SimpleGraph V} [∀ v, Fintype (G.neighborSet v)] {d₁ d₂ : ℕ}
    (h₁ : IsRegular G d₁) (h₂ : IsRegular G d₂) [Nonempty V] :
    d₁ = d₂ := by
  obtain ⟨v⟩ := ‹Nonempty V›
  rw [← h₁ v, ← h₂ v]

/-- Sum of degrees in a regular graph equals d times the number of vertices. -/
lemma sum_degrees_IsRegular {G : SimpleGraph V} [∀ v, Fintype (G.neighborSet v)] {d : ℕ}
    (h : IsRegular G d) :
    Finset.univ.sum (G.degree ·) = d * Fintype.card V := by
  conv_lhs => arg 2; ext v; rw [h v]
  rw [Finset.sum_const, Finset.card_univ, Nat.nsmul_eq_mul, mul_comm]

end Expander.Unit01
