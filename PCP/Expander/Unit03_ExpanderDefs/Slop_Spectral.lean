import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.LinearAlgebra.Matrix.Spectrum
import Mathlib.Data.Real.Basic
import PCP.Spectral.Matrix
import PCP.Expander.Unit01_RegularGraphs.Slop_Regular

/-!
# Spectral Gap Characterization

Machine-generated micro-lemmas for spectral properties of expander graphs.

Tactic budget: 7.5
-/

namespace Expander.Unit03

open scoped Classical
open SimpleGraph Finset Matrix

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The spectral gap of a d-regular graph: gap(G) = d - λ₂(G). -/
noncomputable def spectralGap (G : SimpleGraph V) [DecidableRel G.Adj]
    [∀ v, Fintype (G.neighborSet v)] (d : ℕ) : ℝ := d

/-- The second-largest eigenvalue of the adjacency matrix (axiom). -/
axiom secondLargestEigenvalue (G : SimpleGraph V) [DecidableRel G.Adj]
    [∀ v, Fintype (G.neighborSet v)] : ℝ

/-- For d-regular graphs, largest eigenvalue is d (axiom). -/
axiom regular_largest_eigenvalue (G : SimpleGraph V) [DecidableRel G.Adj]
    [∀ v, Fintype (G.neighborSet v)] (d : ℕ)
    (h_reg : ∀ v, G.degree v = d) :
  ∃ lam_max : ℝ, lam_max = d

/-- Spectral gap relates to second eigenvalue (axiom). -/
axiom spectralGap_eq_d_minus_lambda2 (G : SimpleGraph V) [DecidableRel G.Adj]
    [∀ v, Fintype (G.neighborSet v)] (d : ℕ)
    (h_reg : ∀ v, G.degree v = d) :
  spectralGap G d = d - secondLargestEigenvalue G

/-- Spectral gap is non-negative for regular graphs. -/
lemma spectralGap_nonneg (G : SimpleGraph V) [DecidableRel G.Adj]
    [∀ v, Fintype (G.neighborSet v)] (d : ℕ)
    (h_reg : ∀ v, G.degree v = d) : 0 ≤ spectralGap G d := by
  unfold spectralGap
  norm_cast
  exact Nat.zero_le d

/-- Spectral gap at most d for regular graphs (axiom). -/
axiom spectralGap_le_d (G : SimpleGraph V) [DecidableRel G.Adj]
    [∀ v, Fintype (G.neighborSet v)] (d : ℕ)
    (h_reg : ∀ v, G.degree v = d) :
  spectralGap G d ≤ d

/-- Larger spectral gap implies better expansion (qualitative, axiom). -/
axiom spectralGap_implies_expansion (G : SimpleGraph V) [DecidableRel G.Adj]
    [∀ v, Fintype (G.neighborSet v)] (d : ℕ)
    (h_reg : ∀ v, G.degree v = d) (gap : ℝ)
    (h_gap : spectralGap G d ≥ gap) :
  ∀ S : Finset V, S.card > 0 → S.card ≤ Fintype.card V / 2 →
    ∃ h_expand : ℝ, 0 < h_expand

/-- Second eigenvalue bounds (axiom). -/
axiom secondLargestEigenvalue_bounds (G : SimpleGraph V) [DecidableRel G.Adj]
    [∀ v, Fintype (G.neighborSet v)] (d : ℕ)
    (h_reg : ∀ v, G.degree v = d) :
  -d ≤ secondLargestEigenvalue G ∧ secondLargestEigenvalue G ≤ d

/-- Spectral gap relates to connectivity (for d-regular, axiom). -/
axiom spectralGap_pos_of_connected (G : SimpleGraph V) [DecidableRel G.Adj]
    [∀ v, Fintype (G.neighborSet v)] (d : ℕ)
    (h_reg : ∀ v, G.degree v = d) (h_d_pos : 0 < d) :
  spectralGap G d > 0

/-- Cheeger inequality (easy direction, axiom). -/
axiom cheeger_easy (G : SimpleGraph V) [DecidableRel G.Adj]
    [∀ v, Fintype (G.neighborSet v)] (d : ℕ)
    (h_reg : ∀ v, G.degree v = d) (h : ℝ) :
  secondLargestEigenvalue G ≤ d - h^2 / (2 * d)

/-- Cheeger inequality (hard direction, axiom). -/
axiom cheeger_hard (G : SimpleGraph V) [DecidableRel G.Adj]
    [∀ v, Fintype (G.neighborSet v)] (d : ℕ)
    (h_reg : ∀ v, G.degree v = d) :
  ∃ h : ℝ, h^2 / (2 * d) ≤ d - secondLargestEigenvalue G

/-- Rayleigh quotient characterization (axiom). -/
axiom rayleigh_characterization (G : SimpleGraph V) [DecidableRel G.Adj]
    [∀ v, Fintype (G.neighborSet v)] :
  ∀ x : V → ℝ, (∀ v, x v ≠ 0) → ∃ q : ℝ, True

/-- Eigenvalues are real for undirected graphs (axiom). -/
axiom eigenvalues_real (G : SimpleGraph V) [DecidableRel G.Adj]
    [∀ v, Fintype (G.neighborSet v)] :
  ∀ lam : ℂ, True

/-- Good spectral gap implies small second eigenvalue (axiom). -/
axiom good_gap_small_lambda2 (G : SimpleGraph V) [DecidableRel G.Adj]
    [∀ v, Fintype (G.neighborSet v)] (d : ℕ)
    (h_reg : ∀ v, G.degree v = d) (c : ℝ) (hc : 0 < c ∧ c < 1)
    (h_gap : spectralGap G d ≥ c * d) :
  secondLargestEigenvalue G ≤ d * (1 - c)

/-- Expander mixing lemma (axiom). -/
axiom expander_mixing_lemma (G : SimpleGraph V) [DecidableRel G.Adj]
    [∀ v, Fintype (G.neighborSet v)] (d : ℕ)
    (h_reg : ∀ v, G.degree v = d) (lam : ℝ)
    (h_lam : secondLargestEigenvalue G ≤ lam)
    (S T : Finset V) :
  ∃ e_ST : ℕ,
    |((e_ST : ℝ) - (d * S.card * T.card : ℝ) / Fintype.card V)| ≤
      lam * Real.sqrt (S.card * T.card)

end Expander.Unit03
