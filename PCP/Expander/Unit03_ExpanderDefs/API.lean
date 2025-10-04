import Mathlib
import PCP.Expander.Unit03_ExpanderDefs.Slop_Combinatorial
import PCP.Expander.Unit03_ExpanderDefs.Slop_Spectral
import PCP.Expander.Unit03_ExpanderDefs.Slop_Families

/-!
# API: Expander Graph Definitions

Core definitions for expander graphs.

Expander graphs are sparse yet highly connected graphs with strong
expansion properties. They are fundamental to Dinur's PCP proof.

This module provides:
- Combinatorial expansion definitions (vertex and edge expansion)
- Spectral characterization (λ₂ bounds and spectral gap)
- Explicit family interface for constructible expander sequences

## Main Results

### Combinatorial Expansion
- `IsExpander`: Definition of (d, λ)-expander graphs
- `vertexExpansionOf`: Vertex expansion ratio |∂S| / |S|
- `edgeExpansionOf`: Edge expansion ratio |∂_E(S)| / |S|
- `expansionConstant`: Minimum expansion over all small sets

### Spectral Properties
- `spectralGap`: Spectral gap d - λ₂ for d-regular graphs
- `secondLargestEigenvalue`: Second-largest eigenvalue λ₂
- `spectralGap_nonneg`: Spectral gap is non-negative

### Expander Families
- `ExpanderFamily`: Sequence of expanders with uniform parameters
- `IsExplicitFamily`: Polynomial-time constructible families
- `family_member_is_expander`: Every family member is an expander
- `explicit_degree3_exists`: Explicit degree-3 expanders exist

## Usage

```lean
import PCP.Expander.Unit03_ExpanderDefs.API

open Expander.Unit03

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [∀ v, Fintype (G.neighborSet v)]

-- Check if a graph is an expander
example (d : ℕ) (λ : ℝ) (h_reg : ∀ v, G.degree v = d)
    (h_d : 0 < d) (h_λ : 0 < λ) :
    IsExpander G d λ :=
  ⟨h_reg, h_d, h_λ⟩

-- Vertex expansion is non-negative
example (S : Finset V) : 0 ≤ vertexExpansionOf G S :=
  vertexExpansionOf_nonneg

-- Use explicit expander families
example : ∃ family : ExpanderFamily, family.d = 3 ∧ IsExplicitFamily family :=
  explicit_degree3_exists
```
-/

namespace Expander.Unit03

-- Combinatorial Expansion
-- ========================

/-- A graph is an (n, d, λ)-expander if it is d-regular with spectral parameter λ. -/
export Expander.Unit03 (IsExpander)

/-- Vertex expansion ratio for a set S: |∂S| / |S|. -/
export Expander.Unit03 (vertexExpansionOf)

/-- Edge expansion ratio for a set S: |∂_E(S)| / |S|. -/
export Expander.Unit03 (edgeExpansionOf)

/-- The expansion constant: minimum expansion over all small sets. -/
export Expander.Unit03 (expansionConstant)

/-- Vertex expansion ratio is non-negative. -/
export Expander.Unit03 (vertexExpansionOf_nonneg)

/-- Edge expansion ratio is non-negative. -/
export Expander.Unit03 (edgeExpansionOf_nonneg)

/-- Empty set has zero vertex expansion. -/
export Expander.Unit03 (vertexExpansionOf_empty)

/-- Empty set has zero edge expansion. -/
export Expander.Unit03 (edgeExpansionOf_empty)

/-- Expander property implies positive degree. -/
alias expander_degree_pos := IsExpander_degree_pos

/-- Expander property implies positive spectral parameter. -/
alias expander_lam_pos := IsExpander_lam_pos

/-- Small sets in expanders have good expansion (qualitative). -/
export Expander.Unit03 (expander_small_set_expansion)

/-- Expansion implies large boundary (qualitative). -/
export Expander.Unit03 (expansion_large_boundary)


-- Spectral Gap
-- ============

/-- The spectral gap of a d-regular graph: gap(G) = d - λ₂(G). -/
export Expander.Unit03 (spectralGap)

/-- The second-largest eigenvalue of the adjacency matrix. -/
export Expander.Unit03 (secondLargestEigenvalue)

/-- Spectral gap is non-negative for regular graphs. -/
export Expander.Unit03 (spectralGap_nonneg)


-- Axiomatized Spectral Properties
-- ================================

/-- For d-regular graphs, largest eigenvalue is d. -/
export Expander.Unit03 (regular_largest_eigenvalue)

/-- Spectral gap relates to second eigenvalue: gap = d - λ₂. -/
export Expander.Unit03 (spectralGap_eq_d_minus_lambda2)

/-- Spectral gap at most d for regular graphs. -/
export Expander.Unit03 (spectralGap_le_d)

/-- Second eigenvalue bounds: -d ≤ λ₂ ≤ d. -/
export Expander.Unit03 (secondLargestEigenvalue_bounds)

/-- Cheeger inequality (easy direction): λ₂ ≤ d - h²/(2d). -/
export Expander.Unit03 (cheeger_easy)

/-- Expander mixing lemma: bounds on edge counts between sets. -/
export Expander.Unit03 (expander_mixing_lemma)


-- Explicit Families
-- =================

/-- An expander family is a sequence of expanders with uniform parameters. -/
export Expander.Unit03 (ExpanderFamily)

/-- An explicit family is constructible in polynomial time. -/
export Expander.Unit03 (IsExplicitFamily)

/-- Every expander family member is an expander. -/
export Expander.Unit03 (family_member_is_expander)

/-- Explicit families are polynomial-time constructible. -/
export Expander.Unit03 (explicit_family_poly_time)

/-- Explicit degree-3 expanders exist. -/
export Expander.Unit03 (explicit_degree3_exists)

/-- Explicit degree-d expanders exist for any d ≥ 3. -/
export Expander.Unit03 (explicit_degree_d_exists)

/-- Degree is constant across family. -/
export Expander.Unit03 (family_degree_constant)

/-- Spectral gap is uniform across family. -/
export Expander.Unit03 (family_spectral_uniform)

/-- Expander families have unbounded size. -/
export Expander.Unit03 (family_unbounded)

/-- Explicit families satisfy size requirements for PCP. -/
export Expander.Unit03 (explicit_family_pcp_suitable)


-- Axiomatized Existence Results
-- ==============================

/-- Constant degree expander families exist (axiom). -/
alias constantDegreeExpanderExists := Expander.Unit03.constantDegreeExpanderExists

/-- Explicit constant degree families exist (axiom). -/
alias explicitExpanderExists := Expander.Unit03.explicitExpanderExists

/-- Ramanujan graphs are optimal expanders (axiom). -/
alias ramanujanGraphsExist := Expander.Unit03.ramanujanGraphsExist

end Expander.Unit03
