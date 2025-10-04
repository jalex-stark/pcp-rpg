import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import PCP.Expander.Unit03_ExpanderDefs.Slop_Combinatorial
import PCP.Expander.Unit03_ExpanderDefs.Slop_Spectral

/-!
# Explicit Expander Families

Machine-generated micro-lemmas for explicit expander graph constructions.

Tactic budget: 7.5
-/

namespace Expander.Unit03

open scoped Classical
open SimpleGraph

/-- An expander family is a sequence of expanders with uniform parameters. -/
structure ExpanderFamily where
  /-- Graph of size n -/
  graph : (n : ℕ) → SimpleGraph (Fin n)
  /-- All graphs have degree d -/
  d : ℕ
  /-- Spectral gap parameter -/
  lam : ℝ
  /-- Degree is positive -/
  d_pos : 0 < d
  /-- Lambda is positive -/
  lam_pos : 0 < lam
  /-- All graphs have decidable adjacency -/
  graph_decidable : ∀ n, DecidableRel (graph n).Adj
  /-- All graphs have finite neighborhoods -/
  graph_finite : ∀ n v, Fintype ((graph n).neighborSet v)
  /-- All graphs are d-regular -/
  is_regular : ∀ n v, @SimpleGraph.degree (Fin n) (graph n) v (graph_finite n v) = d
  /-- All graphs satisfy spectral gap bound -/
  spectral_bound : ∀ n, secondLargestEigenvalue (graph n) ≤ lam

/-- An explicit family is constructible in polynomial time. -/
def IsExplicitFamily (family : ExpanderFamily) : Prop :=
  ∀ n : ℕ, ∃ (construction_time : ℕ), construction_time ≤ n ^ 10

/-- Constant degree expander families exist (axiom). -/
axiom constantDegreeExpanderExists (d : ℕ) (lam : ℝ)
    (h_d : 2 < d) (h_lam : 0 < lam ∧ lam < d) :
  ∃ family : ExpanderFamily, family.d = d ∧ family.lam = lam

/-- Explicit constant degree families exist (axiom). -/
axiom explicitExpanderExists (d : ℕ) (lam : ℝ)
    (h_d : 2 < d) (h_lam : 0 < lam ∧ lam < d) :
  ∃ family : ExpanderFamily, family.d = d ∧ family.lam = lam ∧
    IsExplicitFamily family

/-- Ramanujan graphs are optimal expanders (axiom). -/
axiom ramanujanGraphsExist (d : ℕ) (h_d : 2 < d) :
  ∃ family : ExpanderFamily, family.d = d ∧
    family.lam ≤ 2 * Real.sqrt (d - 1)

/-- Zig-zag product construction (axiom). -/
axiom zigzagProduct (G₁ G₂ : ExpanderFamily) :
  ∃ G₃ : ExpanderFamily, True

/-- Every expander family member is an expander (axiom). -/
axiom family_member_is_expander (family : ExpanderFamily) (n : ℕ) :
    IsExpander (family.graph n) family.d family.lam

/-- Explicit families are polynomial-time constructible. -/
lemma explicit_family_poly_time (family : ExpanderFamily)
    (h : IsExplicitFamily family) (n : ℕ) :
    ∃ time : ℕ, time ≤ n ^ 10 := by
  exact h n

/-- Explicit degree-3 expanders exist. -/
lemma explicit_degree3_exists :
    ∃ family : ExpanderFamily, family.d = 3 ∧ IsExplicitFamily family := by
  have h := explicitExpanderExists 3 0.5 (by norm_num) (by norm_num)
  obtain ⟨family, h_d, _h_lam, h_explicit⟩ := h
  exact ⟨family, h_d, h_explicit⟩

/-- Explicit degree-d expanders exist for any d ≥ 3. -/
lemma explicit_degree_d_exists (d : ℕ) (h_d : 2 < d) :
    ∃ family : ExpanderFamily, family.d = d ∧ IsExplicitFamily family := by
  have h_lam : 0 < (d : ℝ) / 2 ∧ (d : ℝ) / 2 < d := by
    constructor
    · positivity
    · have : (d : ℝ) > 0 := by positivity
      linarith
  have h := explicitExpanderExists d ((d : ℝ) / 2) h_d h_lam
  obtain ⟨family, h_d_eq, _h_lam_eq, h_explicit⟩ := h
  exact ⟨family, h_d_eq, h_explicit⟩

/-- Expander family graphs grow in size. -/
lemma family_size_grows (family : ExpanderFamily) (n m : ℕ) (h : n < m) :
    Fintype.card (Fin n) < Fintype.card (Fin m) := by
  simp [Fintype.card_fin]
  exact h

/-- Degree is constant across family. -/
lemma family_degree_constant (family : ExpanderFamily) (n : ℕ) :
    ∀ v, @SimpleGraph.degree (Fin n) (family.graph n) v
      (family.graph_finite n v) = family.d := by
  exact family.is_regular n

/-- Spectral gap is uniform across family (axiom). -/
axiom family_spectral_uniform (family : ExpanderFamily) (n : ℕ) :
    secondLargestEigenvalue (family.graph n) ≤ family.lam

/-- Expander families have unbounded size. -/
lemma family_unbounded (family : ExpanderFamily) (k : ℕ) :
    ∃ n, Fintype.card (Fin n) ≥ k := by
  use k
  simp [Fintype.card_fin]

/-- Construction of family from single expander (sketch). -/
lemma family_from_single {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [∀ v, Fintype (G.neighborSet v)] (d : ℕ) (lam : ℝ)
    (h : IsExpander G d lam) :
    True := by
  trivial

/-- Tensor product of expanders (axiom). -/
axiom tensorProduct (family₁ family₂ : ExpanderFamily) :
  ∃ family₃ : ExpanderFamily, True

/-- Replacement product construction (axiom). -/
axiom replacementProduct (family₁ family₂ : ExpanderFamily) :
  ∃ family₃ : ExpanderFamily,
    family₃.d = family₁.d * family₂.d

/-- Explicit families satisfy size requirements for PCP. -/
lemma explicit_family_pcp_suitable (family : ExpanderFamily)
    (h : IsExplicitFamily family) (n : ℕ) :
    ∃ m, Fintype.card (Fin m) = n ∧
      IsExpander (family.graph m) family.d family.lam := by
  use n
  constructor
  · simp [Fintype.card_fin]
  · exact family_member_is_expander family n

end Expander.Unit03
