/-
  Constraint Graph Definitions
  
  Binary CSP, assignments, satisfaction, UNSAT value
  
  Difficulty: ★★☆☆☆ (2/5)
  Estimated LOC: 200
  Work Package: WP-A
-/

import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Sym.Sym2
import Mathlib.Order.Bounds.Basic
import Mathlib.Tactic

/-!
# Constraint Graph Definitions

Binary CSP (Constraint Satisfaction Problem), assignments, satisfaction, and UNSAT value.

This file defines the core constraint graph structures used in Dinur's gap amplification proof.

## General Proof Strategy Notes

### Axioms Used
- `maxSat`: Computes maximum satisfaction fraction (axiom because it's an optimization problem)
- `maxSat_spec`: States that maxSat is achievable by some assignment and is maximal
- `EdgeC.decidableEq`: Decidable equality for edges (axiom due to function fields in BinRel)

### Key Lemmas Proved (lines 110-156)
1. `satFrac_nonneg`, `satFrac_le_one`: Basic bounds on satisfaction fraction
2. `unsat_bounds`: UNSAT is between 0 and 1
3. `unsat_zero_iff_satisfiable`: UNSAT = 0 iff there exists a fully satisfying assignment

### Tactics and Lemmas That Work
- **Division bounds**: `div_nonneg`, `div_le_iff₀` (note: iff₀, not iff) for rationals
- **Linear arithmetic**: `linarith` for ℚ (NOT `omega`, which only handles Nat/Int)
- **Cardinality**: `Finset.card_filter_le` for filtered subset bounds
- **Witness extraction**: `obtain ⟨x, hx⟩ := spec` to extract existential witnesses
- **Rewriting**: `hσ ▸ lemma` to rewrite with hypothesis before applying lemma

### Pattern for Bounds Proofs
```lean
1. unfold definitions
2. obtain ⟨witness, hwit, hspec⟩ := axiom_spec
3. establish key inequality using previously proved lemmas
4. use `linarith` to combine facts and finish
```

### TODO for Future Work
- Prove `regular_size_bound`: Needs careful Sym2 cardinality counting
- Improve `degree` definition (currently may double-count edges)
- Derive decidability instances properly instead of axiomatizing
-/

/-- Binary constraint on alphabet α: a decidable subset of α × α. -/
structure BinRel (α : Type*) where
  /-- The constraint relation -/
  carrier : α × α → Prop
  /-- The constraint must be decidable -/
  [decidable_carrier : DecidablePred carrier]

attribute [instance] BinRel.decidable_carrier

/-- A labeled edge with a binary constraint. -/
structure EdgeC (V α : Type*) where
  /-- The edge (unordered pair of vertices) -/
  e : Sym2 V
  /-- The constraint on this edge -/
  rel : BinRel α

-- Decidability for EdgeC (axiomatized for simplicity)
axiom EdgeC.decidableEq {V α : Type*} [DecidableEq V] [DecidableEq α] : DecidableEq (EdgeC V α)

attribute [instance] EdgeC.decidableEq

/-- An assignment maps vertices to alphabet symbols. -/
abbrev Assignment (V α : Type*) := V → α

/-- Finite binary CSP on vertices V over alphabet α. -/
structure BinaryCSP (V α : Type*) [Fintype V] [Fintype α] where
  /-- Set of constrained edges -/
  E : Finset (EdgeC V α)
  /-- The CSP must have at least one constraint -/
  nonempty : 0 < E.card

namespace EdgeC

/-- Satisfaction of a single constrained edge by an assignment. -/
def sat {V α : Type*} [DecidableEq V] (σ : Assignment V α) (ec : EdgeC V α) : Prop :=
  ∃ (u v : V), ec.e = s(u, v) ∧ ec.rel.carrier (σ u, σ v)

/-- Decidability instance for edge satisfaction. -/
instance sat_decidable {V α : Type*} [DecidableEq V] [Fintype V]
  (σ : Assignment V α) (ec : EdgeC V α) : Decidable (sat σ ec) := by
  unfold sat
  infer_instance

end EdgeC

namespace BinaryCSP

variable {V α : Type*} [Fintype V] [Fintype α] [DecidableEq V]

/-- Fraction of constraints satisfied by an assignment. -/
def satFrac (G : BinaryCSP V α) (σ : Assignment V α) : ℚ :=
  (G.E.filter (fun ec => EdgeC.sat σ ec)).card / G.E.card

/-- The maximum satisfaction fraction over all assignments.

    Note: This is axiomatized for simplicity. A constructive version could use:
    `Finset.univ.sup' (Fintype.card_pos) (satFrac G)` where `Finset.univ : Finset (V → α)`.
    However, this requires proving `LinearOrder ℚ` properties and decidability,
    so we defer to an axiom for now. -/
axiom maxSat (G : BinaryCSP V α) : ℚ

/-- UNSAT value: minimum fraction of unsatisfied constraints. -/
noncomputable def unsat (G : BinaryCSP V α) : ℚ :=
  1 - maxSat G

/-- Axiom: maxSat returns a valid satisfaction fraction -/
axiom maxSat_spec (G : BinaryCSP V α) :
  ∃ (σ : Assignment V α), satFrac G σ = maxSat G ∧
  ∀ (σ' : Assignment V α), satFrac G σ' ≤ maxSat G

/-!
### Proof Strategy Notes

For rational arithmetic bounds (satFrac, unsat):
- Use `div_nonneg` to show division is non-negative (both arguments must be non-negative)
- Use `div_le_iff₀` (note: iff₀, not iff) for division inequalities with rationals
- `linarith` works well for linear arithmetic over ℚ after establishing key facts
- `Finset.card_filter_le` gives cardinality bounds for filtered Finsets
- `omega` does NOT work with rationals (only Nat/Int), use `linarith` instead
- Extract witnesses from `maxSat_spec` using `obtain`, then rewrite with `hσ ▸`

Pattern for bounds proofs:
1. Unfold definitions
2. Obtain witness from axiom/spec
3. Establish key inequality via previously proved lemmas
4. Use `linarith` to finish
-/

/-- Satisfaction fraction is non-negative. -/
lemma satFrac_nonneg (G : BinaryCSP V α) (σ : Assignment V α) :
  0 ≤ satFrac G σ := by
  unfold satFrac
  apply div_nonneg <;> simp

/-- Satisfaction fraction is bounded by 1. -/
lemma satFrac_le_one (G : BinaryCSP V α) (σ : Assignment V α) :
  satFrac G σ ≤ 1 := by
  unfold satFrac
  -- Key fact: filtered subset has ≤ cardinality
  have h1 : (G.E.filter fun ec => EdgeC.sat σ ec).card ≤ G.E.card := Finset.card_filter_le _ _
  have h2 : (0 : ℚ) < G.E.card := by simp [G.nonempty]
  -- div_le_iff₀ transforms a/b ≤ c into a ≤ b*c (when b > 0)
  rw [div_le_iff₀ h2, one_mul]
  simp [h1]

/-- UNSAT is bounded between 0 and 1. -/
lemma unsat_bounds (G : BinaryCSP V α) : 0 ≤ unsat G ∧ unsat G ≤ 1 := by
  unfold unsat
  -- Extract witness assignment that achieves maxSat
  obtain ⟨σ, hσ, hle⟩ := maxSat_spec G
  constructor
  · -- 0 ≤ 1 - maxSat G, i.e., maxSat G ≤ 1
    have : maxSat G ≤ 1 := hσ ▸ satFrac_le_one G σ  -- Rewrite using witness
    linarith
  · -- 1 - maxSat G ≤ 1, i.e., 0 ≤ maxSat G
    have : 0 ≤ maxSat G := hσ ▸ satFrac_nonneg G σ
    linarith

/-- If all constraints can be satisfied, UNSAT is 0. -/
lemma unsat_zero_iff_satisfiable (G : BinaryCSP V α) :
  unsat G = 0 ↔ ∃ σ : Assignment V α, satFrac G σ = 1 := by
  unfold unsat
  constructor
  · -- unsat G = 0 → ∃ σ, satFrac G σ = 1
    intro h
    obtain ⟨σ, hσ, _⟩ := maxSat_spec G
    use σ
    linarith  -- From h: 1 - maxSat G = 0 and hσ: satFrac σ = maxSat G
  · -- (∃ σ, satFrac G σ = 1) → unsat G = 0
    intro ⟨σ, hσ⟩
    obtain ⟨σ', hσ', hle⟩ := maxSat_spec G
    -- Show maxSat G = 1 by squeezing: maxSat G ≥ 1 (from hle) and maxSat G ≤ 1 (from satFrac_le_one)
    have h1 : maxSat G ≥ 1 := hσ ▸ hle σ
    have h2 : maxSat G ≤ 1 := hσ' ▸ satFrac_le_one G σ'
    linarith  -- Therefore maxSat G = 1, so unsat = 1 - 1 = 0

/-- The number of edges in a CSP. -/
def size (G : BinaryCSP V α) : ℕ := G.E.card

/-- A CSP with more constraints has larger size. -/
lemma size_pos (G : BinaryCSP V α) : 0 < size G := G.nonempty

/-- An assignment satisfies a CSP if it satisfies all constraints (satFrac = 1). -/
def Satisfies (G : BinaryCSP V α) (a : Assignment V α) : Prop :=
  satFrac G a = 1

/-- A CSP checks a constraint between two vertices under an assignment. -/
def ChecksConstraint (G : BinaryCSP V α) (v w : V) (a : Assignment V α) : Prop :=
  ∃ ec ∈ G.E, ec.e = s(v, w) ∧ ec.rel.carrier (a v, a w)

/-- A CSP has spectral expansion lam if its normalized adjacency matrix has
    second-largest eigenvalue (in absolute value) at most lam. -/
def HasExpansion (G : BinaryCSP V α) (lam : ℝ) : Prop :=
  -- TODO: Define properly via spectral properties of adjacency matrix
  -- For now, this is a placeholder
  True

end BinaryCSP

/-!
## Graph Degree and Regularity

Definitions for degree-regular constraint graphs.
-/

namespace BinaryCSP

variable {V α : Type*} [Fintype V] [Fintype α] [DecidableEq V]

/-- The degree of a vertex in a constraint graph (number of constraints involving it).

    Note: Since Sym2 is symmetric (s(v,u) = s(u,v)), we only need one condition. -/
def degree (G : BinaryCSP V α) (v : V) : ℕ :=
  (G.E.filter (fun ec => ∃ u, ec.e = s(v, u))).card

/-- A constraint graph is d-regular if all vertices have degree d. -/
def IsRegular (G : BinaryCSP V α) (d : ℕ) : Prop :=
  ∀ v : V, degree G v = d

/-- Handshaking lemma: sum of degrees equals twice the number of edges.

    Requires that the graph has no self-loops (edges of the form s(v,v)). -/
lemma sum_degrees_eq_twice_size (G : BinaryCSP V α)
    (no_loops : ∀ ec ∈ G.E, ¬ec.e.IsDiag) :
  (Finset.univ.sum (degree G)) = 2 * size G := by
  unfold size degree
  -- Strategy: Show that ∑_v |{e ∈ E : v ∈ e}| = ∑_{e ∈ E} |{v : v ∈ e}|
  -- For each edge e = s(a,b) with a ≠ b, there are exactly 2 distinct vertices

  -- Rewrite the sum as a double count over (vertex, edge) pairs
  have key : Finset.univ.sum (fun v => (G.E.filter (fun ec => ∃ u, ec.e = s(v, u))).card) =
             (G.E.sum fun ec => (Finset.univ.filter (fun v => ∃ u, ec.e = s(v, u))).card) := by
    -- This is a sum exchange: we're counting (v, ec) pairs where v is incident to ec
    -- Both sides count the same set of pairs, just in different orders
    -- TODO: This is a standard combinatorial identity (Fubini for finite sums)
    -- A complete proof would use Finset.card_sigma and a bijection
    sorry

  rw [key]
  -- Helper lemma: for any non-diagonal s(a,b), the filter has exactly 2 elements
  have pair_filter_card : ∀ (a b : V), a ≠ b →
      (Finset.univ.filter (fun v => ∃ u, s(a, b) = s(v, u))).card = 2 := by
    intro a b hab
    -- Key equivalence: ∃ u, s(a,b) = s(v,u) ↔ v = a ∨ v = b
    have mem_equiv : ∀ v, (∃ u, s(a, b) = s(v, u)) ↔ (v = a ∨ v = b) := fun v => by
      simp only [Sym2.eq, Sym2.rel_iff]
      constructor
      · intro ⟨u, h⟩
        -- h : (a, b) = (v, u) ∨ (a, b) = (u, v)
        cases h with
        | inl heq =>
          -- heq : a = v ∧ b = u, so a = v
          exact Or.inl heq.1.symm
        | inr heq =>
          -- heq : a = u ∧ b = v, so b = v
          exact Or.inr heq.2.symm
      · intro h
        cases h with
        | inl heq =>
          -- v = a, pick u = b to get s(a, b) = s(v, b)
          use b
          left
          exact ⟨heq.symm, rfl⟩
        | inr heq =>
          -- v = b, pick u = a to get s(a, b) = s(a, v) = s(v, a)
          use a
          right
          exact ⟨rfl, heq.symm⟩
    -- Rewrite the filter using equivalence
    calc (Finset.univ.filter (fun v => ∃ u, s(a, b) = s(v, u))).card
        = (Finset.univ.filter (fun v => v = a ∨ v = b)).card := by
            congr 1; ext v
            simp only [Finset.mem_filter, Finset.mem_univ, true_and]
            exact mem_equiv v
      _ = ({a, b} : Finset V).card := by
            congr 1; ext v
            simp only [Finset.mem_filter, Finset.mem_univ, true_and,
                       Finset.mem_insert, Finset.mem_singleton]
      _ = 2 := Finset.card_pair hab

  -- Now show that for each non-diagonal edge ec, exactly 2 vertices are members
  have all_edges_have_two_vertices : ∀ ec ∈ G.E,
      (Finset.univ.filter (fun v => ∃ u, ec.e = s(v, u))).card = 2 := by
    intro ec hec
    -- TODO: Use Sym2.inductionOn to pattern match ec.e as s(a,b)
    -- Then apply pair_filter_card above, deriving a ≠ b from no_loops
    -- See lines 260-297 for the proof pattern on a concrete edge
    sorry

  -- Therefore ∑_{e ∈ E} 2 = 2 * |E|
  simp_rw [Finset.sum_congr rfl all_edges_have_two_vertices]
  rw [Finset.sum_const]
  simp [mul_comm]

/-- Regular graphs have bounded size (assuming no self-loops). -/
lemma regular_size_bound (G : BinaryCSP V α) (d : ℕ)
    (no_loops : ∀ ec ∈ G.E, ¬ec.e.IsDiag) (h : IsRegular G d) :
  size G ≤ d * (Fintype.card V) / 2 := by
  unfold size IsRegular at *
  -- Use handshaking lemma
  have hs : (Finset.univ.sum (degree G)) = 2 * G.E.card := sum_degrees_eq_twice_size G no_loops
  -- All vertices have degree d
  have hd : Finset.univ.sum (degree G) = d * Fintype.card V := by
    calc Finset.univ.sum (degree G)
      _ = Finset.univ.sum (fun _ => d) := Finset.sum_congr rfl (fun v _ => h v)
      _ = d * Fintype.card V := by rw [Finset.sum_const, Finset.card_univ]; ring
  -- Combine: d * |V| = 2 * |E|, so |E| = d * |V| / 2
  omega

end BinaryCSP

/-!
## 3-Colorability Reduction

Reduction from 3-Colorability to 2-CSP satisfiability.
This establishes NP-hardness of the constraint graph satisfiability problem.

Reference: Dinur, Proposition 1.4 (p. 3)
-/

section ThreeColoring

/-- A finite simple graph for 3-coloring reduction. -/
structure Graph3Color (V : Type*) [DecidableEq V] where
  /-- Edge set as finite set of unordered pairs -/
  E : Finset (Sym2 V)

/-- The three colors for graph coloring. -/
inductive Color
  | red : Color
  | green : Color
  | blue : Color
  deriving DecidableEq, Fintype

/-- A graph is 3-colorable if vertices can be colored with 3 colors such that
    adjacent vertices have different colors. -/
def Graph3Color.is3Colorable {V : Type*} [DecidableEq V] (G : Graph3Color V) : Prop :=
  ∃ (c : V → Color), ∀ e ∈ G.E, ∃ u v, e = s(u, v) ∧ c u ≠ c v

/-- The inequality constraint (not equal) on colors. -/
def neqRel : BinRel Color where
  carrier := fun (c₁, c₂) => c₁ ≠ c₂
  decidable_carrier := inferInstance

/-- Convert a graph to a binary CSP where edges have "not equal" constraints. -/
def graphToCSP {V : Type*} [Fintype V] [DecidableEq V] (G : Graph3Color V)
    (hne : 0 < G.E.card) : BinaryCSP V Color where
  E := G.E.map ⟨fun e => EdgeC.mk e neqRel, fun e₁ e₂ h => by
    -- If EdgeC.mk e₁ neqRel = EdgeC.mk e₂ neqRel, then e₁ = e₂
    injection h with h_e⟩
  nonempty := by
    rw [Finset.card_map]
    exact hne

/-- The reduction is correct: a graph is 3-colorable iff the corresponding CSP has UNSAT = 0. -/
theorem threeColor_to_csp_correct {V : Type*} [Fintype V] [DecidableEq V]
    (G : Graph3Color V) (hne : 0 < G.E.card) :
    G.is3Colorable ↔ (graphToCSP G hne).unsat = 0 := by
  constructor
  · -- If 3-colorable, then UNSAT = 0
    intro ⟨c, hc⟩
    rw [BinaryCSP.unsat_zero_iff_satisfiable]
    use c
    unfold BinaryCSP.satFrac graphToCSP
    -- Need to show: all CSP edges are satisfied by c
    -- i.e., (filtered edges).card = (all edges).card
    simp only [Finset.card_map]
    -- Show that every edge in the CSP is satisfied
    have all_sat : ∀ ec ∈ (G.E.map ⟨fun e => EdgeC.mk e neqRel, fun e₁ e₂ h => by injection h⟩), EdgeC.sat c ec := by
      intro ec hec
      simp only [Finset.mem_map] at hec
      obtain ⟨e, he, rfl⟩ := hec
      -- e is an edge in G.E, so by hc we have endpoints with different colors
      obtain ⟨u, v, rfl, huv⟩ := hc e he
      -- Show EdgeC.sat c (EdgeC.mk s(u,v) neqRel)
      unfold EdgeC.sat neqRel BinRel.carrier
      use u, v
      constructor
      · rfl
      · exact huv
    -- Therefore the filter is everything
    have : (G.E.map ⟨fun e => EdgeC.mk e neqRel, fun e₁ e₂ h => by injection h⟩).filter (EdgeC.sat c) =
           (G.E.map ⟨fun e => EdgeC.mk e neqRel, fun e₁ e₂ h => by injection h⟩) := by
      apply Finset.filter_true_of_mem all_sat
    rw [this]
    simp only [Finset.card_map]
    have h_ne_zero : (G.E.card : ℚ) ≠ 0 := by
      simp only [ne_eq, Nat.cast_eq_zero]
      omega
    field_simp [h_ne_zero]
  · -- If UNSAT = 0, then 3-colorable
    intro h
    rw [BinaryCSP.unsat_zero_iff_satisfiable] at h
    obtain ⟨σ, hσ⟩ := h
    use σ
    intro e he
    unfold BinaryCSP.satFrac graphToCSP at hσ
    simp only [Finset.card_map] at hσ

    -- TODO: Fix pattern matching on Sym2
    sorry

end ThreeColoring
