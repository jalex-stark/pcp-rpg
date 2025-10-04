# Inhuman Lean Style Guide

## Purpose

This style guide defines the **machine-optimized** coding conventions for automated Lean 4 proof generation in the PCP-RPG project. These rules maximize automation success rates by constraining proofs to be short, deterministic, and locally self-contained.

**Key principle:** Optimize for automation, not human elegance. Redundancy is encouraged. Human-readable exports go in separate `API.lean` files.

---

## Core Rules

### 1. Use `lemma`, Never `theorem`

All results must be stated as `lemma`. This keeps indexing simple and signals these are building blocks, not final results.

```lean
-- ✓ Good
lemma add_comm_variant {G : Type} [AddCommSemigroup G] (a b : G) :
    a + b = b + a := by
  simpa [add_comm]

-- ✗ Bad - don't use theorem
theorem add_comm_variant ...
```

### 2. Tactic Budget: ≤ 5 Lines Per Proof

**Hard limit:** Each lemma proof must be ≤ 5 tactic lines (configurable per unit in `unit.yaml`).

If a proof exceeds this, **fail fast** and request decomposition into auxiliary lemmas.

```lean
-- ✓ Good - 3 tactics
lemma satFrac_nonneg {G : ConstraintGraph} : 0 ≤ satFrac G := by
  unfold satFrac
  apply div_nonneg <;> norm_cast
  exact Finset.card_nonneg

-- ✗ Bad - too long, needs aux lemmas
lemma complex_proof : ... := by
  intro x
  cases x
  constructor
  · apply foo
    rw [bar, baz]
    simp [...]
  · ...  -- exceeds budget!
```

### 3. Tactic Whitelist (Deterministic Only)

**Allowed tactics:**
- `simp [explicit_lemmas]` - with explicit simp set
- `simpa [...]` - simp + assumption
- `rw [lemma1, lemma2]` - explicit rewrites
- `apply`, `refine`, `refine'`
- `constructor`, `intro`, `intros`
- `cases`, `induction` (simple patterns only)
- `unfold` - for definitions
- `exact` - explicit terms
- `norm_cast`, `norm_num` - normalization
- `ring`, `ring_nf` - when obviously correct
- `linarith` - for linear arithmetic
- `omega` - for Nat/Int arithmetic
- `decide` - for decidable props

**Banned tactics (non-deterministic/exploratory):**
- `simp?`, `aesop?`, `linarith?` - no suggestion tactics
- `simp_all` - too broad
- `by_cases` - unless absolutely necessary (adds branching)
- `tauto`, `finish` - deprecated/unpredictable
- `tactic'` - no tactic composition
- Long `<;>` chains - prefer explicit steps

**Rationale:** Exploratory tactics waste prover time and reduce reproducibility.

### 4. One Tactic Per Line

Use `by` blocks with one tactic per line. Avoid `;` chaining (except simple cases like `<;> norm_cast`).

```lean
-- ✓ Good
lemma foo : ... := by
  unfold bar
  apply baz
  simpa

-- ✗ Bad - hard to debug
lemma foo : ... := by unfold bar; apply baz; simpa
```

### 5. Top-Level Lemmas Only (No `where` Helpers)

All lemmas must be **top-level**. Never use `where` clauses or local helpers.

Reason: Our specialized prover (`bin/copilot-prove`) targets top-level declarations only.

```lean
-- ✓ Good - aux lemma is top-level
lemma aux_step {G : Type} [Group G] (a b : G) : a * b⁻¹ * b = a := by
  simp [mul_inv_cancel_right]

lemma main_result {G : Type} [Group G] (a b c : G) : ... := by
  rw [aux_step]
  ...

-- ✗ Bad - where clause
lemma main_result ... := by
  ...
  where aux_step := ...
```

### 6. Repeat Hypotheses (No Cross-Lemma Local Context)

Each lemma must be **self-contained**. Repeat type class assumptions and hypotheses explicitly. Do not rely on `variable` or `section` context.

```lean
-- ✓ Good - self-contained
lemma cancel_left {G : Type} [Group G] (a b c : G) (h : a * b = a * c) : b = c := by
  simpa using mul_left_cancel h

-- ✗ Bad - relies on section variables
section MySection
variable {G : Type} [Group G]

lemma cancel_left (a b c : G) (h : a * b = a * c) : b = c := ...
end MySection
```

### 7. Explicit Type Class Binders

Always include explicit type class assumptions at the lemma head. Do not rely on instance inference across lemmas.

```lean
-- ✓ Good
lemma degree_pos {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (v : V) (hv : v ∈ G.support) :
    0 < G.degree v := by
  ...

-- ✗ Bad - missing explicit binders
lemma degree_pos (G : SimpleGraph V) (v : V) (hv : v ∈ G.support) : ... := by
  ...
```

### 8. Deterministic Naming Convention

Use systematic, deterministic names:
- Namespace: `{Unit}.{Topic}`
- Pattern: `{concept}_{property}_{variant}`
- Index variants: `foo_1`, `foo_2`, `foo_alt`, `foo'`

```lean
namespace ConstraintGraph.Unit01

lemma satFrac_nonneg : ...
lemma satFrac_le_one : ...
lemma satFrac_eq_zero_iff : ...
lemma degree_pos_of_incident : ...
lemma degree_pos_of_incident_alt : ...  -- redundant variant OK

end ConstraintGraph.Unit01
```

### 9. Minimal Imports

Import only what's needed for the unit. Declare imports in `unit.yaml`.

```lean
-- ✓ Good - targeted
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.Order.Field.Defs

-- ✗ Bad - too broad
import Mathlib
```

### 10. Sparing Use of Attributes

- `[simp]` - only on safe normal forms (commutativity, associativity, identities)
- `[simp, norm_cast]` - for casting lemmas
- Avoid `[instance]` in slop files (put in API.lean if needed)

```lean
-- ✓ Good
@[simp]
lemma add_zero' {M : Type} [AddMonoid M] (a : M) : a + 0 = a := by
  simpa

-- ✗ Bad - aggressive simp can break things
@[simp]
lemma complex_rewrite ... := ...
```

### 11. One-Line Docstrings

Each lemma gets a one-line docstring. Detailed docs go in `API.lean`.

```lean
/-- Left cancellation for addition. -/
lemma add_left_cancel' {G : Type} [AddLeftCancelSemigroup G]
    {a b c : G} (h : a + b = a + c) : b = c := by
  simpa using add_left_cancel h
```

### 12. Redundancy is a Feature

**Do not deduplicate within slop files.** If a lemma can be stated multiple ways, write all variants.

Curation happens in `API.lean`, not during generation.

```lean
-- Both OK - redundancy helps automation
lemma add_comm_1 {G : Type} [AddCommSemigroup G] (a b : G) : a + b = b + a := by
  simpa [add_comm]

lemma add_comm_2 {G : Type} [AddCommSemigroup G] (a b : G) : a + b = b + a := by
  rw [add_comm]
```

---

## Example: Good Slop File

```lean
import Mathlib.Algebra.Group.Defs
import Mathlib.Data.Finset.Card

namespace ConstraintGraph.Unit01

/-- Satisfaction fraction is nonnegative. -/
lemma satFrac_nonneg {G : ConstraintGraph} : 0 ≤ satFrac G := by
  unfold satFrac
  apply div_nonneg <;> norm_cast
  exact Finset.card_nonneg

/-- Satisfaction fraction is at most one. -/
lemma satFrac_le_one {G : ConstraintGraph} : satFrac G ≤ 1 := by
  unfold satFrac
  apply div_le_one_of_le <;> norm_cast
  apply Finset.card_le_card
  exact Finset.filter_subset _ _

/-- Degree is positive for vertices with incident edges. -/
lemma degree_pos_of_incident {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {v : V} (e : Sym2 V)
    (he : e ∈ G.edgeSet) (hv : v ∈ e) : 0 < G.degree v := by
  apply Finset.card_pos.mpr
  obtain ⟨u, hu⟩ := Sym2.exists_other_mem hv
  use u
  simp [SimpleGraph.mem_neighborFinset, SimpleGraph.mem_edgeSet]
  exact ⟨hu.1, Or.inl ⟨e, he, hu.2⟩⟩

end ConstraintGraph.Unit01
```

---

## Example: Bad Slop File (Don't Do This)

```lean
-- ✗ Multiple violations!

import Mathlib  -- too broad

-- Uses theorem instead of lemma
theorem my_result : ... := by
  simp?  -- exploratory tactic
  by_cases h : ...  -- branching
  · sorry  -- incomplete
  · have aux := ... where  -- local helper
      aux := ...  -- not top-level
    ...  -- exceeds 5 lines

-- Missing docstring
lemma another_result : ... := by
  simp; rw [foo]; apply bar; constructor; exact baz; done  -- chained, hard to debug
```

---

## Enforcement

1. **Decomposer agent** must generate code following these rules
2. **Prover agent** fails fast if proof exceeds tactic budget
3. **Failure analyst** proposes fixes within these constraints
4. **CI** runs linters to check compliance (future work)

---

## When to Bend the Rules

These rules apply to **slop files** (`Slop_*.lean`).

In **API files** (`API.lean`), you may:
- Use longer proofs (if stable)
- Add detailed docstrings
- Use `theorem` for main results
- Apply human-readable formatting

But API files should mostly **re-export** proven lemmas from slop files, not prove things from scratch.

---

## Relation to RPG Graph

- Each RPG node → one or more units
- Unit difficulty rating → tactic budget (harder problems get more tactics)
- Node tags → routing heuristics (`heuristics.yaml`)
- Node dependencies → import structure between units

---

## Success Metrics

A good slop file:
- **High win rate** - prover closes >80% of lemmas on first try
- **Short proofs** - avg ≤ 3 tactics per lemma
- **Fast proving** - <10s per lemma with Copilot
- **Low churn** - minimal edits after initial generation

If win rate is low, **decompose further**, don't relax rules.
