# Lean 4 Proof Strategies for PCP Formalization

Documentation of tactics, lemmas, and patterns discovered during formalization.

## Quick Reference

### Tactics by Use Case

| Goal Type | Recommended Tactics | Notes |
|-----------|-------------------|-------|
| Rational inequalities | `linarith` | After establishing key facts |
| Natural number arithmetic | `omega` or `linarith` | `omega` doesn't work for ℚ |
| Division bounds | `div_nonneg`, `div_le_iff₀` | Note: `iff₀` not `iff` |
| Cardinality | `Finset.card_filter_le` | Filtered subset ≤ original |
| Simplification | `simp` | More reliable than `decide` with axioms |
| Witness extraction | `obtain ⟨x, hx⟩ := spec` | From existential specs |
| Rewriting with hypothesis | `hσ ▸ lemma` | Apply lemma after rewrite |

### Common Pitfalls

1. **`omega` doesn't work with rationals** - Use `linarith` instead
2. **`div_le_iff` vs `div_le_iff₀`** - For rationals, need `div_le_iff₀`
3. **`decide` fails with axiomatized instances** - Use `simp` or manual proofs
4. **Finset construction** - Use `List.toFinset`, not direct `insert`
5. **Sym2 equality** - Often needs explicit witness construction, not automation

## Detailed Strategies

### 1. Proving Bounds on Fractions (PCP/ConstraintGraph/Defs.lean:110-156)

**Pattern:**
```lean
lemma fraction_bound (G : BinaryCSP V α) : 0 ≤ some_fraction G ∧ some_fraction G ≤ 1 := by
  unfold some_fraction
  obtain ⟨witness, hwit_eq, hwit_max⟩ := spec_axiom G
  constructor
  · have : key_fact := hwit_eq ▸ previously_proved_lemma G witness
    linarith
  · have : other_fact := hwit_eq ▸ other_lemma G witness
    linarith
```

**Key techniques:**
- Extract witnesses from axiom specs using `obtain`
- Establish bounds using previously proved lemmas
- Rewrite with `▸` before applying lemmas
- Use `linarith` to combine linear facts

**Example:** `satFrac_nonneg`, `unsat_bounds`

### 2. Working with Finsets (PCP/ConstraintGraph/Examples.lean)

**Problem:** Need to construct `Finset (EdgeC V α)` but `EdgeC` contains function fields

**Solutions:**

#### Option A: List.toFinset (Used)
```lean
noncomputable def my_csp : BinaryCSP V α := {
  E := [edge1, edge2, edge3].toFinset
  nonempty := by simp  -- not `decide`!
}
```
- Requires `DecidableEq (EdgeC V α)`
- Must axiomatize if EdgeC contains functions
- Mark definition as `noncomputable`

#### Option B: Finset.mk (Not used, but possible)
```lean
def my_csp : BinaryCSP V α := {
  E := Finset.mk ⟨[edge1, edge2, edge3], by simp⟩ (by simp)
  nonempty := by simp
}
```

### 3. Division Inequalities with Rationals

**Goal:** Prove `a / b ≤ c` where `a, b, c : ℚ`

**Strategy:**
```lean
have h_pos : (0 : ℚ) < b := by simp [...]  -- Prove denominator positive
rw [div_le_iff₀ h_pos, mul_comm]           -- Transform to `a ≤ b * c`
have h_bound : a ≤ b * c := ...            -- Prove transformed goal
exact h_bound
```

**Key points:**
- Must prove denominator positive first
- Use `div_le_iff₀` (with zero subscript) for rationals
- Consider using `mul_comm` to match goal shape

**Example:** `satFrac_le_one`

### 4. Extracting Witnesses from Existential Axioms

**Pattern:**
```lean
axiom my_spec (x : α) : ∃ (y : β), P y ∧ Q y

lemma uses_spec (x : α) : R x := by
  obtain ⟨y, hy_P, hy_Q⟩ := my_spec x
  -- Now have: hy_P : P y, hy_Q : Q y
  -- Use these to prove R x
  ...
```

**Example:** `maxSat_spec` provides witness assignment achieving maximum satisfaction

### 5. Building Concrete Examples

**Checklist:**
1. Define relation with `DecidablePred` instance
2. Create edges using `s(v1, v2)` notation for Sym2
3. Build Finset using `List.toFinset`
4. Mark CSP definition as `noncomputable`
5. Use `simp` (not `decide`) for `nonempty` proof

**Example structure:**
```lean
def my_rel : BinRel α where
  carrier := fun (a, b) => ...
  decidable_carrier := by infer_instance

def my_edge : EdgeC V α := {
  e := s(0, 1)
  rel := my_rel
}

noncomputable def my_csp : BinaryCSP V α := {
  E := [my_edge, ...].toFinset
  nonempty := by simp
}
```

## Files with Proof Strategy Comments

1. **PCP/ConstraintGraph/Defs.lean** (lines 26-57, 127-162)
   - General strategy overview
   - Detailed inline comments on each proved lemma
   - Pattern for bounds proofs

2. **PCP/ConstraintGraph/Examples.lean** (lines 10-46)
   - Finset construction strategies
   - Decidability issues and solutions
   - Working with Sym2

## Future Improvements

### Short Term
- Complete example proofs (currently `sorry`)
- Prove `regular_size_bound` (needs Sym2 counting)
- Fix degree definition (may double-count)

### Medium Term
- Derive `DecidableEq (EdgeC V α)` properly instead of axiomatizing
- Add more complex examples (e.g., 3-coloring, SAT reduction)
- Prove composition properties of CSPs

### Long Term
- Implement actual graph powering construction
- Prove gap amplification lemmas
- Complete Dinur's main theorem

## References

- [Lean 4 Manual](https://lean-lang.org/lean4/doc/)
- [Mathlib4 Docs](https://leanprover-community.github.io/mathlib4_docs/)
- [Tactics Reference](https://leanprover-community.github.io/mathlib4_docs/tactics.html)
- Dinur's Paper: "The PCP theorem by gap amplification"

## Contributing

When adding new proofs:
1. Document non-obvious tactics in inline comments
2. Note any lemmas that work differently than expected
3. Add patterns to this file if they're reusable
4. Include references to line numbers for examples
