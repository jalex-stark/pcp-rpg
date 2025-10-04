# Using LeanCopilot on the Sym2 Sorry

This demonstrates how to use LeanCopilot **interactively in VSCode** to get help with the `sorry` at line 303 in `PCP/ConstraintGraph/Defs.lean`.

## The Problem

```lean
have all_edges_have_two_vertices : ∀ ec ∈ G.E,
    (Finset.univ.filter (fun v => ∃ u, ec.e = s(v, u))).card = 2 := by
  intro ec hec
  sorry  -- TODO: Fix pattern matching on Sym2
```

We need to prove that for any edge `ec`, exactly 2 vertices are incident to it.

## Why Command-Line Failed

The automated `./bin/prove-one` didn't work because:
1. This is a **nested lemma** inside a larger proof (not a top-level theorem)
2. It requires **Sym2 case analysis** which is domain-specific
3. The proof above it (lines 260-297) shows the pattern, but it's for a concrete edge

## Solution: Interactive VSCode Approach

### Step 1: Open the file in VSCode

Open `PCP/ConstraintGraph/Defs.lean` in VSCode with the Lean extension.

### Step 2: Import LeanCopilot

Add at the top of the file (if not already there):
```lean
import LeanCopilot
```

Then run:
```bash
lake build PCP.ConstraintGraph.Defs
```

### Step 3: Use `suggest_tactics` at the sorry

Replace the `sorry` with:
```lean
have all_edges_have_two_vertices : ∀ ec ∈ G.E,
    (Finset.univ.filter (fun v => ∃ u, ec.e = s(v, u))).card = 2 := by
  intro ec hec
  suggest_tactics  -- LeanCopilot will show suggestions here
  sorry
```

### Step 4: Click on suggestions

In VSCode, you'll see a lightbulb or infoview message with suggestions like:
- `obtain ⟨a, b⟩ := ec.e.out`
- `cases ec.e using Sym2.inductionOn`
- `apply Sym2.ind`

Click to insert them!

### Step 5: Iterate

After inserting a tactic, use `suggest_tactics` again at the next goal:
```lean
have all_edges_have_two_vertices : ∀ ec ∈ G.E,
    (Finset.univ.filter (fun v => ∃ u, ec.e = s(v, u))).card = 2 := by
  intro ec hec
  obtain ⟨a, b⟩ := ec.e.out
  suggest_tactics  -- What next?
  sorry
```

## Manual Solution (Based on Pattern Above)

Looking at lines 260-297, the pattern is:
1. Extract the two vertices from the Sym2
2. Show equivalence between the filter condition and `v = a ∨ v = b`
3. Use `Finset.card_pair`

Here's the filled-in proof:

```lean
have all_edges_have_two_vertices : ∀ ec ∈ G.E,
    (Finset.univ.filter (fun v => ∃ u, ec.e = s(v, u))).card = 2 := by
  intro ec hec
  -- Extract the two vertices from the Sym2
  obtain ⟨a, b, hab, rfl⟩ := Sym2.exists_rep ec.e

  -- Now we need to show the filter has exactly 2 elements
  -- This is the same proof as above for the specific edge s(a,b)

  -- First establish equivalence: (∃ u, s(a, b) = s(v, u)) ↔ (v = a ∨ v = b)
  have mem_equiv : ∀ v, (∃ u, s(a, b) = s(v, u)) ↔ (v = a ∨ v = b) := by
    intro v
    constructor
    · intro ⟨u, h⟩
      rw [Sym2.eq_iff] at h
      cases h with
      | inl heq => exact Or.inl heq.1.symm
      | inr heq => exact Or.inr heq.2.symm
    · intro h
      cases h with
      | inl heq => use b; left; exact ⟨heq.symm, rfl⟩
      | inr heq => use a; right; exact ⟨rfl, heq.symm⟩

  -- Now compute the cardinality
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
```

## Why This Works

1. **`Sym2.exists_rep`**: Extracts witnesses `a, b` from `ec.e` with proof that they're distinct
2. **Equivalence**: Shows that "there exists a vertex u such that s(a,b) = s(v,u)" means exactly "v is a or v is b"
3. **Set equality**: Rewrites the filter as `{a, b}`
4. **Cardinality**: Uses `Finset.card_pair` which says `|{a, b}| = 2` when `a ≠ b`

## Alternative: Use search_proof

You can also try:
```lean
have all_edges_have_two_vertices : ∀ ec ∈ G.E,
    (Finset.univ.filter (fun v => ∃ u, ec.e = s(v, u))).card = 2 := by
  intro ec hec
  obtain ⟨a, b, hab, rfl⟩ := Sym2.exists_rep ec.e
  search_proof (beam := 8) (maxSteps := 50)
```

This lets LeanCopilot try to complete the proof after you give it the key first step (extracting `a, b`).

## Key Lesson

**Automated proof search** works best when:
- Theorems are **top-level** (not nested in other proofs)
- The proof is **short** (1-5 tactics)
- No domain-specific case analysis needed

**Interactive mode** (`suggest_tactics`) is better for:
- Nested lemmas like this one
- Proofs requiring specific Sym2 patterns
- Getting hints for the next step when you're stuck

## Try It!

### Option 1: VSCode Interactive
1. Add `import LeanCopilot` to Defs.lean
2. Change `sorry` to `suggest_tactics; sorry`
3. Look at suggestions in infoview
4. Click to insert, repeat

### Option 2: Apply the manual solution
Just copy the proof above into the file at line 302-303!

### Option 3: Hybrid approach
```lean
intro ec hec
obtain ⟨a, b, hab, rfl⟩ := Sym2.exists_rep ec.e
suggest_tactics  -- Now ask LeanCopilot what to do next
```

The first line is the key insight (extract vertices from Sym2). After that, LeanCopilot might be able to complete it!
