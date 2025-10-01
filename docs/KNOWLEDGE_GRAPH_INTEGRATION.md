# Knowledge Graph Integration with RPG

## Overview

We've created a parallel knowledge graph (`proof-strategy-graph.json`) that complements the Repository Planning Graph (RPG) with proof strategy information.

## Two-Graph Architecture

### 1. RPG Graph (`website/data/pcp-graph.json`)
**Purpose**: Project structure and dependencies
- Modules and their relationships
- Work packages and difficulty ratings
- Implementation dependencies
- Progress tracking

### 2. Proof Strategy Graph (`docs/proof-strategy-graph.json`)
**Purpose**: Proof knowledge and tactics
- Tactic capabilities and limitations
- Common proof patterns
- Error messages and solutions
- Goal → Tactic mappings
- Lemma dependencies with proof strategies

## Why Two Graphs?

**Separation of Concerns:**
- RPG: "What needs to be built and in what order?"
- Strategy Graph: "How do I actually prove this?"

**Different Users:**
- RPG: Project managers, collaborators planning work
- Strategy Graph: Proof engineers actively writing Lean code

**Different Update Cycles:**
- RPG: Updated when architecture changes
- Strategy Graph: Updated as we discover tactics that work/don't work

## Integration Points

### 1. Enriched Nodes in RPG

Add `proof_hints` field to RPG nodes:

```json
{
  "id": "ConstraintGraph.Defs.satFrac_le_one",
  "type": "lemma",
  "difficulty": 2,
  "proof_hints": {
    "pattern": "pattern:division_inequality",
    "key_tactics": ["div_le_iff₀", "linarith"],
    "common_errors": ["error:omega_rationals"]
  }
}
```

### 2. Cross-References

Link between graphs using IDs:

**In RPG node:**
```json
{
  "id": "BinaryCSP.unsat_bounds",
  "strategy_ref": "lemma:unsat_bounds"
}
```

**In Strategy Graph:**
```json
{
  "unsat_bounds": {
    "id": "lemma:unsat_bounds",
    "rpg_ref": "BinaryCSP.unsat_bounds",
    "location": "PCP/ConstraintGraph/Defs.lean:127-138"
  }
}
```

### 3. Visualization Integration

**Option A: Separate Views**
- Keep RPG visualization as-is
- Add new "Strategy View" that shows tactics/patterns/errors
- Link between views via shared IDs

**Option B: Overlay Mode**
- RPG shows structure
- Toggle to show proof hints on nodes
- Color-code nodes by proof difficulty/status

**Option C: Combined Graph**
- Merge both graphs
- Use different node shapes: rectangles=modules, circles=tactics, diamonds=patterns
- Edge types: "depends on" vs "uses tactic" vs "follows pattern"

## Query Tool Usage

```bash
# Find tactics for a goal type
python docs/query_strategies.py --goal "rational inequality"

# Get help with an error
python docs/query_strategies.py --error "omega could not prove"

# Learn about a tactic
python docs/query_strategies.py --tactic linarith

# Study a proof pattern
python docs/query_strategies.py --pattern bounds_proof

# List all available tactics
python docs/query_strategies.py --list-tactics

# Generate visualization
python docs/query_strategies.py --graphviz > strategy-graph.dot
dot -Tpng strategy-graph.dot -o strategy-graph.png
```

## Extending the Strategy Graph

### Adding New Tactics

```json
"my_new_tactic": {
  "id": "tactic:my_new_tactic",
  "name": "my_new_tactic",
  "description": "What it does",
  "works_with_types": ["types it works on"],
  "typical_usage": "When to use it",
  "examples": ["File.lean:123"]
}
```

### Adding New Patterns

```json
"my_pattern": {
  "id": "pattern:my_pattern",
  "name": "My Pattern Name",
  "description": "What this pattern does",
  "steps": ["step 1", "step 2", "step 3"],
  "tactics_used": ["tactic1", "tactic2"],
  "examples": ["File.lean:100-120"]
}
```

### Recording New Errors

```json
"my_error": {
  "id": "error:my_error",
  "error_message": "Exact error text from Lean",
  "description": "What causes this error",
  "solution": "How to fix it",
  "references": ["tactic:helpful_tactic"]
}
```

## Web Scraping Strategy

### Zulip Chat Mining

The web searches showed that Zulip chat logs are indexed but hard to search directly. Strategy:

1. **Direct Zulip Search**: Use https://leanprover.zulipchat.com's built-in search
2. **Archive Mining**: Clone https://github.com/leanprover-community/archive
3. **Pattern Extraction**: Search for common phrases:
   - "how do I prove"
   - "tactic X doesn't work"
   - "error message: ..."
   - "you should use Y instead of X"

### Mathlib Documentation

Systematically crawl:
- Tactic documentation pages
- "See Also" sections
- Code examples
- Docstrings mentioning common pitfalls

### Automation Ideas

```python
def extract_tactic_info(zulip_thread):
    """Extract tactic usage patterns from Zulip discussions."""
    info = {
        "error_messages": extract_errors(thread),
        "solutions": extract_solutions(thread),
        "recommended_tactics": extract_recommendations(thread)
    }
    return info

def build_goal_to_tactic_map(mathlib_examples):
    """Learn which tactics work for which goals."""
    mapping = {}
    for example in mathlib_examples:
        goal_pattern = classify_goal(example.goal)
        successful_tactic = example.tactic
        mapping[goal_pattern].append(successful_tactic)
    return mapping
```

## Integration with AI Assistants

### For LLM-Based Proof Search

The strategy graph provides structured knowledge for AI:

```python
def suggest_tactic(goal_state, strategy_graph):
    """Suggest tactics based on goal pattern."""
    goal_type = classify_goal(goal_state)
    suggestions = strategy_graph["goal_to_tactic"].get(goal_type, [])

    # Filter by context
    if contains_rationals(goal_state):
        suggestions = [t for t in suggestions if t != "omega"]

    return suggestions
```

### For Interactive IDE Support

```lean
-- IDE could show hints based on goal type
example (a b : ℚ) : a / b ≤ 1 := by
  -- 💡 Hint: For rational division bounds, use div_le_iff₀
  -- 💡 Pattern: pattern:division_inequality
  sorry
```

## Visualization Examples

### Strategy Graph Only

```
[Tactics]           [Patterns]          [Lemmas]
  linarith ------>  bounds_proof -----> unsat_bounds
  div_le_iff₀ -/                    \-> satFrac_le_one
  obtain -------/
```

### Combined with RPG

```
[Module: ConstraintGraph.Defs]
    |
    |-- [Lemma: satFrac_nonneg]
    |     pattern: bounds_proof
    |     uses: div_nonneg, simp
    |
    |-- [Lemma: unsat_bounds]
          pattern: bounds_proof
          depends: satFrac_nonneg, satFrac_le_one
          uses: obtain, linarith
```

## Future Enhancements

### 1. Proof Replay Analysis
- Analyze successful proofs to extract patterns
- Build statistics: "tactic X works 80% of time for goal Y"

### 2. Error Prediction
- Warn before common mistakes: "You're using omega on ℚ, this will fail"

### 3. Tactic Sequences
- Learn common tactic chains: "obtain → rw → linarith"

### 4. Difficulty Estimation
- Estimate proof difficulty based on required tactics
- "This needs div_le_iff₀ + custom lemma = difficulty 3"

### 5. Community Contributions
- Allow others to add their discovered patterns
- Voting/rating on tactic effectiveness

## Related Work

- **LeanDojo**: Extracts tactic traces from mathlib proofs
- **Lean Copilot**: Uses ML to suggest tactics
- **ReProver**: Learns proof strategies from examples

Our strategy graph is complementary - it's human-curated knowledge that can augment ML-based approaches.

## Contributing

To add your discoveries:

1. Edit `docs/proof-strategy-graph.json`
2. Add your tactic/pattern/error with examples
3. Reference line numbers in Lean files
4. Link to external resources if available
5. Run `python docs/query_strategies.py --tactic your_tactic` to test

The graph grows as we formalize more of the PCP theorem!
