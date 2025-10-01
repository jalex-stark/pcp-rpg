# Documentation Directory

## Files

### Proof Strategy Knowledge Base

1. **`proof-strategy-graph.json`** - Structured knowledge about tactics, patterns, and errors
   - Tactic capabilities and limitations
   - Common proof patterns with step-by-step guides
   - Error messages and solutions
   - Goal type → Recommended tactics mappings
   - Lemma dependencies with proof strategy annotations

2. **`proof-strategy-schema.json`** - JSON Schema for the knowledge graph
   - Defines structure and validation rules
   - Ensures consistency when adding new entries

3. **`query_strategies.py`** - Command-line tool to query the knowledge graph
   ```bash
   # Query a tactic
   python3 query_strategies.py --tactic linarith

   # Get help with an error
   python3 query_strategies.py --error "omega could not"

   # Find tactics for a goal type
   python3 query_strategies.py --goal "rational"

   # Study a proof pattern
   python3 query_strategies.py --pattern bounds_proof

   # Generate visualization
   python3 query_strategies.py --graphviz > graph.dot
   dot -Tpng graph.dot -o graph.png
   ```

4. **`KNOWLEDGE_GRAPH_INTEGRATION.md`** - Integration strategy
   - How the strategy graph complements the RPG
   - Ideas for visualization and tooling
   - Web scraping strategies for Zulip/docs
   - Future enhancements

### Project Documentation

5. **`PROOF_STRATEGIES.md`** - Human-readable tactics guide (in parent directory)
   - Quick reference table
   - Common pitfalls
   - Detailed patterns with examples

## Quick Start

### Query the Knowledge Graph

```bash
cd docs

# What tactics work with rationals?
python3 query_strategies.py --goal "rational inequality"

# Help! Omega isn't working!
python3 query_strategies.py --error "omega"

# How do I prove bounds?
python3 query_strategies.py --pattern bounds_proof

# List all tactics
python3 query_strategies.py --list-tactics
```

### Visualize the Strategy Graph

```bash
# Generate DOT file
python3 query_strategies.py --graphviz > strategy.dot

# Convert to PNG (requires Graphviz)
dot -Tpng strategy.dot -o strategy.png

# Or convert to SVG
dot -Tsvg strategy.dot -o strategy.svg
```

### Add Your Discoveries

Edit `proof-strategy-graph.json` following the schema:

```json
"my_tactic": {
  "id": "tactic:my_tactic",
  "name": "my_tactic",
  "description": "What it does",
  "works_with_types": ["types"],
  "examples": ["File.lean:123"]
}
```

Validate against schema:
```bash
python3 -c "import json, jsonschema
kg = json.load(open('proof-strategy-graph.json'))
schema = json.load(open('proof-strategy-schema.json'))
jsonschema.validate(kg, schema)
print('✓ Valid')"
```

## Structure

The knowledge graph has several interconnected sections:

```
tactics
  ├─ linarith (works with ℚ, ℝ, ...)
  ├─ omega (only Nat, Int)
  └─ div_le_iff₀ (rational division)

patterns
  ├─ bounds_proof (prove a ≤ x ≤ b)
  ├─ division_inequality (prove a/b ≤ c)
  └─ finset_construction (build Finset)

common_errors
  ├─ omega_with_rationals → use linarith
  ├─ div_le_iff_not_found → use div_le_iff₀
  └─ decidable_eq_missing → axiomatize or noncomputable

goal_to_tactic
  ├─ rational_inequality → [linarith, div_le_iff₀]
  ├─ nat_inequality → [omega, linarith]
  └─ division_bound → [div_le_iff₀]

lemma_dependencies
  ├─ satFrac_nonneg (uses: div_nonneg, simp)
  ├─ satFrac_le_one (uses: div_le_iff₀, simp)
  └─ unsat_bounds (depends: both above, pattern: bounds_proof)
```

## Web Resources

The knowledge graph includes links to:
- Mathlib4 documentation
- Mathematics in Lean tutorial
- Lean 4 tactics reference
- Zulip chat (for searching discussions)

## Integration with RPG

See `KNOWLEDGE_GRAPH_INTEGRATION.md` for:
- How this complements the project RPG graph
- Visualization ideas
- AI assistant integration
- Community contribution workflow

## Examples in Codebase

The knowledge graph references actual proofs:

- **`PCP/ConstraintGraph/Defs.lean`** (lines 110-156)
  - Proved lemmas with detailed comments
  - Demonstrates patterns like `bounds_proof`
  - Shows what tactics work for rational bounds

- **`PCP/ConstraintGraph/Examples.lean`**
  - Concrete CSP instances
  - Shows Finset construction pattern
  - Demonstrates noncomputable definitions

## Future Work

### Near Term
- Add more tactics as we discover them
- Document successful proof strategies
- Link errors to specific Zulip discussions

### Medium Term
- Web scraper for Zulip archive
- Extract patterns from mathlib proofs
- Statistics: which tactics succeed most often?

### Long Term
- IDE integration (show hints based on goal)
- AI-powered tactic suggestion
- Community-contributed knowledge base
- Automated pattern extraction from proof traces

## Contributing

1. Try to prove something in Lean
2. Note what works / what doesn't
3. Add to `proof-strategy-graph.json`
4. Reference specific file:line examples
5. Test with query tool
6. Update this README if adding new sections

The knowledge graph grows with the formalization!
