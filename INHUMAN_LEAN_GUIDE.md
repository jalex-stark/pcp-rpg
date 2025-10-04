# Inhuman Lean Infrastructure Guide

## Overview

This document describes the **"AI slop" multi-agent architecture** for automated Lean 4 proof generation in the PCP-RPG project. This system is inspired by the approach outlined in `new-instructions` and optimized for **high automation win rates** rather than human readability.

**Key Philosophy:**
- **Optimize for automation**, not elegance
- **Short, deterministic proofs** (≤5 tactics)
- **Heavy redundancy encouraged**
- **Separate slop (machine) from API (human) files**
- **Multi-agent orchestration** with specialized roles

## Architecture

### Multi-Agent Pipeline

```
Spec (from RPG graph node)
  ↓
Decomposer Agent → Slop_N.lean (micro-lemmas with ≤5 tactic proofs)
  ↓
Prover Agent → Complete proofs using short tactics
  ↓
Failure Analyst → Diagnose errors, propose fixes (if needed)
  ↓
Specialized Prover → Copilot/LeanDojo proves each lemma
  ↓
API Curator → API.lean (curated exports + human docs)
  ↓
Results Tracker → results.json (win rates, metrics)
```

### Agents

1. **Decomposer** (`orchestrator/agents/decomposer.py`)
   - Input: High-level spec from unit.yaml
   - Output: Slop_N.lean with micro-lemmas
   - Strategy: Break into "one-shot" solvable pieces

2. **Prover** (`orchestrator/agents/prover.py`)
   - Input: Lemma statements (possibly with `sorry`)
   - Output: Completed proofs (≤5 tactics each)
   - Strategy: Use deterministic tactics only

3. **Failure Analyst** (`orchestrator/agents/failure_analyst.py`)
   - Input: Error log from Lean
   - Output: Proposed fixes (imports, attributes, aux lemmas)
   - Strategy: Minimal changes to make proofs trivial

4. **API Curator** (`orchestrator/agents/api_curator.py`)
   - Input: Proven lemmas from slop files
   - Output: API.lean with curated exports
   - Strategy: De-duplicate, document, organize

5. **Router** (`orchestrator/router.py`)
   - Orchestrates the pipeline
   - Reads RPG graph for prioritization
   - Applies heuristics for resource allocation

### Tools

- **spec_prover.py**: Wrapper around `bin/copilot-prove`
- **index.py**: Extract lemma names/statements from Lean files
- **lean_runner.py**: Run Lake build, parse errors

## Repository Structure

```
PCP/
  ConstraintGraph/
    Unit01_BasicBounds/         # A single "unit" of work
      unit.yaml                 # Configuration
      Slop_Bounds.lean          # Machine-generated lemmas
      API.lean                  # Human-facing exports
      results.json              # Metrics (win rates, etc.)
    Unit02_Degree/
      unit.yaml
      Slop_Degree.lean
      Slop_Size.lean
      API.lean
      results.json

playbooks/
  style.md                      # Strict Lean style guide
  heuristics.yaml               # Routing rules by work package
  prompts/
    system/                     # System prompts for each agent
      decomposer.txt
      prover.txt
      failure_analyst.txt
      api_curator.txt
    decomposer/
      user.txt                  # User prompt template
    prover/
      user.txt
    failure_analyst/
      user.txt
    api_curator/
      user.txt

orchestrator/
  router.py                     # Main orchestration engine
  agents/
    decomposer.py
    prover.py
    failure_analyst.py
    api_curator.py
  tools/
    spec_prover.py
    index.py
    lean_runner.py
```

## Configuration Files

### unit.yaml

Each unit directory contains a `unit.yaml` configuration:

```yaml
# Metadata
id: "csp.basic_bounds"
name: "Basic Bounds on Satisfaction"
work_package: "WP-A"
difficulty: 1
status: "pending"

# Lean configuration
namespace: "ConstraintGraph.Unit01"
imports:
  - "Mathlib.Data.Fintype.Basic"
  - "Mathlib.Data.Rat.Defs"

# Target specification
spec: |
  Prove basic bounds for satFrac and unsat:
  1. satFrac_nonneg: 0 ≤ satFrac G σ
  2. satFrac_le_one: satFrac G σ ≤ 1
  ...

# Constraints
max_lemmas: 15
tactic_budget: 4

# Tags for routing
tags:
  - "constraint_graphs"
  - "arithmetic"

# Outputs
slop_files:
  - "Slop_Bounds.lean"
api_file: "API.lean"
api_comment: |
  Basic bounds on satisfaction fractions...
```

### playbooks/heuristics.yaml

Routing heuristics by work package and difficulty:

```yaml
work_packages:
  WP-A:
    description: "Core definitions"
    tactic_budget: 4
    strategies:
      - name: "definitional"
        tactics: ["unfold", "simp", "rfl"]
        weight: 0.4
    when_fail:
      - "add_unfold_lemma"
      - "add_simp_tag"

difficulty_scaling:
  1:  # Easy
    tactic_multiplier: 0.8
    aux_lemma_budget: 1
  2:  # Medium
    tactic_multiplier: 1.0
    aux_lemma_budget: 2
```

## Usage

### Run a Single Unit

```bash
# Set API key
export ANTHROPIC_API_KEY=your_key_here

# Run one unit
python -m orchestrator.router PCP/ConstraintGraph/Unit01_BasicBounds

# Output:
#   1. Generates Slop_Bounds.lean
#   2. Attempts proofs with Claude
#   3. Runs Copilot on each lemma
#   4. Generates API.lean
#   5. Saves results.json
```

### Run All Units

```bash
# Discover and run all units (in priority order)
python -m orchestrator.router --all
```

Units are prioritized by:
- **Impact**: Number of dependents in RPG graph
- **Blockers**: Unsatisfied dependencies
- **Win rate**: Historical success for this work package
- **Freshness**: Recently modified
- **Difficulty**: Prefer easier units first

### Test Individual Agents

```bash
# Test decomposer
python -m orchestrator.agents.decomposer PCP/ConstraintGraph/Unit01_BasicBounds/unit.yaml

# Test prover
python -m orchestrator.agents.prover Slop_Bounds.lean

# Test API curator
python -m orchestrator.agents.api_curator PCP/ConstraintGraph/Unit01_BasicBounds/unit.yaml
```

### Test Tools

```bash
# Index lemmas
python -m orchestrator.tools.index Slop_Bounds.lean

# Run Lake build
python -m orchestrator.tools.lean_runner PCP/ConstraintGraph/Unit01_BasicBounds

# Prove with Copilot
python -m orchestrator.tools.spec_prover PCP/ConstraintGraph/Unit01_BasicBounds
```

## Style Guide (playbooks/style.md)

**Core Rules:**
1. Use `lemma`, never `theorem`
2. ≤5 tactic lines per proof
3. Deterministic tactics only (no `simp?`, `aesop?`, `by_cases`)
4. Top-level lemmas only (no `where` clauses)
5. Explicit type class binders
6. Redundancy is encouraged

**Allowed tactics:**
- `simp [explicit]`, `simpa`, `rw`
- `apply`, `refine`, `exact`
- `constructor`, `intro`, `cases`
- `unfold`, `norm_cast`, `norm_num`
- `ring`, `linarith`, `omega`, `decide`

**Banned tactics:**
- `simp?`, `aesop?`, `linarith?` (exploratory)
- `by_cases` (adds branching)
- Long `;` chains

See [playbooks/style.md](playbooks/style.md) for details.

## Results Tracking

Each unit generates `results.json`:

```json
{
  "unit_id": "csp.basic_bounds",
  "unit_name": "Basic Bounds on Satisfaction",
  "work_package": "WP-A",
  "difficulty": 1,
  "lemmas_attempted": 10,
  "lemmas_proven": 8,
  "win_rate": 0.8,
  "tactic_budget": 4,
  "results": {
    "satFrac_nonneg": true,
    "satFrac_le_one": true,
    ...
  }
}
```

This feeds back into the router for future prioritization.

## Integration with Existing Tools

### Lean Copilot

The specialized prover (`spec_prover.py`) calls `bin/copilot-prove`:

```bash
bin/copilot-prove --file Slop_Bounds.lean --lemma satFrac_nonneg --timeout 30
```

Expected:
- Returns 0 on success, non-zero on failure
- Proves individual top-level lemmas

### LeanDojo

TODO: Add LeanDojo integration in `prove_with_leandojo()`.

### RPG Graph

The router reads `website/data/pcp-graph.json` to:
- Identify dependencies between nodes
- Score units by impact (number of dependents)
- Map work packages to heuristics

## Workflow

### Creating a New Unit

1. **Identify a node** in the RPG graph (e.g., `constraint_graph.regular_defs`)

2. **Create unit directory:**
   ```bash
   mkdir -p PCP/ConstraintGraph/Unit03_Regular
   ```

3. **Write unit.yaml:**
   - Specify namespace, imports, spec
   - Set difficulty, work_package, tags
   - Define max_lemmas, tactic_budget

4. **Run the router:**
   ```bash
   python -m orchestrator.router PCP/ConstraintGraph/Unit03_Regular
   ```

5. **Inspect results:**
   - Check `results.json` for win rate
   - Review `Slop_*.lean` files
   - Inspect `API.lean` exports

6. **Iterate if needed:**
   - If win rate is low (<50%), adjust spec or tactic_budget
   - Add hints in unit.yaml under `agent_hints`
   - Check `playbooks/heuristics.yaml` for escalation policies

### Debugging Failed Lemmas

1. **Check results.json** to see which lemmas failed
2. **Run Copilot manually:**
   ```bash
   bin/copilot-prove --file Slop_Bounds.lean --lemma failed_lemma --timeout 30
   ```
3. **Inspect Lean errors:**
   ```bash
   lake env lean Slop_Bounds.lean
   ```
4. **Invoke failure analyst manually:**
   ```bash
   python -m orchestrator.agents.failure_analyst Slop_Bounds.lean error.log
   ```
5. **Apply suggested fixes** (imports, attributes, aux lemmas)

## Extending the System

### Add a New Agent

1. Create `orchestrator/agents/new_agent.py`
2. Define function with Claude API call
3. Add prompt templates in `playbooks/prompts/`
4. Wire into router.py pipeline

### Add a New Prover Backend

1. Implement in `orchestrator/tools/spec_prover.py`
2. Add to `prove_lemmas()` switch statement
3. Configure in `playbooks/heuristics.yaml` under `provers:`

### Customize Heuristics

Edit `playbooks/heuristics.yaml`:
- Adjust tactic budgets per work package
- Add new domain tags
- Define escalation policies
- Tune director scoring weights

## Monitoring and Dashboards

### Aggregate Metrics

```bash
# Collect all results.json files
find PCP -name "results.json" -exec cat {} \; > all_results.txt

# Compute aggregate win rates by work package
python scripts/aggregate_metrics.py
```

### Web Dashboard

TODO: Integrate with existing `website/` visualization:
- Show per-unit win rates
- Display progress toward RPG graph completion
- Highlight blockers and high-priority units

## Best Practices

1. **Start with easy units** (difficulty 1-2, WP-A)
2. **Monitor win rates** - aim for >70% proven
3. **Embrace redundancy** - don't fight duplicate lemmas
4. **Iterate on prompts** - adjust based on common failures
5. **Use failure analyst** - don't manually debug
6. **Curate APIs incrementally** - don't wait for perfection
7. **Track metrics religiously** - data drives improvement

## Troubleshooting

### Low win rates (<50%)

- **Increase tactic_budget** in unit.yaml
- **Simplify spec** - break into smaller units
- **Check imports** - missing Mathlib modules?
- **Add aux lemmas** via agent_hints
- **Review style** - are proofs deterministic?

### Decomposer generates bad lemmas

- **Refine spec** - be more explicit
- **Add examples** in agent_hints
- **Reduce max_lemmas** - prefer quality over quantity
- **Check prompt** - adjust system prompt

### Prover exceeds tactic budget

- **Decompose further** - lemma too complex
- **Add aux lemmas** preemptively
- **Use escalation policies** in heuristics.yaml

### Failure analyst not helping

- **Provide better error logs** - full Lean output
- **Check prompt** - is it asking the right questions?
- **Manual intervention** - some failures need human insight

## FAQ

**Q: Why "slop" files?**
A: Machine-optimized code is intentionally redundant and inelegant. The term "slop" acknowledges this is not for human consumption.

**Q: Do I edit slop files manually?**
A: No! Slop files are generated. Manual edits go in API.lean or unit.yaml hints.

**Q: Can I use longer proofs?**
A: Yes, but it hurts automation. Increase tactic_budget only if necessary.

**Q: What if my lemma needs `by_cases`?**
A: Try to decompose into cases as separate lemmas. If truly needed, add to agent_hints.

**Q: How do I know if my unit is done?**
A: Check results.json - aim for >70% win rate. Inspect API.lean to ensure key lemmas are exported.

**Q: Can I run units in parallel?**
A: Not yet. TODO: Add `asyncio` parallel execution in router.py.

## Next Steps

1. **Run Unit01 and Unit02** to validate the pipeline
2. **Bootstrap more units** from RPG graph nodes
3. **Tune heuristics** based on win rates
4. **Integrate dashboard** for visualization
5. **Add LeanDojo** as alternative prover
6. **Scale to full PCP formalization**

## References

- **new-instructions**: Original ChatGPT conversation about this architecture
- **playbooks/style.md**: Detailed Lean style guide
- **playbooks/heuristics.yaml**: Routing configuration
- **docs/engine.md**: Original development system design
- **website/data/pcp-graph.json**: RPG dependency graph
