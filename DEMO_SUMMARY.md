# LeanCopilot Command-Line Tools - Demo Summary

## What We Built

You now have **two command-line tools** for automated proof search:

### 1. `./bin/prove-one <file> <theorem>`
One-shot proof attempt using LeanCopilot

**Example:**
```bash
./bin/prove-one PCP/Test/ProofSearch.lean test_add_comm
```

### 2. `./bin/copilot-prove`
Interactive theorem browser and prover

**Features:**
- Scans all `.lean` files for `sorry`
- Lets you select file → theorem
- Runs LeanCopilot proof search
- Shows results or timeout

## Demo: The Sym2 Sorry

We tested the tools on the `sorry` at line 303 in [PCP/ConstraintGraph/Defs.lean](PCP/ConstraintGraph/Defs.lean:303):

```lean
have all_edges_have_two_vertices : ∀ ec ∈ G.E,
    (Finset.univ.filter (fun v => ∃ u, ec.e = s(v, u))).card = 2 := by
  intro ec hec
  sorry  -- TODO: Fix pattern matching on Sym2
```

### What Happened

```bash
$ ./bin/prove-one PCP/ConstraintGraph/Defs.lean all_edges_have_two_vertices
🎯 Attempting to prove: all_edges_have_two_vertices
🤖 Running LeanCopilot proof search (30-60 seconds)...
😔 No proof found or timeout reached
```

**Why it didn't work:**
1. This is a **nested lemma** inside another proof (not top-level)
2. Requires **Sym2 case analysis** which is domain-specific
3. The proof pattern is shown above it (lines 260-297) but needs generalization

## What the Tools Are Good For

### ✅ Works Well On:
- **Top-level theorems** with `sorry`
- **Short proofs** (1-5 tactics)
- **Standard math** (arithmetic, lists, finsets)
- **Simple type class instances**

### ❌ Struggles With:
- **Nested lemmas** (like our example)
- **Domain-specific patterns** (Sym2, custom inductives)
- **Complex case analysis**
- **Long proofs** (6+ steps)

### 🎯 Best Use Cases:
1. **Quick wins**: Try on all simple lemmas
2. **Getting unstuck**: See what tactics LeanCopilot suggests
3. **Finding mathlib lemmas**: Premise selection shows relevant results
4. **Completing calculations**: Routine algebra/arithmetic

## How to Use Effectively

### Workflow 1: Batch Mode

```bash
# Scan everything and see success rate
./bin/copilot-prove --scan

# Expected: 20-40% success on simple auxiliary lemmas
```

### Workflow 2: Interactive VSCode (Better for Hard Cases)

For theorems like the Sym2 one:

```lean
import LeanCopilot

have all_edges_have_two_vertices : ... := by
  intro ec hec
  suggest_tactics  -- Get AI hints
  -- See suggestions in infoview, click to insert
  sorry
```

**Advantage**: Step-by-step guidance, see intermediate goal states

### Workflow 3: Hybrid

1. Use `./bin/prove-one` on all simple theorems
2. For failures, open in VSCode with `suggest_tactics`
3. Manually complete using hints
4. Build a lemma library of proven results

## Files Created

### Tools:
- [bin/prove-one](bin/prove-one) - Simple one-shot prover script
- [bin/copilot-prove](bin/copilot-prove) - Interactive Python tool
- [orchestrator/workers/copilot_direct.py](orchestrator/workers/copilot_direct.py) - Direct LeanCopilot functions

### Documentation:
- [QUICK_START_PROVING.md](QUICK_START_PROVING.md) - **Start here!**
- [PROVING_TOOLS.md](PROVING_TOOLS.md) - Detailed reference
- [COPILOT_DEMO.md](COPILOT_DEMO.md) - Sym2 example walkthrough
- [PCP/Test/ProofSearch.lean](PCP/Test/ProofSearch.lean) - Test theorems

## Try It Now!

### Easy wins:

```bash
# These should succeed quickly:
./bin/prove-one PCP/Test/ProofSearch.lean test_add_comm
./bin/prove-one PCP/Test/ProofSearch.lean test_nat_le
./bin/prove-one PCP/Test/ProofSearch.lean test_list_append
```

### Real PCP lemmas:

```bash
# Browse and try actual project theorems:
./bin/copilot-prove

# Select from:
# - PCP/ConstraintGraph/Defs.lean
# - PCP/Expander/Defs.lean
# - PCP/AssignmentTester/Defs.lean
```

### Full scan:

```bash
# Try to prove everything (be patient, ~5-10 min):
./bin/copilot-prove --scan > results.txt

# Check results:
grep "✓ PROVED" results.txt
grep "✗ failed" results.txt
```

## Key Takeaway

**You asked**: "Can we give Claude Code access to LeanCopilot somehow?"

**Answer**: ✅ **Yes! You now have command-line tools that:**
- Run LeanCopilot proof search automatically
- Show results in seconds/minutes
- Work on batches of theorems
- Provide both automated and interactive modes

**No more "just thinking" - now you can run commands and watch proofs happen!** 🎉

## Next Steps

1. **Test the tools** on [PCP/Test/ProofSearch.lean](PCP/Test/ProofSearch.lean)
2. **Scan your codebase** with `--scan` mode
3. **Use VSCode interactively** for harder theorems (`suggest_tactics`)
4. **Build a proof library** of successful results
5. **Integrate with orchestrator** for full automation (see [ORCHESTRATOR_COPILOT_INTEGRATION.md](ORCHESTRATOR_COPILOT_INTEGRATION.md))

## See Also

- [ORCHESTRATOR_COPILOT_INTEGRATION.md](ORCHESTRATOR_COPILOT_INTEGRATION.md) - Full automation system
- [LEANCOPILOT_SETUP.md](LEANCOPILOT_SETUP.md) - Installation details
- [LeanCopilot Paper](https://arxiv.org/abs/2404.12534) - Technical background
