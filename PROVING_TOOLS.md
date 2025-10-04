# Automated Proving Tools

This document describes the command-line tools available for automated proof search using LeanCopilot.

## Quick Start

### 1. Simple One-Shot Proof Attempt

Try to prove a single theorem with LeanCopilot:

```bash
./bin/prove-one PCP/ConstraintGraph/Defs.lean sum_degrees_eq_twice_size
```

This will:
1. Create a temporary file with your theorem
2. Replace the proof body with `search_proof`
3. Run `lake build` with LeanCopilot
4. Show you the result (proof if found, or timeout)

**Use this when**: You have a specific theorem with `sorry` and want to see if LeanCopilot can solve it automatically.

### 2. Interactive Proof Assistant

Run the interactive tool to browse and prove theorems:

```bash
./bin/copilot-prove
```

This will:
1. Scan all `.lean` files for theorems with `sorry`
2. Let you interactively select a file and theorem
3. Try to prove it with LeanCopilot
4. Optionally apply the proof back to the file

**Use this when**: You want to explore what can be proven and make progress on multiple theorems.

### 3. Batch Scan Mode

Try to prove ALL theorems with sorry:

```bash
./bin/copilot-prove --scan
```

This will:
1. Find all theorems with `sorry` in your codebase
2. Try to prove each one (with a 15s timeout)
3. Report success rate statistics

**Use this when**: You want to see what percentage of your proof obligations LeanCopilot can handle.

## Examples

### Example 1: Prove a specific theorem

```bash
$ ./bin/prove-one PCP/Basic.lean nat_add_comm
🎯 Attempting to prove: nat_add_comm in PCP/Basic.lean

📝 Creating temporary file with search_proof...
✓ Temporary file created: PCP/Basic_copilot_test.lean

🤖 Running LeanCopilot proof search (this may take 30-60 seconds)...

info: Try this: omega

🎉 SUCCESS! LeanCopilot found a proof!

To apply it, replace the proof body in PCP/Basic.lean

Done!
```

### Example 2: Interactive mode

```bash
$ ./bin/copilot-prove

🎯 LeanCopilot Interactive Proof Assistant
==================================================

📁 Found 22 Lean files

Scanning for theorems with 'sorry'...

Files with unproven theorems:
  1. PCP/ConstraintGraph/Defs.lean (1 theorem)
  2. PCP/Expander/Defs.lean (3 theorems)

Select file (1-2, or q to quit): 1

Theorems in PCP/ConstraintGraph/Defs.lean:
  1. sum_degrees_eq_twice_size (line 242)

Select theorem (1-1, or b for back): 1

🤖 Starting LeanCopilot proof search...
   File: PCP/ConstraintGraph/Defs.lean
   Theorem: sum_degrees_eq_twice_size

1️⃣  Getting tactic suggestions...
   ✗ No suggestions

2️⃣  Running full proof search (beam=4, maxSteps=30)...

😔 No proof found within timeout
   Try:
   - Simplifying the theorem statement
   - Adding helper lemmas
   - Using LeanCopilot in VSCode for interactive exploration
```

## How It Works

### Behind the Scenes

These tools work by:

1. **Reading your Lean file**: Finding the theorem you want to prove
2. **Injecting LeanCopilot**: Adding `import LeanCopilot` if needed
3. **Replacing the proof**: Changing `sorry` to `search_proof (beam := 4) (maxSteps := 40)`
4. **Compiling**: Running `lake build` with the modified file
5. **Extracting results**: Looking for "Try this:" in the output

### What LeanCopilot Does

`search_proof` uses:
- **AI-powered tactic generation**: Neural models trained on mathlib proofs
- **Premise selection**: Automatically finds relevant lemmas from mathlib
- **Beam search**: Explores multiple proof paths simultaneously
- **Aesop integration**: Combines AI suggestions with automated reasoning

Parameters:
- `beam`: How many parallel search paths (higher = more thorough, slower)
- `maxSteps`: Maximum proof steps to try (higher = longer proofs possible)

## Configuration

### Environment Variables

```bash
# Enable LeanCopilot library
export DYLD_LIBRARY_PATH=.lake/packages/LeanCopilot/.lake/build/lib:$DYLD_LIBRARY_PATH

# Set cache directory (optional)
export LEAN_COPILOT_CACHE_DIR=~/.cache/lean_copilot/models
```

### Adjusting Search Parameters

Edit the scripts to change:
- **Beam width**: Increase from 4 to 8 for harder theorems (slower)
- **Max steps**: Increase from 40 to 100 for longer proofs
- **Timeout**: Increase from 60s to 120s for complex goals

Example in `bin/prove-one`:
```bash
# Change this line:
search_proof (beam := 4) (maxSteps := 40)

# To this for harder theorems:
search_proof (beam := 8) (maxSteps := 100)
```

## Success Rate Expectations

Based on LeanCopilot paper benchmarks:

- **Simple lemmas** (1-2 tactics): ~80% success rate
- **Medium complexity** (3-5 tactics): ~40% success rate
- **Complex proofs** (6+ tactics): ~10-20% success rate

**Current theorems in PCP**:
- Most have `sorry` because they're placeholders or require domain knowledge
- Expect ~20-30% success rate on the simpler lemmas
- The tool is most useful for:
  - Finding the first few tactics
  - Suggesting relevant mathlib lemmas
  - Completing routine calculations

## Troubleshooting

### "Library not loaded: libctranslate2.dylib"

```bash
export DYLD_LIBRARY_PATH=.lake/packages/LeanCopilot/.lake/build/lib:$DYLD_LIBRARY_PATH
```

### "timeout: command not found"

Install coreutils:
```bash
brew install coreutils
```

Or remove the `timeout` prefix from the script.

### "Models not found"

Ensure LeanCopilot models are downloaded:
```bash
ls ~/.cache/lean_copilot/models/huggingface.co/kaiyuy/
# Should show 4 model directories
```

If missing, run:
```bash
lake build PCP.Test.Copilot
```

### Script finds wrong theorem

The regex matching is simple. For theorems with similar names:
- Use the exact name as it appears in the file
- Check that the theorem declaration is on a single line

## Next Steps

### 1. Use in VSCode

For interactive development:
```lean
import LeanCopilot

theorem my_theorem : ... := by
  suggest_tactics  -- Get AI suggestions
  search_proof     -- Or let it search fully
```

### 2. Build a Proof Bank

Create a database of proven lemmas:
```bash
# After proving with copilot-prove
./bin/copilot-prove --scan > results.txt
# Extract successful proofs and add to lemma library
```

### 3. Integration with Orchestrator

The full orchestrator (in `orchestrator/`) combines:
- Micro tactics (fast, no AI)
- LeanCopilot (medium, local AI)
- ReProver (slow, heavy AI)

See [ORCHESTRATOR_COPILOT_INTEGRATION.md](ORCHESTRATOR_COPILOT_INTEGRATION.md) for details.

## See Also

- [LEANCOPILOT_SETUP.md](LEANCOPILOT_SETUP.md) - Installation guide
- [ORCHESTRATOR_COPILOT_INTEGRATION.md](ORCHESTRATOR_COPILOT_INTEGRATION.md) - Full automation
- [LeanCopilot Paper](https://arxiv.org/abs/2404.12534) - Technical details
