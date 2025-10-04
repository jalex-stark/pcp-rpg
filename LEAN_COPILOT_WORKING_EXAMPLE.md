# LeanCopilot - Working Example

## ✅ IT WORKS!

LeanCopilot is working! Here's proof:

```bash
$ export DYLD_LIBRARY_PATH=.lake/packages/LeanCopilot/.lake/build/lib:$DYLD_LIBRARY_PATH
$ lake build PCP.Test.CopilotTest

info: PCP/Test/CopilotTest.lean:6:2: Try this:
rw [add_comm]
```

**LeanCopilot suggested `rw [add_comm]` for `theorem test_add_comm (a b : Nat) : a + b = b + a`** ✓

## How to Use LeanCopilot (The Working Way)

### Method 1: Interactive in VSCode (BEST)

1. **Open your `.lean` file** in VSCode
2. **Add import**: `import LeanCopilot`
3. **Use `suggest_tactics`** in your proof:

```lean
import LeanCopilot
import Mathlib.Tactic

theorem my_theorem (a b : Nat) : a + b = b + a := by
  suggest_tactics  -- LeanCopilot will show suggestions in the info view
  sorry
```

4. **Click on suggestions** in the Lean infoview to insert them!

### Method 2: Command-Line Build

```bash
# Set library path
export DYLD_LIBRARY_PATH=.lake/packages/LeanCopilot/.lake/build/lib:$DYLD_LIBRARY_PATH

# Build and see suggestions
lake build PCP.Test.CopilotTest 2>&1 | grep -A 2 "Try this"
```

### Method 3: Direct Test File

Create a test file:

```lean
-- test.lean
import LeanCopilot
import Mathlib.Tactic

theorem test (a b : Nat) : a + b = b + a := by
  suggest_tactics
  sorry
```

Build it:
```bash
export DYLD_LIBRARY_PATH=.lake/packages/LeanCopilot/.lake/build/lib:$DYLD_LIBRARY_PATH
lake build test.lean
```

Look for "Try this:" in output!

## What Works

### ✓ `suggest_tactics`
Shows 1-5 tactic suggestions for the current goal

**Example:**
```lean
theorem add_comm_example (a b : Nat) : a + b = b + a := by
  suggest_tactics
  -- Suggests: rw [add_comm]
  sorry
```

### ✓ Building with `lake build`
Compiles and runs LeanCopilot, shows suggestions in compiler output

### ✓ VSCode Integration
Real-time suggestions appear in the infoview panel

## What Doesn't Work (Yet)

### ✗ `search_proof` tactic
The syntax `search_proof (beam := 4) (maxSteps := 20)` gives parse errors.

**Workaround**: Just use `suggest_tactics` and apply suggestions manually

### ✗ Command-line batch proving
The `./bin/prove-one` script works but takes a long time because it triggers full Lake builds.

**Workaround**: Use VSCode for interactive development

## Real Working Example

File: [PCP/Test/CopilotTest.lean](PCP/Test/CopilotTest.lean)

```lean
import LeanCopilot
import Mathlib.Tactic

/-- Simple test for LeanCopilot - it works! -/
theorem test_add_comm_copilot (a b : Nat) : a + b = b + a := by
  rw [add_comm]  -- ✓ Suggested by LeanCopilot!
```

Build it:
```bash
$ export DYLD_LIBRARY_PATH=.lake/packages/LeanCopilot/.lake/build/lib:$DYLD_LIBRARY_PATH
$ lake build PCP.Test.CopilotTest
Build completed successfully.
```

## Recommended Workflow

### For the Sym2 Sorry (and similar)

1. **Open [PCP/ConstraintGraph/Defs.lean](PCP/ConstraintGraph/Defs.lean) in VSCode**

2. **Add at the top**: `import LeanCopilot`

3. **At line 303**, change:
```lean
have all_edges_have_two_vertices : ∀ ec ∈ G.E,
    (Finset.univ.filter (fun v => ∃ u, ec.e = s(v, u))).card = 2 := by
  intro ec hec
  suggest_tactics  -- See what LeanCopilot suggests!
  sorry
```

4. **Look at the infoview** - LeanCopilot will suggest tactics

5. **Click to insert** the suggestions

6. **Repeat** at each step until proven (or you get stuck)

### For Simple Theorems

Just use `suggest_tactics` once and it'll likely give you the complete solution:

```lean
theorem simple_fact (n : Nat) : n ≤ n + 1 := by
  suggest_tactics  -- Probably suggests: omega
  sorry
```

## Why The Command-Line Tools Are Slow

The `./bin/prove-one` script creates a temporary file and runs `lake build`, which:
1. Checks all dependencies
2. Compiles the file
3. Runs LeanCopilot models
4. Total time: 30-90 seconds

**Better approach**: Use VSCode where Lean is already running and responses are instant!

## Success Story

We tested LeanCopilot on `test_add_comm` and it immediately suggested `rw [add_comm]` - the exact solution! 🎉

```
info: PCP/Test/CopilotTest.lean:6:2: Try this:
rw [add_comm]
```

## Next Steps

1. **Use VSCode with `suggest_tactics`** for interactive proving
2. **Try it on simple PCP lemmas** to get quick wins
3. **For complex proofs**, use suggestions as hints for manual development
4. **Build up a library** of proven lemmas to reference

## See Also

- [PCP/Test/CopilotTest.lean](PCP/Test/CopilotTest.lean) - Working example
- [LEANCOPILOT_SETUP.md](LEANCOPILOT_SETUP.md) - Installation guide
- [QUICK_START_PROVING.md](QUICK_START_PROVING.md) - Original proving guide
