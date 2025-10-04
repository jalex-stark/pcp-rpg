# How to Run the Orchestrator

## Quick Start

```bash
# Run on the test bank (64 toy theorems)
./bin/orch bank --timeout 30
```

**What you'll see:**
- Progress updates as goals are processed
- Final stats showing solve rates by strategy
- Results saved to `bench/results/`

## Understanding the Output

```
============================================================
BENCHMARK BANK RUNNER
============================================================
Loaded 64 goals from bank
Running for up to 30 seconds...
Progress: 64/64 (100%) | Solved: 8 | Time: 3s
✓ All goals processed

============================================================
RESULTS
============================================================
Goals: 64/64 processed
Solved: 8 (12.5%)

By strategy:
  StrategyType.MICRO:   8/ 64 (12.5%)
  StrategyType.COPILOT:   0/ 64 (0.0%)
  StrategyType.SKETCH:   0/ 64 (0.0%)

✓ Results saved to bench/results/bank-20251003-091925.json
```

This means:
- ✅ **Orchestrator is working**
- ⚠️ **Using mock workers** (so solve rate is low)
- ⚠️ **Not connected to actual Lean** (yet)

## Current Status

### What's Working ✅

1. **Scheduler**
   - UCB1 strategy selection
   - CPU throttling (~50% target)
   - Concurrent worker execution
   - Progress tracking

2. **Workers** (Mock Mode)
   - `micro`: Random success/failure
   - `copilot`: Always fails (needs real Lean)
   - `sketch`: Always fails (needs real Lean)

3. **Infrastructure**
   - SQLite cache for results
   - JSON output to `bench/results/`
   - Lemma marketplace (ready)
   - Dashboard (ready)

### What Needs Lean ⚠️

To get **real proof search**, you need to connect workers to actual Lean:

1. **LeanDojo Integration**
   - Requires: `lean-dojo` Python package installed
   - Requires: Lean project built with `lake build`
   - Use: `./bin/orch-lean` instead of `./bin/orch`

2. **LeanCopilot Integration**
   - Requires: LeanCopilot models downloaded ✅ (you have this!)
   - Requires: Library paths set ✅ (you have this!)
   - Requires: Real Lean environment running
   - Status: **Ready to use interactively in VSCode**

## Different Ways to Run

### 1. Mock Mode (Fast, No Dependencies)

```bash
# Uses stub workers - good for testing orchestrator logic
./bin/orch bank --timeout 30 --profile 0
```

**Use when:**
- Testing the scheduler
- Developing orchestrator features
- No Lean environment available

**Limitations:**
- Random solve rates (~10-20%)
- No actual proofs generated
- Can't verify against real Lean

### 2. LeanDojo Mode (Real Proofs)

```bash
# Uses real Lean verification via LeanDojo
./bin/orch-lean bank --timeout 60 --profile 1
```

**Requires:**
1. LeanDojo installed (`pip install lean-dojo`)
2. Lean project built (`lake build`)
3. Theorems in Lean files (not just in bank.jsonl)

**Use when:**
- Want real proof verification
- Testing on actual PCP theorems
- Building proof cache

**Currently:** Not fully wired up (workers need theorem file paths)

### 3. Interactive Mode (VSCode + LeanCopilot)

This is **what works best right now**:

```lean
-- In VSCode, open any .lean file
import LeanCopilot

theorem my_theorem (n : Nat) : n + 0 = n := by
  suggest_tactics  -- Get AI suggestions
  -- Click one to insert it
```

**Advantages:**
- ✅ Full LeanCopilot functionality
- ✅ Real-time suggestions
- ✅ Human-guided proving
- ✅ Models already downloaded

## Configuration

### Profile Levels

Control which strategies are available:

```bash
export ORCH_PROFILE=0  # Micro tactics only (rfl, simp, omega, aesop)
export ORCH_PROFILE=1  # + LeanCopilot (AI-powered)
export ORCH_PROFILE=2  # + ReProver (heavy retrieval)
```

### Resource Limits

```bash
export ORCH_CPU_TARGET=0.5   # Target 50% CPU usage
export ORCH_MAX_LIGHT=8      # Max concurrent light workers
export ORCH_MAX_HEAVY=2      # Max concurrent heavy workers
```

### Timeouts

```bash
./bin/orch bank --timeout 60    # Total runtime limit (seconds)
```

## What the Orchestrator Does

1. **Loads goals** from `bench/bank.jsonl`
2. **Prioritizes** them using UCB1 algorithm
3. **Dispatches** to workers in parallel
4. **Throttles** CPU to stay under target
5. **Caches** successful proofs in SQLite
6. **Reports** statistics and saves results

## Viewing Results

### Command Line Output

Real-time during run:
```
Progress: 32/64 (50%) | Solved: 6 | Time: 1s
```

Final summary:
```
Goals: 64/64 processed
Solved: 8 (12.5%)
```

### JSON Files

Detailed results saved to:
```bash
bench/results/bank-YYYYMMDD-HHMMSS.json
```

Contains:
- Per-goal results (success, tactics, time)
- Strategy statistics
- Cache hit rates
- Timing breakdown

### Dashboard (Future)

```bash
./bin/orch dashboard
# Open http://127.0.0.1:8000
```

Real-time monitoring:
- Active workers
- Goal queue
- Success rates
- Cache statistics

## Example Workflows

### 1. Test Orchestrator Logic

```bash
# Quick test with mock workers
./bin/orch bank --timeout 10
# Should complete in ~3 seconds
# Expect ~10-20% solve rate (random)
```

### 2. Profile Performance

```bash
# Run longer to see UCB1 adaptation
./bin/orch bank --timeout 60
# Watch how strategy selection changes
# CPU should stay around 50%
```

### 3. Test Real Integration (When Ready)

```bash
# First: ensure Lean builds
lake build

# Then: test LeanDojo connection
./bin/orch-test-dojo

# Finally: run with real workers
./bin/orch-lean bank --timeout 120 --profile 1
```

## Troubleshooting

### "Warning: psutil not available"

This is **fine** - CPU throttling will be disabled but everything else works.

To fix:
```bash
pip install psutil
```

### "lean-dojo not installed"

Use `./bin/orch` (mock mode) instead of `./bin/orch-lean`.

Or install it:
```bash
source .venv-lean/bin/activate
pip install lean-dojo
```

### "No goals to process"

The bank file is missing or empty:
```bash
ls -l bench/bank.jsonl
cat bench/bank.jsonl | wc -l  # Should show 64
```

### Low solve rates (< 20%)

**This is normal** in mock mode! Mock workers use randomness.

For real proof search, you need:
1. LeanDojo integration
2. Real Lean theorems (with file paths)
3. Proper worker implementation

## Next Steps

### To Get Real Automation Working

1. **Create Lean test file** with simple theorems:
   ```lean
   -- PCP/Test/Auto.lean
   import Mathlib.Tactic

   theorem test1 (n : Nat) : n + 0 = n := by sorry
   theorem test2 (n : Nat) : 0 + n = n := by sorry
   ```

2. **Extract to bank.jsonl** with file paths:
   ```json
   {"id": "test1", "goal": "n + 0 = n", "metadata": {"file_path": "PCP/Test/Auto.lean", "theorem_name": "test1"}}
   ```

3. **Wire up LeanDojo workers** to actually invoke Lean

4. **Test with real verification**:
   ```bash
   ./bin/orch-lean bank --profile 1
   ```

### To Use LeanCopilot Now

**Don't wait for full automation** - use it interactively:

1. Open VSCode
2. Create/open a `.lean` file
3. Add `import LeanCopilot` at top
4. Use `suggest_tactics` in proofs
5. Build your proof library manually
6. Later: feed completed proofs to orchestrator for optimization

## Summary

| Mode | Command | Status | Use Case |
|------|---------|--------|----------|
| **Mock** | `./bin/orch bank` | ✅ Working | Test orchestrator logic |
| **Interactive** | VSCode + LeanCopilot | ✅ Working | Prove theorems with AI help |
| **Automated** | `./bin/orch-lean bank` | ⚠️ Partial | Batch verification (needs wiring) |

**Right now:** Use orchestrator to test scheduling logic, use LeanCopilot in VSCode for actual theorem proving.

**Eventually:** Full automation where orchestrator discovers proofs autonomously.
