# Testing Instructions - PCP Orchestrator

This document provides step-by-step instructions for testing the automated theorem proving orchestrator system.

## Prerequisites

- macOS (tested on Apple Silicon)
- Python 3.12+ and 3.13+ installed
- Lean 4.15.0 (automatically installed by elan)
- Git configured with GitHub access token

## Quick Start

### 1. Initial Setup

```bash
cd /Users/jalex/repos/pcp-rpg

# Install Python dependencies for both environments
make orch-init        # Python 3.13 environment (stub workers)
make orch-lean-init   # Python 3.12 environment (LeanDojo support)
```

**What this does:**
- Creates `.venv` with Python 3.13 for general orchestrator use
- Creates `.venv-lean` with Python 3.12 for LeanDojo compatibility
- Installs all required Python packages in both environments

### 2. Verify Lean Build

```bash
lake build PCP.Basic
```

**Expected output:**
- Build succeeds with warnings about `sorry` declarations
- Takes 1-2 minutes on first run (builds mathlib cache)
- Subsequent builds are instant

### 3. Test Stub Workers (No LeanDojo)

```bash
bin/orch bank --timeout 20 --profile 0
```

**Expected output:**
```
============================================================
BENCHMARK BANK RUNNER
============================================================
Loaded 64 goals from bank
Running for up to 20 seconds...
Progress: 64/64 (100%) | Solved: 40 | Time: 3s
✓ All goals processed

============================================================
RESULTS
============================================================
Goals: 64/64 processed
Solved: 40 (62.5%)

By strategy:
  StrategyType.MICRO:  40/ 64 (62.5%)
  StrategyType.COPILOT:   0/ 64 (0.0%)
  StrategyType.SKETCH:   0/ 64 (0.0%)
```

**What this tests:**
- Scheduler with UCB1 strategy selection working
- CPU throttling maintaining ~50% target
- SQLite cache/ledger persisting results
- Stub workers simulating proof search

### 4. Test LeanDojo Integration (Currently In Progress)

**IMPORTANT:** LeanDojo integration is currently building mathlib for the first time. This is a **one-time** cost that takes 10-15 minutes.

Check build status:
```bash
# Check if any lean/lake processes are running
ps aux | grep -E "lean|lake" | grep -v grep

# If you see processes, LeanDojo is still building. Wait for completion.
```

Once build completes, test with:
```bash
bin/orch-lean bank --timeout 30 --profile 1
```

**Expected output (after build completes):**
- Real LeanDojo workers executing tactics on actual Lean goals
- Higher solve rate on compatible goals
- Detailed tactic execution results

## Architecture Overview

```
orchestrator/
├── scheduler/        # UCB1 strategy selection + CPU throttling
├── workers/          # Proof search strategies
│   ├── micro.py     # Fast deterministic tactics (simp, rfl, omega)
│   ├── copilot.py   # Lean Copilot integration
│   ├── dojo.py      # LeanDojo wrapper
│   └── reprover.py  # ReProver RAG (stub)
├── cache/           # SQLite ledger for deduplication
├── brokers/         # Lemma marketplace
└── dashboards/      # FastAPI monitoring
```

## Testing Scenarios

### Scenario A: Basic Orchestrator Functionality

**Test:** Stub workers on benchmark bank

**Command:**
```bash
bin/orch bank --timeout 10 --profile 0
```

**Success criteria:**
- ✓ All 64 goals processed
- ✓ ~40-50 goals solved (60-80% solve rate)
- ✓ Completes in under 10 seconds
- ✓ Results saved to `bench/results/`
- ✓ No crashes or exceptions

**Troubleshooting:**
- If 0% solve rate: Check that stub workers are generating random successes
- If crashes: Check Python 3.13 environment activated
- If slow: Check CPU throttling not too aggressive

### Scenario B: Real Lean Proof Search (Requires LeanDojo Build)

**Test:** Real workers on PCP theorems

**Setup:**
1. Ensure LeanDojo build completed (check no lean/lake processes running)
2. Verify test theorems exist:
```bash
grep -A2 "sorry" PCP/Basic.lean
```

**Expected theorems:**
- `nat_add_zero` : ∀ n : ℕ, n + 0 = n
- `nat_zero_add` : ∀ n : ℕ, 0 + n = n
- `nat_add_comm` : ∀ m n : ℕ, m + n = n + m
- `nat_mul_one` : ∀ n : ℕ, n * 1 = n
- `list_append_nil` : ∀ l : List α, l ++ [] = l
- `list_nil_append` : ∀ l : List α, [] ++ l = l

**Command:**
```bash
# Extract goals from PCP files (to be implemented)
# For now, test with benchmark that uses real DojoWrapper
bin/orch-lean bank --timeout 30
```

**Success criteria:**
- ✓ LeanDojo initializes without errors
- ✓ Workers execute real tactics (simp, rfl, omega)
- ✓ At least some trivial goals solved
- ✓ Tactics and proof scripts logged

**Troubleshooting:**
- Error "lean-dojo not installed": Use `bin/orch-lean` not `bin/orch`
- Error "AST parsing failed": Lean version mismatch, check `lean-toolchain` is v4.15.0
- Error "lake build failed": Run `lake clean && lake build` manually first

### Scenario C: Dashboard Monitoring

**Test:** Real-time web dashboard

**Command:**
```bash
# Terminal 1: Start dashboard
bin/orch dashboard

# Terminal 2: Run proof search
bin/orch bank --timeout 60
```

**Access:** http://localhost:8080

**Success criteria:**
- ✓ Dashboard loads with no errors
- ✓ Real-time progress updates visible
- ✓ Strategy statistics shown
- ✓ UCB scores visible

## Common Issues & Solutions

### Issue 1: "lean-dojo not installed"

**Cause:** Using wrong Python environment

**Solution:**
```bash
# Check which script you're using
which bin/orch       # Uses Python 3.13 (no LeanDojo)
which bin/orch-lean  # Uses Python 3.12 (with LeanDojo)

# For LeanDojo features, always use:
bin/orch-lean [command]
```

### Issue 2: LeanDojo build takes forever

**Cause:** First-time mathlib build (normal!)

**Solution:**
- Be patient - this is a one-time cost (10-15 min)
- LeanDojo caches the traced repo for future runs
- Use stub workers while waiting: `bin/orch bank`

### Issue 3: 0% solve rate with real workers

**Cause:** Goals need proper metadata (file paths, theorem names)

**Solution:**
```bash
# Benchmark bank uses abstract goals (no metadata)
# For real Lean proofs, need goal extraction utility
# Coming soon: bin/orch-lean extract PCP/Basic.lean
```

### Issue 4: Python version conflicts

**Cause:** Multiple Python installations

**Solution:**
```bash
# Check Python versions
python3.13 --version  # Should be 3.13.5+
python3.12 --version  # Should be 3.12.0+

# Recreate environments if needed
rm -rf .venv .venv-lean
make orch-init
make orch-lean-init
```

## Next Steps

After successful testing:

1. **Implement goal extraction:**
   - Scan Lean files for `sorry` declarations
   - Extract theorem signatures and metadata
   - Generate goal queue for orchestrator

2. **Wire Lean Copilot:**
   - Add Copilot to lakefile dependencies
   - Update copilot worker to use real tactics
   - Test `select_premises` + `search_proof`

3. **Add GitHub Actions CI:**
   - Automated benchmark runs
   - Performance regression detection
   - Heavy compute job dispatch

4. **Deploy dashboard:**
   - Persistent results database
   - Historical performance tracking
   - Strategy optimization visualizations

## File Locations

- **Scripts:** `bin/orch`, `bin/orch-lean`, `bin/orch-test-dojo`
- **Config:** `orchestrator/config.py` (if created)
- **Results:** `bench/results/bank-TIMESTAMP.json`
- **Cache:** `orchestrator/cache/ledger.db`
- **Logs:** Console output (add file logging if needed)

## Getting Help

If tests fail:

1. Check this document for troubleshooting
2. Look at recent git commits for clues
3. Read orchestrator implementation docs in `docs/engine.md`
4. Check LeanDojo documentation: https://leandojo.readthedocs.io/

## Test Summary Checklist

Before handoff, verify:

- [ ] `make orch-init` succeeds
- [ ] `make orch-lean-init` succeeds
- [ ] `lake build PCP.Basic` succeeds
- [ ] `bin/orch bank` achieves >50% solve rate
- [ ] `bin/orch-test` shows LeanDojo initialized
- [ ] No untracked files with secrets/credentials
- [ ] Git working tree clean except expected changes

---

**Last Updated:** 2025-10-01
**Lean Version:** 4.15.0
**Mathlib Version:** v4.15.0 (commit 9837ca9d)
**LeanDojo Version:** 4.20.0
