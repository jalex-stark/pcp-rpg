# Handoff Summary - PCP Orchestrator

**Date:** 2025-10-01
**Status:** Core framework complete, LeanDojo integration in progress
**Next Tester:** Ready for immediate testing with stub workers

## What Was Built

### 1. Complete Orchestrator Framework

**Location:** `orchestrator/`

**Components:**
- **Scheduler** (`scheduler/scheduler.py`) - 242 lines
  - UCB1 bandit algorithm for strategy selection
  - EMA-based CPU throttling (maintains ~50% target)
  - Concurrent task management with semaphores
  - Real-time statistics tracking

- **Workers** (`workers/`)
  - `micro.py` - Deterministic tactics (rfl, simp, omega, linarith)
  - `copilot.py` - Lean Copilot integration (select_premises + search_proof)
  - `dojo.py` - LeanDojo wrapper with caching (340 lines)
  - `reprover.py` - ReProver RAG (stub)
  - `sketch.py` - LLM sketch validation (stub)

- **Cache** (`cache/store.py`) - SQLite ledger for deduplication
- **Marketplace** (`brokers/marketplace.py`) - Helper lemma requests
- **Dashboard** (`dashboards/serve.py`) - FastAPI monitoring
- **CLI** (`cli/`) - Typer-based command interface

### 2. Multi-Environment Setup

**Python 3.13** (`.venv`)
- General orchestrator use
- Stub workers
- Dashboard and CLI
- No LeanDojo dependency

**Python 3.12** (`.venv-lean`)
- LeanDojo support
- Real Lean proof search
- Full worker capabilities

**Scripts:**
- `bin/orch` - Uses Python 3.13
- `bin/orch-lean` - Uses Python 3.12 + LeanDojo
- `bin/orch-test-dojo` - Tests LeanDojo setup

### 3. Test Infrastructure

**Benchmark Bank** (`bench/bank.jsonl`)
- 64 toy theorems
- Categories: Nat (28), List (20), Bool (14), Option (4)
- Difficulty ratings 0.1-0.5

**PCP Test Theorems** (`PCP/Basic.lean`)
- 6 theorems with `sorry` for orchestrator to solve
- Simple arithmetic and list operations
- Ready for real proof search

### 4. Lean Version Downgrade

**Change:** Lean 4.24.0-rc1 → Lean 4.15.0

**Reason:** LeanDojo 4.20.0 incompatible with Lean 4.24
- AST parsing failures
- Known issue with bleeding-edge Lean versions

**Files Updated:**
- `lean-toolchain` - Now v4.15.0
- `lakefile.toml` - Pinned mathlib to v4.15.0
- `lake-manifest.json` - Committed for reproducibility
- `PCP/Basic.lean` - Simplified imports

## Current Status

### ✅ Working

1. **Stub Workers**
   - Command: `bin/orch bank --timeout 10`
   - Result: **62.5% solve rate** (40/64 goals)
   - Speed: Under 10 seconds

2. **Core Infrastructure**
   - UCB1 strategy selection
   - CPU throttling
   - SQLite caching
   - Result persistence

3. **Build System**
   - `lake build PCP.Basic` succeeds
   - Mathlib 4.15.0 cached
   - All dependencies installed

### ⏳ In Progress

**LeanDojo Build** (Currently Running)
- Background process building mathlib4 cache
- One-time cost: 10-15 minutes
- Check status: `ps aux | grep -E "lean|lake"`
- Once complete: Real proof search becomes available

### 🔲 Not Yet Implemented

1. **Goal Extraction Utility**
   - Scan Lean files for `sorry`
   - Extract theorem metadata
   - Generate goal queue

2. **Lean Copilot Integration**
   - Add to lakefile dependencies
   - Test select_premises + search_proof
   - Validate with real theorems

3. **GitHub Actions CI**
   - Automated benchmarks
   - Performance tracking
   - Heavy compute dispatch

## How to Test

### Quick Test (30 seconds)

```bash
# Setup
cd /Users/jalex/repos/pcp-rpg
make orch-init

# Test
bin/orch bank --timeout 10
```

**Expected:** `~40/64 goals solved (62%)` in <10 seconds

### Full Test (after LeanDojo build completes)

```bash
# 1. Check if LeanDojo ready
make orch-test

# 2. Test real workers
bin/orch-lean bank --timeout 30

# 3. Monitor with dashboard
bin/orch dashboard &
bin/orch-lean bank --timeout 60
```

**See:** [TESTING_INSTRUCTIONS.md](TESTING_INSTRUCTIONS.md) for details

## Known Issues

### Issue 1: LeanDojo Build Time

**Symptom:** First LeanDojo test takes 10-15 minutes
**Cause:** Building mathlib4 cache (one-time)
**Status:** Normal, expected behavior
**Workaround:** Use stub workers meanwhile

### Issue 2: ExtractData.lean Build Error

**Symptom:** LeanDojo tracing fails with `lake env lean --run ExtractData.lean`
**Cause:** Under investigation (may be LeanDojo version mismatch)
**Status:** Still building, may resolve when complete
**Workaround:** None yet, monitoring build

### Issue 3: Python Version Management

**Symptom:** "lean-dojo not installed" errors
**Cause:** Using wrong wrapper script
**Solution:** Use `bin/orch-lean` for LeanDojo features

## File Structure

```
pcp-rpg/
├── bin/
│   ├── orch                    # Orchestrator (Py 3.13)
│   ├── orch-lean               # With LeanDojo (Py 3.12)
│   └── orch-test-dojo          # Test LeanDojo
├── orchestrator/
│   ├── __init__.py
│   ├── main.py                 # CLI entry point
│   ├── scheduler/
│   │   ├── __init__.py
│   │   └── scheduler.py        # UCB1 + CPU throttling
│   ├── workers/
│   │   ├── __init__.py
│   │   ├── micro.py            # Fast deterministic tactics
│   │   ├── copilot.py          # Lean Copilot
│   │   ├── dojo.py             # LeanDojo wrapper
│   │   ├── reprover.py         # ReProver (stub)
│   │   ├── sketch.py           # Sketch (stub)
│   │   └── lean_repl.py        # Alternative to LeanDojo
│   ├── cache/
│   │   ├── __init__.py
│   │   └── store.py            # SQLite ledger
│   ├── brokers/
│   │   ├── __init__.py
│   │   └── marketplace.py      # Lemma requests
│   ├── dashboards/
│   │   ├── __init__.py
│   │   └── serve.py            # FastAPI dashboard
│   ├── cli/
│   │   ├── __init__.py
│   │   └── run_bank.py         # Benchmark runner
│   └── requirements.txt
├── bench/
│   ├── bank.jsonl              # 64 test goals
│   └── results/                # Timestamped results
├── PCP/
│   └── Basic.lean              # Test theorems
├── .venv/                      # Python 3.13 env
├── .venv-lean/                 # Python 3.12 env
├── Makefile                    # All commands
├── QUICK_START.md              # 30-second test
├── TESTING_INSTRUCTIONS.md     # Full testing guide
├── HANDOFF_SUMMARY.md          # This file
├── lean-toolchain              # v4.15.0
├── lakefile.toml               # Mathlib v4.15.0
└── lake-manifest.json          # Pinned dependencies
```

## Key Commands Reference

```bash
# Setup
make orch-init              # Install Python 3.13 env
make orch-lean-init         # Install Python 3.12 env + LeanDojo
make orch-test              # Test LeanDojo initialization

# Testing
bin/orch bank               # Stub workers
bin/orch-lean bank          # Real workers (after LeanDojo build)
bin/orch dashboard          # Start monitoring dashboard

# Development
lake build PCP.Basic        # Build Lean project
lake clean                  # Clean build artifacts
git status                  # Check uncommitted changes
```

## Next Steps

### Immediate (Tester)

1. Run `make orch-init`
2. Run `bin/orch bank --timeout 10`
3. Verify ~60% solve rate
4. Check if LeanDojo build complete
5. If complete, test `bin/orch-lean bank`

### Short-term (Developer)

1. Implement goal extraction utility
2. Wire Lean Copilot (add to lakefile)
3. Test real proof search on PCP theorems
4. Fix ExtractData.lean build error if persists
5. Add logging to file (currently console only)

### Medium-term (Team)

1. GitHub Actions CI pipeline
2. Performance regression tests
3. Blueprint integration for progress tracking
4. Lemma marketplace activation
5. ReProver integration

## Questions & Debugging

**Q: Build taking forever?**
A: Normal for first LeanDojo run. Use stub workers meanwhile.

**Q: 0% solve rate?**
A: Check which script (orch vs orch-lean). Stubs use randomness.

**Q: Import errors?**
A: Check Python env activated. Use correct wrapper script.

**Q: Where are results?**
A: `bench/results/bank-TIMESTAMP.json`

**Q: How to monitor live?**
A: `bin/orch dashboard` then http://localhost:8080

## Contact

- **Project Docs:** `docs/engine.md`, `docs/proof.md`
- **LeanDojo:** https://leandojo.readthedocs.io/
- **Issues:** Check git history and commit messages

## Final Checklist

Before starting tests:

- [ ] Git repo cloned to `/Users/jalex/repos/pcp-rpg`
- [ ] Python 3.12+ and 3.13+ available
- [ ] `elan` installed (Lean version manager)
- [ ] GitHub token configured (optional, reduces rate limits)
- [ ] Read QUICK_START.md
- [ ] Read TESTING_INSTRUCTIONS.md

**Ready to test!** Start with `make orch-init && bin/orch bank --timeout 10`

---

**Last Update:** 2025-10-01
**Git Commit:** 0252d7c
**Lean:** v4.15.0
**Mathlib:** v4.15.0 (9837ca9d)
**LeanDojo:** 4.20.0
