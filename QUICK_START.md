# Quick Start - PCP Orchestrator

## 30-Second Test

```bash
# Setup (one time)
make orch-init

# Run test
bin/orch bank --timeout 10
```

**Expected:** `~40/64 goals solved (62%)` in under 10 seconds

## What Just Happened?

The orchestrator:
1. Loaded 64 toy theorems from `bench/bank.jsonl`
2. Used UCB1 algorithm to select proof strategies
3. Ran stub workers simulating tactics
4. Throttled CPU to stay around 50% utilization
5. Cached results in SQLite for deduplication
6. Saved full results to `bench/results/`

## Key Commands

```bash
# Test with stub workers (fast, no Lean dependencies)
bin/orch bank --timeout 20 --profile 0

# Test with real LeanDojo (requires build complete)
bin/orch-lean bank --timeout 30 --profile 1

# Test LeanDojo initialization
make orch-test

# Start monitoring dashboard
bin/orch dashboard
```

## Status Check

```bash
# Check if LeanDojo is ready
make orch-test

# ✓ Output should show:
# ✓ LeanDojo imported successfully
# ✓ DojoWrapper initialized
```

## What's Working

✅ **Complete Orchestrator Framework**
- Scheduler with UCB1 strategy selection
- CPU throttling with EMA (maintains ~50% target)
- SQLite cache/ledger for result persistence
- Lemma marketplace for helper requests
- FastAPI dashboard for monitoring
- Multi-environment setup (Python 3.13 + 3.12)

✅ **Workers**
- Stub workers: Fully functional for testing
- Real workers: Code ready, awaiting LeanDojo build

✅ **Infrastructure**
- Wrapper scripts (`bin/orch`, `bin/orch-lean`)
- Makefile targets for all operations
- Test theorem suite in PCP/Basic.lean
- Comprehensive documentation

## What's Pending

⏳ **LeanDojo Build** (One-Time, ~10-15 min)
- Currently building mathlib4 cache
- Check status: `ps aux | grep -E "lean|lake"`
- Once complete, real proof search becomes available

🔲 **Goal Extraction** (Next Step)
- Scan Lean files for `sorry` declarations
- Extract metadata (file paths, theorem names)
- Feed real PCP goals to orchestrator

## Directory Structure

```
pcp-rpg/
├── bin/
│   ├── orch              # Orchestrator (Python 3.13)
│   ├── orch-lean         # With LeanDojo (Python 3.12)
│   └── orch-test-dojo    # Test LeanDojo setup
├── orchestrator/
│   ├── scheduler/        # UCB1 + CPU throttling
│   ├── workers/          # Proof search strategies
│   ├── cache/            # SQLite ledger
│   ├── brokers/          # Lemma marketplace
│   └── dashboards/       # FastAPI monitoring
├── bench/
│   ├── bank.jsonl        # 64 test goals
│   └── results/          # Timestamped results
├── PCP/
│   └── Basic.lean        # Test theorems with sorry
├── Makefile              # All commands
└── TESTING_INSTRUCTIONS.md  # Full testing guide
```

## Troubleshooting

**Problem:** `lean-dojo not installed`
**Solution:** Use `bin/orch-lean` instead of `bin/orch`

**Problem:** LeanDojo build taking forever
**Solution:** Normal! First build takes 10-15min. Use stub workers meanwhile.

**Problem:** 0% solve rate
**Solution:** Stub workers use randomness. Real workers need LeanDojo build complete.

## Next Steps

1. Wait for LeanDojo build to complete
2. Test real workers: `bin/orch-lean bank`
3. Implement goal extraction from PCP files
4. Wire Lean Copilot for Profile 1
5. Add GitHub Actions CI

## Resources

- **Full Testing Guide:** [TESTING_INSTRUCTIONS.md](TESTING_INSTRUCTIONS.md)
- **System Design:** [docs/engine.md](docs/engine.md)
- **Proof Plan:** [docs/proof.md](docs/proof.md)
- **LeanDojo Docs:** https://leandojo.readthedocs.io/

---

**TL;DR:** Run `make orch-init && bin/orch bank` to see it work!
