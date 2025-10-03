# LeanDojo Integration - In Progress

**Status**: 🔨 Building  
**Started**: 2025-10-01 23:28  
**ETA**: ~25 minutes remaining

## What's Happening

LeanDojo is currently:
1. Tracing the PCP repo dependencies
2. Building mathlib (2548 modules) - **this is the slow part**
3. Will then test 4 theorems with different tactics

## Setup Complete ✅

### Environment
- Python 3.12.11 virtual environment: `.venv-lean`
- LeanDojo 4.20.0 installed
- All orchestrator dependencies installed

### Test File Created
Created `PCP/Test/Basic.lean` with 8 simple theorems:
- `nat_zero_add` - should solve with `rfl`
- `nat_add_zero` - should solve with `simp`
- `nat_mul_zero` - should solve with `ring`
- `nat_zero_mul` - should solve with `ring`
- `nat_sub_self` - should solve with `omega`
- `nat_sub_zero` - should solve with `omega`
- `nat_add_comm` - harder (needs existing lemmas)
- `nat_add_assoc` - harder (needs induction)

### Test Script Running
Located at: `/tmp/test_leandojo_full.py`
- Running as PID: `60853` (from /tmp/leandojo_test.pid)
- Output: `/tmp/leandojo_test.log`

## Monitoring the Build

```bash
# Watch progress
bash /tmp/monitor_leandojo.sh

# Or tail the log
tail -f /tmp/leandojo_test.log

# Check if still running
ps -p $(cat /tmp/leandojo_test.pid)
```

## What Happens Next

Once the build completes, the script will:
1. Test `PCP.Test.nat_zero_add` with `rfl` tactic
2. Test `PCP.Test.nat_add_zero` with `simp` tactic  
3. Test `PCP.Test.nat_mul_zero` with `ring` tactic
4. Test `PCP.Test.nat_sub_self` with `omega` tactic
5. Print a summary of which tactics succeeded

Expected results:
- `rfl` on `nat_zero_add`: ✓ (reflexivity)
- `simp` on `nat_add_zero`: ✓ (simplifier knows this)
- `ring` on `nat_mul_zero`: ✓ (ring normalization)
- `omega` on `nat_sub_self`: ✓ (linear arithmetic)

## After LeanDojo Testing

Once we confirm LeanDojo works, we'll:
1. Run the orchestrator with real LeanDojo (not mock mode)
2. Test micro worker on all 8 theorems in Basic.lean
3. Measure success rates and timing
4. Integrate with ledger/cache for persistence

## Files Modified

- `PCP/Test/Basic.lean` - New test file with 8 theorems
- `orchestrator/workers/dojo.py` - Added `mock_mode` parameter
- `.venv-lean/` - Python 3.12 environment with LeanDojo

## Build Progress

Current: Building mathlib modules (warnings about doc-strings are normal)

Check line count to estimate progress:
```bash
wc -l /tmp/leandojo_test.log
# Full build generates ~50,000+ lines of output
```
