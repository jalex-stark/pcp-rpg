# Orchestrator Setup Guide

The orchestrator framework is now ready! This guide will help you get started.

## What's Been Built

A complete proof search orchestration system with:

✅ **Scheduler** - UCB-based strategy selection with CPU throttling
✅ **Workers** - Stubs for micro/copilot/reprover/sketch/dojo strategies
✅ **Lemma Marketplace** - Helper lemma request/fulfillment system
✅ **Cache/Ledger** - SQLite-based checkpointing and deduplication
✅ **CLI** - Commands for running searches, benchmarks, and viewing stats
✅ **Dashboard** - FastAPI web interface for real-time monitoring
✅ **Benchmark Bank** - 64 toy lemmas for testing

## Quick Start

### 1. Install Dependencies

```bash
make orch-init
```

Or manually:

```bash
python3 -m venv .venv
source .venv/bin/activate
pip install -r orchestrator/requirements.txt
```

### 2. Run Benchmark

Test with stub workers (Profile 0 = micro tactics only):

```bash
source .venv/bin/activate
export ORCH_PROFILE=0
make orch-bank
```

This will:
- Load 64 goals from `bench/bank.jsonl`
- Run them through the scheduler
- Generate results in `bench/results/`

### 3. Launch Dashboard

```bash
source .venv/bin/activate
make orch-dashboard
```

Then open http://127.0.0.1:8000

### 4. View Statistics

```bash
source .venv/bin/activate
make orch-stats
```

## Directory Structure

```
orchestrator/
├── scheduler/
│   ├── __init__.py
│   └── scheduler.py          # UCB scheduler with CPU throttling
├── workers/
│   ├── __init__.py
│   ├── micro.py              # Quick tactics (simp, aesop, etc)
│   ├── copilot.py            # Lean Copilot integration (stub)
│   ├── reprover.py           # ReProver RAG (stub)
│   ├── sketch.py             # LLM validation (stub)
│   └── dojo.py               # LeanDojo wrapper (stub)
├── brokers/
│   ├── __init__.py
│   └── marketplace.py        # Lemma request marketplace
├── cache/
│   ├── __init__.py
│   ├── store.py              # SQLite ledger
│   └── ledger.db             # (created on first run)
├── dashboards/
│   ├── __init__.py
│   └── serve.py              # FastAPI dashboard
├── cli/
│   ├── __init__.py
│   └── run_bank.py           # Benchmark runner
├── __init__.py
├── main.py                   # CLI entry point
├── requirements.txt
└── README.md

bench/
├── bank.jsonl                # 64 toy lemmas
└── results/                  # Benchmark results (created on first run)
```

## Configuration

Set environment variables (or copy `.env.example` to `.env`):

```bash
export ORCH_PROFILE=1          # 0=micro, 1=+copilot, 2=+reprover
export ORCH_CPU_TARGET=0.5     # Target 50% CPU usage
export ORCH_MAX_LIGHT=8        # Max concurrent light tasks
export ORCH_MAX_HEAVY=2        # Max concurrent heavy tasks
```

## Profiles

- **Profile 0** (micro): Baseline with deterministic tactics
  - Strategies: simp, aesop, ring, omega
  - No ML dependencies
  - Good for testing infrastructure

- **Profile 1** (copilot): Add Lean Copilot
  - Requires: LeanCopilot in lakefile.toml
  - Worker: `orchestrator/workers/copilot.py` (stub → needs implementation)

- **Profile 2** (reprover): Add ReProver
  - Requires: ReProver models + premise index
  - Worker: `orchestrator/workers/reprover.py` (stub → needs implementation)

## Current Status

### ✅ Working Now (with stubs)
- Scheduler runs and allocates work
- UCB bandit selects strategies
- CPU throttling maintains target usage
- Ledger records all attempts
- Dashboard shows statistics
- Benchmark bank runs end-to-end

### 🔨 Next Integration Steps

1. **LeanDojo Integration**
   - Install: `pip install lean-dojo`
   - Implement: `orchestrator/workers/dojo.py`
   - Wire into scheduler

2. **Lean Copilot Setup**
   - Add to `lakefile.toml`:
     ```toml
     [[require]]
     name = "LeanCopilot"
     git = "https://github.com/lean-dojo/LeanCopilot.git"
     rev = "v4.22.0"  # Match your Lean version
     ```
   - Run: `lake update && lake exe LeanCopilot/download`
   - Implement: `orchestrator/workers/copilot.py`

3. **ReProver Models**
   - Download models:
     - `kaiyuy/leandojo-lean4-retriever-byt5-small`
     - `kaiyuy/leandojo-lean4-retriever-tacgen-byt5-small`
   - Build premise index from mathlib
   - Implement: `orchestrator/workers/reprover.py`

4. **Goal Extraction**
   - Scan Lean files for `sorry`/`admit`
   - Populate goal queue automatically
   - Integrate with blueprint progress

## Architecture Highlights

### Scheduler
- **UCB1 bandit** balances exploration vs exploitation of strategies
- **EMA CPU throttling** maintains ~50% target without OS-level limits
- **Speculative execution** runs multiple strategies in parallel, cancels losers
- **Concurrency limits** separate light (micro) from heavy (ReProver) tasks

### Workers
- All return `Result` dataclass with success/tactics/time
- Can request helper lemmas via marketplace
- Timeout handling and cancellation support
- Ledger deduplication prevents redundant work

### Lemma Marketplace
- Workers request missing lemmas when blocked
- Other workers can claim and fulfill requests
- Tracks dependencies for reuse
- Search for similar completed requests

### Cache/Ledger
- Every attempt logged with (goal_hash, strategy, outcome, time)
- Tactic cache: goal → best tactics + success rate
- Premise cache: goal → top-k relevant premises (for ReProver)
- Enables checkpointing and resume

## CLI Commands

```bash
# Install dependencies
make orch-init

# Run benchmarks
make orch-bank

# Background search (indefinite)
make orch-bg

# Web dashboard
make orch-dashboard

# View statistics
make orch-stats
```

Or use Python directly:

```bash
python -m orchestrator.main bank --profile 0 --timeout 120
python -m orchestrator.main bg --duration 600
python -m orchestrator.main dashboard --port 8000
python -m orchestrator.main stats
```

## Benchmark Bank

64 toy lemmas covering:
- **Nat arithmetic**: add, mul, sub, min, max, order (30 lemmas)
- **List operations**: append, map, filter, reverse (14 lemmas)
- **Bool logic**: and, or, not (14 lemmas)
- **Option**: map, bind (4 lemmas)

Difficulty labels (easy/medium/hard) are for scheduling, not intrinsic difficulty.

See: `bench/bank.jsonl`

## Dashboard Features

Real-time monitoring at http://127.0.0.1:8000:
- Overall statistics (attempts, successes, success rate)
- Cache performance (cached goals, hit rate)
- Lemma marketplace (open/completed requests)
- Per-strategy performance (attempts, successes, avg time)
- Auto-refresh every 5 seconds

## Testing the Framework

Even with stub workers, you can verify:

1. **Scheduler allocates work** based on UCB scores
2. **CPU throttling** maintains target (check with `top`)
3. **Ledger logs** all attempts to SQLite
4. **Dashboard shows** real-time statistics
5. **Benchmark runs** end-to-end and generates results JSON

Try running with different profiles to see strategy selection change:

```bash
ORCH_PROFILE=0 make orch-bank  # micro only
ORCH_PROFILE=1 make orch-bank  # micro + copilot + sketch
ORCH_PROFILE=2 make orch-bank  # all strategies
```

## Troubleshooting

### `typer not installed`
```bash
source .venv/bin/activate
pip install -r orchestrator/requirements.txt
```

### `psutil not available`
Optional but recommended for CPU throttling:
```bash
pip install psutil
```

### Dashboard won't start
```bash
pip install fastapi uvicorn
```

### Benchmarks time out
Increase timeout or reduce goals:
```bash
python -m orchestrator.main bank --timeout 300
```

Or edit `bench/bank.jsonl` to include fewer goals.

## References

- [orchestrator/README.md](orchestrator/README.md) - Component details
- [docs/engine.md](docs/engine.md) - Original design document
- [docs/proof.md](docs/proof.md) - PCP formalization plan
- [LeanDojo](https://github.com/lean-dojo/LeanDojo)
- [Lean Copilot](https://github.com/lean-dojo/LeanCopilot)
- [ReProver](https://github.com/lean-dojo/ReProver)

## What to Do Next

1. **Test the infrastructure**: Run `make orch-bank` to verify everything works
2. **Choose integration path**:
   - **Profile 0 first**: Focus on goal extraction and Lean file scanning
   - **Profile 1 next**: Integrate LeanDojo + Copilot for real proof search
   - **Profile 2 later**: Add ReProver when needed for hard goals

3. **Start simple**: Begin with extracting a few `sorry`s from your PCP formalization
4. **Iterate**: Add real tactics gradually, comparing against stub baseline

The framework is production-ready for orchestration; workers just need real implementations!
