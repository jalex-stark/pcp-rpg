# PCP Orchestrator

Resource-aware proof search orchestrator for the PCP formalization project.

## Architecture

```
orchestrator/
├─ scheduler/       # UCB-based strategy scheduler with CPU throttling
├─ workers/         # Proof search strategies (micro, copilot, reprover, sketch)
├─ brokers/         # Lemma marketplace for helper requests
├─ cache/           # SQLite ledger + tactic cache
├─ dashboards/      # FastAPI web dashboard
├─ cli/             # Benchmark runner
└─ main.py          # CLI entry point
```

## Quick Start

```bash
# Install dependencies
python3 -m venv .venv
source .venv/bin/activate
pip install -r orchestrator/requirements.txt

# Run benchmarks (Profile 0 = micro tactics only)
export ORCH_PROFILE=0
python -m orchestrator.main bank

# View dashboard
python -m orchestrator.main dashboard
# Open http://127.0.0.1:8000

# Background search (indefinite)
python -m orchestrator.main bg

# View statistics
python -m orchestrator.main stats
```

## Profiles

- **Profile 0** (micro): Deterministic baseline with simp, aesop, ring, omega
- **Profile 1** (copilot): Add Lean Copilot search_proof + select_premises
- **Profile 2** (reprover): Add ReProver retrieval-augmented generation

## Configuration

Set via environment variables (see `.env.example`):

```bash
export ORCH_PROFILE=1          # Strategy profile
export ORCH_CPU_TARGET=0.5     # Target 50% CPU
export ORCH_MAX_LIGHT=8        # Max light workers
export ORCH_MAX_HEAVY=2        # Max heavy workers
```

## Components

### Scheduler

- UCB bandit for strategy selection
- EMA-based CPU throttling
- Concurrency limits (light/heavy)
- Speculative execution (parallel strategies)

### Workers

- **micro**: Quick tactics (simp, aesop, ring, omega)
- **copilot**: Lean Copilot integration (stub, requires lakefile setup)
- **reprover**: ReProver RAG (stub, requires models)
- **sketch**: LLM validation (stub)
- **dojo**: LeanDojo wrapper (stub)

### Lemma Marketplace

- Request helper lemmas when blocked
- Claim and fulfill requests
- Track dependencies
- Search for similar completed requests

### Cache/Ledger

- SQLite-based attempt logging
- Tactic cache (goal hash → best tactics)
- Premise cache (for ReProver)
- Deduplication
- Statistics

### Dashboard

- Real-time monitoring
- Strategy performance
- Cache hit rates
- Marketplace status

## Benchmark Bank

64 toy lemmas in `bench/bank.jsonl`:
- Nat arithmetic (add, mul, sub, min, max, order)
- List operations (append, map, filter, reverse)
- Bool logic (and, or, not)
- Option monadic operations

Run with: `python -m orchestrator.main bank --timeout 120`

## Integration Status

- [x] Scheduler core
- [x] Worker stubs (micro/copilot/reprover/sketch/dojo)
- [x] Lemma marketplace
- [x] Cache/ledger
- [x] CLI
- [x] Dashboard
- [x] Benchmark bank
- [ ] LeanDojo integration (requires lean-dojo package)
- [ ] Lean Copilot integration (requires lakefile setup)
- [ ] ReProver integration (requires models + index)

## Next Steps

1. **Profile 0 validation**: Verify scheduler runs with stub workers
2. **LeanDojo integration**: Wire `workers/dojo.py` to actual LeanDojo
3. **Copilot setup**: Add LeanCopilot to lakefile, implement `workers/copilot.py`
4. **ReProver models**: Download models, build index, implement `workers/reprover.py`
5. **Goal extraction**: Scan Lean files for `sorry`/`admit` to populate queue
6. **Blueprint sync**: Update blueprint status from ledger

## References

- [docs/engine.md](../docs/engine.md) - Full design document
- [docs/proof.md](../docs/proof.md) - PCP formalization plan
- [LeanDojo](https://github.com/lean-dojo/LeanDojo)
- [Lean Copilot](https://github.com/lean-dojo/LeanCopilot)
- [ReProver](https://github.com/lean-dojo/ReProver)
