# Orchestrator Quick Reference

## Installation

```bash
make orch-init                    # Install dependencies
source .venv/bin/activate         # Activate virtualenv
```

## Commands

```bash
make orch-bank                    # Run benchmark (120s)
make orch-bg                      # Background search (indefinite)
make orch-dashboard               # Web UI at :8000
make orch-stats                   # Show statistics
```

## Configuration

```bash
export ORCH_PROFILE=1             # 0=micro, 1=+copilot, 2=+reprover
export ORCH_CPU_TARGET=0.5        # Target CPU (0-1)
export ORCH_MAX_LIGHT=8           # Light workers
export ORCH_MAX_HEAVY=2           # Heavy workers
```

## Files

| Path | Purpose |
|------|---------|
| `orchestrator/scheduler/scheduler.py` | UCB scheduler |
| `orchestrator/workers/micro.py` | Quick tactics |
| `orchestrator/workers/copilot.py` | Lean Copilot (stub) |
| `orchestrator/workers/reprover.py` | ReProver RAG (stub) |
| `orchestrator/workers/dojo.py` | LeanDojo wrapper (stub) |
| `orchestrator/brokers/marketplace.py` | Lemma requests |
| `orchestrator/cache/store.py` | SQLite ledger |
| `orchestrator/dashboards/serve.py` | FastAPI dashboard |
| `orchestrator/main.py` | CLI entry point |
| `bench/bank.jsonl` | 64 toy lemmas |
| `orchestrator/cache/ledger.db` | SQLite database (created on first run) |

## Architecture

```
Goal Queue → Scheduler → [Strategy Selection via UCB]
                ↓
    ┌───────────┴──────────┐
    ↓                      ↓
  Light Tasks           Heavy Tasks
  (micro, quick)        (reprover, deep)
    ↓                      ↓
  Result ← Ledger ← Cache ← Result
```

## Profiles

| Profile | Strategies | ML Deps | Use Case |
|---------|-----------|---------|----------|
| 0 | micro | None | Testing, baseline |
| 1 | micro, copilot, sketch | Copilot | Production (medium) |
| 2 | all strategies | Copilot, ReProver | Production (hard goals) |

## API Endpoints

| Endpoint | Purpose |
|----------|---------|
| `GET /` | Dashboard HTML |
| `GET /api/stats` | Ledger statistics (JSON) |
| `GET /api/marketplace` | Marketplace status (JSON) |
| `GET /api/health` | Health check |

## Data Structures

```python
Goal(
    id: str,
    text: str,
    context: list[str],
    estimated_difficulty: float,  # 0-1
    priority: float,               # 0-1
)

Result(
    success: bool,
    strategy: StrategyType,
    tactics: list[str],
    time_seconds: float,
    subgoals: list[Goal],
    error: Optional[str],
)
```

## Debugging

```bash
# Inspect ledger
sqlite3 orchestrator/cache/ledger.db

# View attempts
SELECT * FROM attempts ORDER BY timestamp DESC LIMIT 10;

# Success rates
SELECT strategy, COUNT(*), SUM(success), AVG(time_seconds)
FROM attempts GROUP BY strategy;

# Monitor CPU
watch -n 1 "ps aux | grep python"
```

## Common Tasks

### Add a new strategy

1. Create `orchestrator/workers/my_strategy.py`:
   ```python
   async def run_my_strategy(goal: Goal, timeout: float) -> Result:
       # ... implementation ...
       return Result(success=..., strategy=StrategyType.MY_STRATEGY, ...)
   ```

2. Add to `StrategyType` enum in `scheduler/scheduler.py`

3. Register in `main.py`:
   ```python
   scheduler.register_worker(StrategyType.MY_STRATEGY, run_my_strategy)
   ```

4. Add to profile logic in `get_enabled_strategies()`

### Add a benchmark lemma

Edit `bench/bank.jsonl`:
```json
{"id": "my_lemma", "goal": "∀ n : ℕ, ...", "difficulty": 0.4, "priority": 0.7}
```

### Request a helper lemma

```python
from orchestrator.brokers import marketplace

ticket_id = await marketplace.request_lemma(
    goal="∀ ε > 0, ...",
    context=["continuous", "Hausdorff"],
    suggested_name="my_module.helper_lemma",
    constraints=["noncomputable"],
    priority=0.8,
)
```

### Check cache for goal

```python
from orchestrator.cache import Ledger

ledger = Ledger()
cached = ledger.get_cached_tactics(goal.text)
if cached:
    print(f"Success rate: {cached['success_rate']}")
    print(f"Tactics: {cached['tactics']}")
```

## Performance Tips

- Start with Profile 0 to test infrastructure
- Increase `ORCH_MAX_LIGHT` for more throughput on easy goals
- Decrease `ORCH_CPU_TARGET` if laptop feels sluggish
- Monitor `bench/results/` for strategy effectiveness
- Use dashboard to identify bottlenecks

## Integration Checklist

- [ ] Install LeanDojo: `pip install lean-dojo`
- [ ] Implement `workers/dojo.py` (replace stub)
- [ ] Add LeanCopilot to `lakefile.toml`
- [ ] Implement `workers/copilot.py` (replace stub)
- [ ] Download ReProver models
- [ ] Build premise index from mathlib
- [ ] Implement `workers/reprover.py` (replace stub)
- [ ] Add goal extraction from Lean files
- [ ] Wire blueprint status updates
- [ ] Set up GitHub Actions for CI

## Troubleshooting

| Issue | Solution |
|-------|----------|
| `typer not installed` | `pip install -r orchestrator/requirements.txt` |
| `psutil not available` | Optional: `pip install psutil` |
| Dashboard won't start | `pip install fastapi uvicorn` |
| CPU usage too high | Lower `ORCH_CPU_TARGET` or reduce `ORCH_MAX_*` |
| No goals processed | Check `bench/bank.jsonl` exists |
| Timeout errors | Increase per-strategy timeouts in workers |
| Ledger DB locked | Close other connections, restart orchestrator |

## Status

✅ **Working now** (with stubs):
- Scheduler + UCB + CPU throttling
- All worker interfaces
- Lemma marketplace
- Cache/ledger
- Dashboard
- CLI
- Benchmark bank

🔨 **Next integrations**:
- LeanDojo (workers/dojo.py)
- Lean Copilot (workers/copilot.py)
- ReProver (workers/reprover.py)
- Goal extraction (scan .lean files)

## Learn More

- [ORCHESTRATOR_SETUP.md](../ORCHESTRATOR_SETUP.md) - Setup guide
- [orchestrator/README.md](README.md) - Architecture overview
- [IMPLEMENTATION_NOTES.md](IMPLEMENTATION_NOTES.md) - Technical details
- [docs/engine.md](../docs/engine.md) - Original design doc
