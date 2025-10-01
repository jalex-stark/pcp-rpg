# Implementation Notes

Technical details for extending the orchestrator framework.

## Scheduler Implementation

### UCB Bandit (`scheduler.py:ucb_score`)

```python
mean = self.success_rate[strategy]
n = max(1, self.trials[strategy])
N = sum(self.trials.values()) + 1
exploration = 1.5 * ((2 * (N).bit_length()) / n) ** 0.5
return mean + exploration
```

- **Mean**: Exponential moving average (α=0.1) of success
- **Exploration bonus**: √(2 log N / n) with tunable constant (1.5)
- **Updates**: After each attempt, success_rate ← 0.9 × old + 0.1 × (1 if success else 0)

### CPU Throttling (`scheduler.py:throttle`)

```python
current_load = psutil.getloadavg()[0] / psutil.cpu_count()
self.cpu_ema = α × current_load + (1 - α) × self.cpu_ema
if cpu_ema > target:
    sleep(min(1.0, 4 × (cpu_ema - target)))
```

- Uses load average (1 min), not instantaneous CPU%
- EMA smoothing (α=0.1) prevents oscillation
- Exponential backoff based on overload
- No OS-level CPU limiting (brittle on macOS)

### Concurrency Control

- **Light tasks** (difficulty < 0.6): fast tactics, max 8 concurrent
- **Heavy tasks** (difficulty ≥ 0.6): deep search, max 2 concurrent
- Separate semaphores prevent heavy tasks from starving
- Task cancelled if slot unavailable (re-queued with backoff)

### Speculative Execution

```python
strategies = select_strategies(goal, n=3)  # Top 3 by UCB
tasks = [run_strategy(s, goal) for s in strategies]
done, pending = await wait(tasks, return_when=FIRST_COMPLETED)
for task in pending: task.cancel()
```

- Launches multiple strategies in parallel
- First success wins, others cancelled
- Updates only winning strategy's UCB stats
- Minimizes latency for easy goals

## Worker Interface

All workers implement:

```python
async def run_<strategy>(goal: Goal, timeout: float) -> Result:
    """
    Args:
        goal: Goal with .id, .text, .context, .estimated_difficulty
        timeout: Max seconds to try

    Returns:
        Result(success, strategy, tactics, time_seconds, subgoals, error)
    """
```

### Integration with LeanDojo

Example real implementation:

```python
from lean_dojo import Dojo, LeanGitRepo

async def run_micro(goal: Goal, timeout: float) -> Result:
    repo = LeanGitRepo(".", commit="HEAD")
    with Dojo(repo) as dojo:
        # Get proof state
        state = dojo.get_state(goal.id)

        # Try tactics
        for tactic in ["simp_all", "aesop?", "omega"]:
            try:
                result = await asyncio.wait_for(
                    dojo.run_tac(state, tactic),
                    timeout=timeout / 3
                )
                if len(result.goals) == 0:  # Closed all goals
                    return Result(
                        success=True,
                        strategy=StrategyType.MICRO,
                        tactics=[tactic],
                        time_seconds=...,
                    )
                state = result  # Continue from new state
            except asyncio.TimeoutError:
                continue

    return Result(success=False, ...)
```

### Integration with Lean Copilot

Via LeanDojo executing Copilot tactics:

```python
async def run_copilot(goal: Goal, timeout: float) -> Result:
    with Dojo(repo) as dojo:
        state = dojo.get_state(goal.id)

        # Step 1: Select premises
        result = await dojo.run_tac(state, "select_premises (num := 12)")
        state = result

        # Step 2: Search with Aesop + LLM
        result = await asyncio.wait_for(
            dojo.run_tac(
                state,
                "search_proof (beam := 4) (temperature := 0.2)"
            ),
            timeout=timeout
        )

        if len(result.goals) == 0:
            # Extract proof script from dojo trace
            proof = dojo.get_proof_script(state)
            return Result(success=True, tactics=[proof], ...)

    return Result(success=False, ...)
```

### Integration with ReProver

```python
from transformers import AutoTokenizer, AutoModel
import faiss

class ReProverWorker:
    def __init__(self):
        self.retriever = AutoModel.from_pretrained(
            "kaiyuy/leandojo-lean4-retriever-byt5-small"
        )
        self.generator = AutoModel.from_pretrained(
            "kaiyuy/leandojo-lean4-retriever-tacgen-byt5-small"
        )
        self.index = faiss.read_index("cache/premise_index.faiss")
        self.corpus = load_corpus()  # mathlib + local lemmas

    async def run(self, goal: Goal, timeout: float) -> Result:
        # Encode goal
        embedding = self.retriever.encode(goal.text)

        # Retrieve premises
        _, indices = self.index.search(embedding, k=12)
        premises = [self.corpus[i] for i in indices[0]]

        # Generate tactics
        tactics = self.generator.generate(
            goal=goal.text,
            premises=[p.statement for p in premises],
            beam=4,
            max_length=128,
        )

        # Try each with Dojo
        with Dojo(repo) as dojo:
            state = dojo.get_state(goal.id)
            for tactic in tactics:
                result = await dojo.run_tac(state, tactic)
                if len(result.goals) == 0:
                    return Result(
                        success=True,
                        tactics=[tactic],
                        metadata={'premises': [p.name for p in premises]},
                    )

        return Result(success=False, ...)
```

## Lemma Marketplace

### Workflow

1. **Worker blocked** on missing lemma:
   ```python
   ticket_id = await marketplace.request_lemma(
       goal="∀ ε > 0, ...",
       context=["Hausdorff", "continuous"],
       suggested_name="foo.bar_continuous",
       constraints=["noncomputable"],
       priority=0.8,
   )
   ```

2. **Supplier claims ticket**:
   ```python
   tickets = await marketplace.get_open_tickets(limit=10)
   success = await marketplace.claim_ticket(tickets[0].ticket_id, "copilot")
   ```

3. **Supplier completes proof**:
   ```python
   proof = """
   theorem foo.bar_continuous : ... := by
     intro ε hε
     ...
   """
   await marketplace.complete_ticket(ticket_id, proof, "copilot")
   ```

4. **Original requester retrieves**:
   ```python
   ticket = await marketplace.get_ticket(ticket_id)
   if ticket.status == TicketStatus.COMPLETED:
       # Use ticket.completed_proof
   ```

### Deduplication

Before requesting, search for similar:

```python
similar = await marketplace.search_similar(goal, limit=5)
if similar and similar[0].status == TicketStatus.COMPLETED:
    # Reuse existing proof
    return similar[0].completed_proof
```

## Cache/Ledger

### Deduplication

```python
goal_hash = ledger.hash_goal(goal.text)
if ledger.check_duplicate(goal.text, strategy):
    # Already tried this combo, skip
    return None
```

Goal normalization:
- Strip whitespace
- Sort implicit args
- Erase binder names
- Canonical ordering

### Tactic Cache

After success:

```python
ledger.update_tactic_cache(
    goal.text,
    tactics=["simp [*]", "aesop"],
    success_rate=0.85,
    avg_time=2.3,
)
```

On new goal:

```python
cached = ledger.get_cached_tactics(goal.text)
if cached and cached['success_rate'] > 0.7:
    # Try cached tactics first
    for tactic in cached['tactics']:
        result = await dojo.run_tac(state, tactic)
        if result.success:
            return Result(...)
```

### Checkpointing

Every attempt writes:

```sqlite
INSERT INTO attempts (goal_hash, strategy, success, time_seconds, tactics, ...)
VALUES (?, ?, ?, ?, ?, ...)
```

On crash, resume frontier:

```python
cursor.execute("""
    SELECT DISTINCT goal_hash, goal_text
    FROM attempts
    WHERE success = 0
    AND goal_hash NOT IN (
        SELECT goal_hash FROM attempts WHERE success = 1
    )
""")
```

## Dashboard API

### Endpoints

- `GET /` - HTML dashboard
- `GET /api/stats` - Ledger statistics (JSON)
- `GET /api/marketplace` - Marketplace status (JSON)
- `GET /api/health` - Health check

### Real-time Updates

JavaScript polls `/api/stats` every 5 seconds:

```javascript
async function refreshData() {
    const stats = await fetch('/api/stats').then(r => r.json());
    const marketplace = await fetch('/api/marketplace').then(r => r.json());
    updateDisplay(stats, marketplace);
}
setInterval(refreshData, 5000);
```

For production, consider WebSockets for true push updates.

## Benchmark Runner

### Flow

1. Load goals from `bench/bank.jsonl`
2. Create scheduler with config
3. Enqueue all goals
4. Monitor progress until timeout or completion
5. Write results JSON to `bench/results/`

### Results Format

```json
{
  "timestamp": "20250930-214500",
  "goals_total": 64,
  "goals_processed": 64,
  "goals_solved": 48,
  "strategies": {
    "micro": {"used": 64, "succeeded": 32},
    "copilot": {"used": 32, "succeeded": 12},
    ...
  },
  "config": {
    "timeout": 120,
    "max_heavy": 2,
    "max_light": 8,
    "cpu_target": 0.5,
    "profile": 1
  }
}
```

## Performance Tuning

### Scheduler Parameters

- `max_heavy`: Higher = more parallelism for hard goals, but higher CPU
- `max_light`: Higher = more throughput for easy goals
- `cpu_target`: 0.5 = 50% (good for laptop usability)
- `cpu_alpha`: Lower = smoother throttling, slower response

### UCB Exploration

- Increase constant (1.5 → 2.0) for more exploration
- Decrease for more exploitation of known-good strategies

### Timeout Tuning

Per-strategy defaults:
- micro: 8s (quick tactics)
- copilot: 20s (Aesop search)
- reprover: 60s (retrieval + generation)
- sketch: 6s (LLM call)

Adjust based on observed success rates.

## Error Handling

### Worker Errors

Workers should catch exceptions and return `Result(success=False, error=...)`:

```python
try:
    result = await dojo.run_tac(state, tactic)
except Exception as e:
    return Result(
        success=False,
        strategy=StrategyType.MICRO,
        error=str(e),
        time_seconds=elapsed,
    )
```

### Timeout Handling

Use `asyncio.wait_for`:

```python
try:
    result = await asyncio.wait_for(worker(goal), timeout=timeout)
except asyncio.TimeoutError:
    return Result(success=False, error="timeout")
```

### Graceful Shutdown

Scheduler handles SIGINT:

```python
try:
    await scheduler.process_queue(goal_queue)
except KeyboardInterrupt:
    scheduler.shutdown()
    await scheduler_task
```

All tasks cancelled cooperatively.

## Testing

### Unit Tests

```python
import pytest
from orchestrator.scheduler import Scheduler, Goal

@pytest.mark.asyncio
async def test_scheduler_ucb():
    scheduler = Scheduler()
    # Test UCB score calculation
    assert scheduler.ucb_score(StrategyType.MICRO) > 0

@pytest.mark.asyncio
async def test_goal_processing():
    scheduler = Scheduler()
    goal = Goal(id="test", text="test", estimated_difficulty=0.3)
    result = await scheduler.run_goal(goal)
    assert result is not None
```

### Integration Tests

```bash
# Test with stub workers
ORCH_PROFILE=0 python -m orchestrator.main bank --timeout 10

# Check results
ls bench/results/
cat bench/results/bank-*.json
```

### Load Tests

Monitor CPU during long runs:

```bash
# Terminal 1
ORCH_PROFILE=1 python -m orchestrator.main bg

# Terminal 2
watch -n 1 "ps aux | grep python | grep -v grep"
```

## Debugging

### Enable Verbose Logging

Add to workers:

```python
import logging
logging.basicConfig(level=logging.DEBUG)
logger = logging.getLogger(__name__)

async def run_micro(goal: Goal, timeout: float) -> Result:
    logger.debug(f"Running micro on {goal.id}")
    # ...
```

### Inspect Ledger

```bash
sqlite3 orchestrator/cache/ledger.db
```

```sql
-- Recent attempts
SELECT * FROM attempts ORDER BY timestamp DESC LIMIT 10;

-- Success rates by strategy
SELECT strategy,
       COUNT(*) as attempts,
       SUM(success) as successes,
       AVG(time_seconds) as avg_time
FROM attempts
GROUP BY strategy;

-- Cached tactics
SELECT * FROM tactic_cache ORDER BY use_count DESC LIMIT 10;
```

### Profile Performance

```python
import cProfile
import pstats

async def main():
    # ... orchestrator code ...

cProfile.run('asyncio.run(main())', 'stats.prof')
pstats.Stats('stats.prof').sort_stats('cumtime').print_stats(20)
```

## Next Steps

1. **LeanDojo integration**: Replace `workers/dojo.py` stub
2. **Goal extraction**: Scan `.lean` files for `sorry`
3. **Copilot setup**: Add to lakefile, implement `workers/copilot.py`
4. **Premise index**: Build FAISS index from mathlib
5. **ReProver models**: Download and wire into `workers/reprover.py`
6. **Blueprint sync**: Update blueprint from ledger status

## Resources

- [LeanDojo Docs](https://leandojo.readthedocs.io/)
- [Lean Copilot README](https://github.com/lean-dojo/LeanCopilot)
- [ReProver Paper](https://arxiv.org/abs/2306.15626)
- [UCB Bandits](https://en.wikipedia.org/wiki/Multi-armed_bandit#Upper_Confidence_Bound)
