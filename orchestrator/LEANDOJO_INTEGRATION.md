# LeanDojo Integration Guide

The orchestrator now includes real LeanDojo integration for programmatic proof search!

## What's Integrated

✅ **DojoWrapper** ([orchestrator/workers/dojo.py](workers/dojo.py))
- Real LeanDojo integration (replaces stub)
- Async interface for running tactics
- Caching of Dojo instances per theorem
- Proof checking and validation
- Error handling for timeouts, crashes, etc.

## Installation

### Prerequisites

1. **elan** (Lean version manager):
   ```bash
   curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
   ```

2. **Git 2.25+**:
   ```bash
   git --version  # Should be >= 2.25
   ```

3. **Python 3.9-3.12**:
   ```bash
   python3 --version
   ```

4. **GitHub Access Token** (required by LeanDojo):
   ```bash
   # Create token at: https://github.com/settings/tokens
   export GITHUB_ACCESS_TOKEN=ghp_your_token_here

   # Add to your shell profile (.bashrc, .zshrc, etc.):
   echo 'export GITHUB_ACCESS_TOKEN=ghp_your_token_here' >> ~/.bashrc
   ```

### Install LeanDojo

```bash
source .venv/bin/activate
pip install -r orchestrator/requirements.txt
```

This will install `lean-dojo>=2.0.0` along with its dependencies.

## Usage

### Basic Example

```python
import asyncio
from orchestrator.workers.dojo import DojoWrapper

async def test_tactic():
    # Initialize wrapper for current repo
    dojo = DojoWrapper(repo_path=".", commit="HEAD")

    try:
        # Run a tactic on a theorem
        result = await dojo.run_tac(
            theorem_file="PCP.lean",
            theorem_name="my_theorem",
            state=0,  # 0 = initial state
            tactic="simp",
            tactic_timeout=10.0,
        )

        if result.success:
            if result.proof_finished:
                print("✓ Proof complete!")
            else:
                print(f"Goals remaining: {result.new_goals}")
        else:
            print(f"✗ Error: {result.error}")

    finally:
        dojo.close()

asyncio.run(test_tactic())
```

### DojoWrapper API

#### Initialization

```python
dojo = DojoWrapper(
    repo_path=".",         # Path to Lean repo (or URL)
    commit="HEAD",         # Git commit hash
    timeout=600,           # Overall timeout (seconds)
    num_procs=4,           # Parallel processes (optional)
)
```

#### Run Tactic

```python
result = await dojo.run_tac(
    theorem_file="PCP/Defs.lean",  # Relative to repo root
    theorem_name="my_lemma",       # Theorem/lemma name
    state=0,                       # TacticState or state_id
    tactic="simp [*]",             # Tactic to execute
    tactic_timeout=10.0,           # Timeout for this tactic
)
```

**Returns**: `DojoResult`
- `success: bool` - Whether tactic succeeded
- `proof_finished: bool` - Whether proof is complete
- `new_goals: list[str]` - Remaining goals (if any)
- `error: Optional[str]` - Error message (if failed)
- `tactic_state_id: Optional[int]` - State ID for continuation

#### Check Proof

```python
is_valid = await dojo.check_proof(
    theorem_file="PCP/Defs.lean",
    theorem_name="my_lemma",
    proof_script="""
        simp [*]
        aesop
    """,
    timeout=30.0,
)
```

**Returns**: `bool` - True if proof is valid

#### Cleanup

```python
dojo.close()  # Close all cached Dojo instances
```

Or use context manager pattern (future enhancement).

## Integration with Workers

### Micro Worker Example

To integrate with the micro worker ([orchestrator/workers/micro.py](workers/micro.py)):

```python
from orchestrator.workers.dojo import DojoWrapper, DojoResult

async def run_micro(goal: Goal, timeout: float = 8.0) -> Result:
    """Run micro-tactics on a goal using real LeanDojo."""

    dojo = DojoWrapper()
    try:
        # Extract theorem info from goal
        theorem_file = goal.metadata.get('file', 'PCP.lean')
        theorem_name = goal.metadata.get('theorem', goal.id)

        # Try quick tactics
        tactics_to_try = ["simp_all", "aesop?", "omega", "ring"]

        for tactic in tactics_to_try:
            result = await dojo.run_tac(
                theorem_file=theorem_file,
                theorem_name=theorem_name,
                state=0,
                tactic=tactic,
                tactic_timeout=timeout / len(tactics_to_try),
            )

            if result.success and result.proof_finished:
                return Result(
                    success=True,
                    strategy=StrategyType.MICRO,
                    tactics=[tactic],
                    time_seconds=elapsed,
                )

        return Result(success=False, strategy=StrategyType.MICRO)

    finally:
        dojo.close()
```

## Tracing Repositories

Before interacting with a theorem, LeanDojo needs to "trace" the repository:

```python
from lean_dojo import LeanGitRepo, trace

# Trace the repo (only needed once, cached afterward)
repo = LeanGitRepo(".", "HEAD")
trace(repo, dst_dir=".trace")
```

The `DojoWrapper` handles this automatically when you first interact with a theorem.

## Environment Variables

```bash
# GitHub token (required)
export GITHUB_ACCESS_TOKEN=ghp_...

# Optional: LeanDojo configuration
export LEANDOJO_NUM_PROCS=4
export LEANDOJO_CACHE_DIR=~/.cache/lean_dojo
```

## Error Handling

LeanDojo operations can fail in several ways. The `DojoWrapper` handles:

1. **DojoCrashError**: Lean process crashed
2. **DojoInitError**: Failed to initialize Dojo
3. **DojoTacticTimeoutError**: Tactic took too long
4. **LeanError**: Tactic returned an error
5. **ProofGivenUp**: Proof was abandoned
6. **asyncio.TimeoutError**: Python-level timeout

All errors are caught and returned as `DojoResult(success=False, error=...)`.

## Caching

The `DojoWrapper` caches Dojo instances per `(file, theorem)` pair:

- First access to a theorem: Creates new Dojo instance
- Subsequent accesses: Reuses cached instance
- Call `dojo.close()` to clean up all instances

This avoids repeatedly initializing the Lean server.

## Limitations

### Current Implementation

1. **State Tracking**: Only supports `state=0` (initial) or direct `TacticState` objects
   - Does not maintain state history by ID
   - For multi-tactic proofs, pass the returned `TacticState` to next call

2. **Goal Extraction**: Simple heuristic parsing of pretty-printed states
   - May not handle all Lean 4 formatting edge cases
   - Works for basic `⊢ goal` format

3. **Proof Splitting**: Basic splitting by newlines and semicolons
   - May not handle complex proof structures
   - Skips comments (`--`)

### Future Enhancements

- [ ] State history tracking (state ID → TacticState mapping)
- [ ] Better goal parser (use Lean LSP info instead of string parsing)
- [ ] Smarter proof script parser (handle indentation, begin/end blocks)
- [ ] Context manager support (`with DojoWrapper() as dojo:`)
- [ ] Batch tactic execution
- [ ] Premise extraction from proof states

## Testing

### Unit Test Example

```python
import pytest
import asyncio
from orchestrator.workers.dojo import DojoWrapper

@pytest.mark.asyncio
async def test_dojo_wrapper():
    """Test DojoWrapper with a simple proof."""
    dojo = DojoWrapper(".")

    try:
        # Assuming you have a test theorem in your repo
        result = await dojo.run_tac(
            theorem_file="PCP.lean",
            theorem_name="test_theorem",
            state=0,
            tactic="rfl",  # Reflexivity
        )

        assert result.success
        # May or may not finish depending on your test_theorem

    finally:
        dojo.close()
```

### Integration with Benchmark

The benchmark runner can now use real LeanDojo if:

1. Goals include `file` and `theorem` metadata
2. LeanDojo is installed
3. Repo has been traced

Update `bench/bank.jsonl`:

```json
{
  "id": "nat_add_zero",
  "goal": "∀ n : ℕ, n + 0 = n",
  "difficulty": 0.1,
  "metadata": {
    "file": "PCP/Tests.lean",
    "theorem": "nat_add_zero"
  }
}
```

## Debugging

### Enable Verbose Output

```python
import logging
logging.basicConfig(level=logging.DEBUG)
```

### Check LeanDojo Status

```python
from lean_dojo import __version__
print(f"LeanDojo version: {__version__}")
```

### Verify GitHub Token

```bash
curl -H "Authorization: token $GITHUB_ACCESS_TOKEN" https://api.github.com/user
```

Should return your GitHub user info.

### Inspect Cache

```bash
ls -la ~/.cache/lean_dojo/
```

## Next Steps

1. **Create test theorems** in your PCP formalization
2. **Update workers** to use real DojoWrapper
3. **Run benchmarks** with real Lean interaction
4. **Integrate with goal extraction** (scan for `sorry`/`admit`)
5. **Wire Lean Copilot** for advanced tactics

## References

- [LeanDojo Documentation](https://leandojo.readthedocs.io/)
- [LeanDojo GitHub](https://github.com/lean-dojo/LeanDojo)
- [DojoWrapper Implementation](workers/dojo.py)
- [Main Documentation](../docs/engine.md)
