# LeanCopilot + Orchestrator Integration

## Overview

The orchestrator now has **full LeanCopilot support** through the `copilot.py` worker. This enables AI-assisted proof search using the same models that power the LeanCopilot VSCode extension.

## Architecture

```
┌─────────────────────────────────────────────────────────────┐
│                     Orchestrator                             │
│  ┌──────────────┐  ┌──────────────┐  ┌──────────────┐     │
│  │ Micro Worker │  │Copilot Worker│  │ReProver Worker│     │
│  │   (fast)     │  │  (AI-based)  │  │   (heavy)    │     │
│  └──────────────┘  └──────────────┘  └──────────────┘     │
│         │                  │                   │            │
│         └──────────────────┼───────────────────┘            │
│                            │                                │
└────────────────────────────┼────────────────────────────────┘
                             │
                    ┌────────▼────────┐
                    │   LeanDojo      │
                    │   (verifier)    │
                    └────────┬────────┘
                             │
                    ┌────────▼────────┐
                    │  LeanCopilot    │
                    │  (tactics in    │
                    │   Lean runtime) │
                    └────────┬────────┘
                             │
              ┌──────────────┴───────────────┐
              │                              │
      ┌───────▼──────┐              ┌───────▼──────┐
      │ CTranslate2  │              │   Models     │
      │  (C++ infer) │              │ (~/.cache)   │
      └──────────────┘              └──────────────┘
```

## How It Works

### 1. Copilot Worker (`orchestrator/workers/copilot.py`)

The copilot worker uses **LeanDojo to invoke LeanCopilot tactics** running in the actual Lean environment:

```python
# Step 1: Select relevant premises from mathlib
premises_result = dojo.run_tac(
    state=initial_state,
    tactic="select_premises (num := 12)",
)

# Step 2: Run AI-powered proof search
search_result = dojo.run_tac(
    state=premises_result.state,
    tactic="search_proof (beam := 4) (temperature := 0.2) (maxSteps := 20)",
)
```

This is **much better** than calling external LLM APIs because:
- ✅ Models run **locally** (no API costs)
- ✅ Uses **CTranslate2** (optimized C++ inference, very fast)
- ✅ Tactics execute **in Lean** (guaranteed type-safe)
- ✅ Has **premise selection** (retrieves relevant mathlib lemmas)

### 2. Available Tactics

LeanCopilot provides three main tactics (all accessible through the orchestrator):

| Tactic | Description | Speed | Use Case |
|--------|-------------|-------|----------|
| `suggest_tactics` | Generate single tactic suggestions | Fast | Interactive development |
| `select_premises` | Retrieve relevant mathlib lemmas | Fast | Premise selection |
| `search_proof` | Multi-step proof search with Aesop | Medium | Automated proving |

### 3. Orchestrator Integration

The scheduler automatically routes goals to appropriate workers based on **profile level**:

- **Profile 0**: Micro tactics only (rfl, simp, omega, aesop)
- **Profile 1**: Micro + **LeanCopilot** 🎯 ← YOU ARE HERE
- **Profile 2**: Micro + LeanCopilot + ReProver (heavy)

Set via environment variable:
```bash
export ORCH_PROFILE=1  # Enable LeanCopilot
```

## Current Status

### ✅ What's Working

1. **LeanCopilot installed** and functional (verified with [PCP/Test/Copilot.lean](PCP/Test/Copilot.lean))
2. **Models downloaded** (~2.5GB) to `~/.cache/lean_copilot/models/`
3. **Pre-built binaries** for arm64-macOS extracted and working
4. **Orchestrator worker** implemented and registered
5. **VSCode integration** ready (use LeanCopilot tactics interactively)

### 🚧 Limitations

1. **LeanDojo initialization**: Theorems must have valid (non-`sorry`) bodies for LeanDojo to trace them
   - **Workaround**: Use LeanCopilot directly in VSCode for initial proof discovery
   - **Future**: Implement direct tactic invocation without LeanDojo tracing

2. **Library path**: Need `DYLD_LIBRARY_PATH` set for command-line builds
   ```bash
   export DYLD_LIBRARY_PATH=.lake/packages/LeanCopilot/.lake/build/lib:$DYLD_LIBRARY_PATH
   ```

3. **Profile requirement**: Must set `ORCH_PROFILE=1` or higher to enable

## Recommended Workflow

### Interactive Development (VSCode)

1. Import LeanCopilot in your `.lean` file:
   ```lean
   import LeanCopilot
   ```

2. Use tactics interactively:
   ```lean
   theorem my_theorem : ... := by
     suggest_tactics  -- Get suggestions
     search_proof     -- Or let AI search
   ```

3. Click suggested tactics to insert them

### Batch Processing (Orchestrator)

1. **Discover initial proofs** in VSCode using LeanCopilot
2. **Add proven theorems** to the lemma bank
3. **Run orchestrator** to verify and optimize:
   ```bash
   export ORCH_PROFILE=1
   python -m orchestrator.cli.run_bank
   ```

4. Orchestrator will:
   - Try micro tactics first (fast)
   - Fall back to LeanCopilot for harder goals
   - Cache successful proofs
   - Report statistics

### Best Practices

1. **Start simple**: Use micro tactics first, then LeanCopilot
2. **Cache everything**: Orchestrator caches all successful proofs
3. **Iterate**: Let LeanCopilot suggest, then simplify/polish manually
4. **Monitor**: Check dashboard for strategy success rates

## Configuration

### Environment Variables

```bash
# Profile level (0=micro, 1=+copilot, 2=+reprover)
export ORCH_PROFILE=1

# Library path for command-line builds
export DYLD_LIBRARY_PATH=.lake/packages/LeanCopilot/.lake/build/lib:$DYLD_LIBRARY_PATH

# Optional: Model cache location
export LEAN_COPILOT_CACHE_DIR=~/.cache/lean_copilot/models
```

### lakefile.toml

Already configured:
```toml
[[require]]
name = "LeanCopilot"
git = "https://github.com/lean-dojo/LeanCopilot.git"
rev = "v4.23.0"

[[lean_lib]]
name = "PCP"
moreLinkArgs = ["-L./.lake/packages/LeanCopilot/.lake/build/lib", "-lctranslate2"]
```

## Performance Expectations

Based on LeanCopilot paper benchmarks:

- **Tactic suggestion**: ~100-500ms per suggestion
- **Premise selection**: ~200-800ms (depends on db size)
- **Proof search**: 5-30s (depends on beam width & max steps)

Our configuration:
- Beam width: 4 (balanced)
- Temperature: 0.2 (focused)
- Max steps: 20 (prevents runaway)
- Premises: 12 (top-k from retrieval)

## Troubleshooting

### "Library not loaded: libctranslate2.dylib"
```bash
export DYLD_LIBRARY_PATH=.lake/packages/LeanCopilot/.lake/build/lib:$DYLD_LIBRARY_PATH
```

### "Models not found"
```bash
ls ~/.cache/lean_copilot/models/huggingface.co/kaiyuy/
# Should show 4 directories with models
```

### "Copilot search exhausted"
This is normal - the tactic couldn't find a proof within the timeout. Try:
- Increasing timeout
- Simplifying the goal
- Adding more context/premises
- Using it interactively in VSCode to see intermediate states

## Next Steps

1. **Test on PCP theorems**: Use LeanCopilot to prove lemmas in `PCP/ConstraintGraph/Defs.lean`
2. **Build lemma bank**: Collect successful proofs for reuse
3. **Optimize search params**: Tune beam width/temperature for your domain
4. **Monitor success rates**: Track which strategies work best

## References

- [LeanCopilot Setup Guide](LEANCOPILOT_SETUP.md)
- [LeanCopilot Paper](https://arxiv.org/abs/2404.12534)
- [LeanDojo Integration Docs](orchestrator/LEANDOJO_INTEGRATION.md)
- [Orchestrator Quick Reference](orchestrator/QUICK_REFERENCE.md)
