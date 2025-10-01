# Multi-Environment Setup Guide

The orchestrator uses **two Python environments** to handle version compatibility:

## Overview

| Environment | Python Version | Purpose | LeanDojo Support |
|-------------|---------------|---------|------------------|
| `.venv` | 3.13 | General orchestrator commands | ❌ No |
| `.venv-lean` | 3.12 | LeanDojo integration | ✅ Yes |

**Why two environments?**
- LeanDojo requires Python 3.9-3.12
- Your system has Python 3.13.5
- We maintain both for maximum compatibility

## Quick Start

### Setup Both Environments

```bash
# Install general orchestrator (Python 3.13)
make orch-init

# Install LeanDojo environment (Python 3.12)
make orch-lean-init
```

### Using Wrapper Scripts (Recommended)

The easiest way to use the orchestrator:

```bash
# General commands (uses Python 3.13, no LeanDojo)
bin/orch bank --timeout 30
bin/orch stats
bin/orch dashboard

# LeanDojo commands (uses Python 3.12, full features)
bin/orch-lean bank --timeout 30
bin/orch-lean bg
```

### Test LeanDojo

```bash
make orch-test
```

Expected output:
```
✓ LeanDojo imported successfully
✓ DojoWrapper initialized
✓ LeanDojo integration is ready!
```

## Environment Details

### Environment 1: General (.venv)
- **Python**: 3.13.5
- **Path**: `.venv/`
- **Dependencies**:
  - typer (CLI)
  - fastapi + uvicorn (dashboard)
  - psutil (CPU monitoring)
  - pytest (testing)
- **Use for**:
  - Running benchmarks with stub workers
  - Dashboard
  - Statistics
  - General orchestration

### Environment 2: LeanDojo (.venv-lean)
- **Python**: 3.12.11
- **Path**: `.venv-lean/`
- **Dependencies**:
  - lean-dojo (Lean integration)
  - ray (distributed computing)
  - All general deps
- **Use for**:
  - Real Lean proof search
  - LeanDojo operations
  - Full-featured orchestration

## Wrapper Scripts

### `bin/orch`
```bash
#!/usr/bin/env bash
# Uses .venv (Python 3.13)
# General orchestrator without LeanDojo
```

**Usage:**
```bash
bin/orch bank           # Run benchmarks
bin/orch stats          # View statistics
bin/orch dashboard      # Launch dashboard
```

### `bin/orch-lean`
```bash
#!/usr/bin/env bash
# Uses .venv-lean (Python 3.12)
# Full orchestrator with LeanDojo support
```

**Usage:**
```bash
bin/orch-lean bank      # Run benchmarks with real Lean
bin/orch-lean bg        # Background proof search
```

### `bin/orch-test-dojo`
```bash
#!/usr/bin/env bash
# Tests LeanDojo integration
```

**Usage:**
```bash
make orch-test
# or
bin/orch-test-dojo
```

## Makefile Commands

### Setup
```bash
make orch-init          # Install Python 3.13 environment
make orch-lean-init     # Install Python 3.12 environment
```

### Run
```bash
make orch-bank          # Run benchmark (uses bin/orch)
make orch-stats         # Show stats (uses bin/orch)
make orch-dashboard     # Launch dashboard (uses bin/orch)
make orch-test          # Test LeanDojo (uses bin/orch-test-dojo)
```

## Manual Activation

If you prefer manual activation:

### General Environment
```bash
source .venv/bin/activate
python -m orchestrator.main --help
```

### LeanDojo Environment
```bash
source .venv-lean/bin/activate
export GITHUB_ACCESS_TOKEN=$(gh auth token)
python -m orchestrator.main --help
```

## Environment Variables

### Required for LeanDojo
```bash
# GitHub token (required by LeanDojo for repo access)
export GITHUB_ACCESS_TOKEN=$(gh auth token)

# Or set manually
export GITHUB_ACCESS_TOKEN=ghp_your_token_here
```

### Optional Configuration
```bash
export ORCH_PROFILE=0              # 0=micro, 1=+copilot, 2=+reprover
export ORCH_CPU_TARGET=0.5         # Target 50% CPU
export LEANDOJO_NUM_PROCS=4        # LeanDojo parallel processes
```

## File Structure

```
.
├── .venv/                  # Python 3.13 environment
│   └── bin/python3.13
├── .venv-lean/             # Python 3.12 environment
│   └── bin/python3.12
├── bin/
│   ├── orch                # General wrapper (→ .venv)
│   ├── orch-lean           # LeanDojo wrapper (→ .venv-lean)
│   └── orch-test-dojo      # Test script
└── orchestrator/
    ├── requirements.txt    # Core deps (both envs)
    └── workers/
        └── dojo.py         # LeanDojo wrapper
```

## Troubleshooting

### Python 3.12 Not Found
```bash
brew install python@3.12
make orch-lean-init
```

### LeanDojo Import Error
```bash
source .venv-lean/bin/activate
pip install lean-dojo
```

### GitHub Token Not Set
```bash
# Check if token is available
gh auth token

# Set it
export GITHUB_ACCESS_TOKEN=$(gh auth token)

# Add to shell profile
echo 'export GITHUB_ACCESS_TOKEN=$(gh auth token)' >> ~/.zshrc
```

### Wrong Environment Active
```bash
# Check current Python version
python --version

# Deactivate current env
deactivate

# Activate correct one
source .venv-lean/bin/activate  # For LeanDojo
# or
source .venv/bin/activate       # For general
```

## Best Practices

### Daily Workflow

1. **For general work** (benchmarks, dashboard, stats):
   ```bash
   bin/orch bank
   bin/orch dashboard
   ```

2. **For Lean integration** (real proof search):
   ```bash
   bin/orch-lean bg
   bin/orch-lean bank --timeout 60
   ```

3. **For development**:
   ```bash
   # Activate the environment you're working in
   source .venv-lean/bin/activate

   # Run tests
   pytest orchestrator/
   ```

### Adding New Dependencies

**General dependencies** (both environments):
```bash
# Add to orchestrator/requirements.txt
# Then:
source .venv/bin/activate && pip install <package>
source .venv-lean/bin/activate && pip install <package>
```

**LeanDojo-specific**:
```bash
source .venv-lean/bin/activate
pip install <package>
```

### Version Pinning

Both environments should use the same versions for shared packages:
- typer
- fastapi
- uvicorn
- psutil
- pytest

Only `.venv-lean` has:
- lean-dojo
- ray

## Migration Path

When LeanDojo supports Python 3.13:

1. Remove `.venv-lean`
2. Install lean-dojo in `.venv`
3. Update `bin/orch` to include LeanDojo
4. Remove `bin/orch-lean`

For now, the multi-env setup provides full compatibility.

## Testing

### Test General Environment
```bash
source .venv/bin/activate
python -m orchestrator.main bank --timeout 10
```

### Test LeanDojo Environment
```bash
make orch-test
# Should show: ✓ LeanDojo integration is ready!
```

### Run Full Suite
```bash
# With stubs (Python 3.13)
bin/orch bank --timeout 30

# With LeanDojo (Python 3.12)
bin/orch-lean bank --timeout 30
```

## Summary

✅ **Two environments** for version compatibility
✅ **Wrapper scripts** for easy switching
✅ **Make commands** for common tasks
✅ **LeanDojo works** in Python 3.12 environment
✅ **General orchestrator works** in Python 3.13 environment

Use `bin/orch` for general work, `bin/orch-lean` for Lean integration!
