# Getting Started with PCP-RPG

Quick start guide for working with the PCP theorem formalization planning infrastructure.

## What's Been Built

### ✅ Complete Infrastructure

1. **JSON Planning Graph** - Single source of truth
   - `website/data/pcp-graph.json` - 19 nodes, 6 work packages, full dependencies
   - `website/data/schema.json` - Validation schema

2. **Interactive Web Visualization**
   - D3.js force-directed graph
   - Click nodes for details, drag to reposition
   - Live progress statistics

3. **Blueprint LaTeX Generator**
   - Reads JSON, outputs traditional Massot-style blueprint
   - Includes `\lean{}`, `\leanok`, `\uses{}` markers
   - Generates both web.tex and print.tex

4. **Lean 4 Scaffolding**
   - 14 Lean files with complete module structure
   - All theorems/lemmas have type signatures
   - `sorry` placeholders ready for formalization
   - Proper imports and dependencies

## Commands

### View the Planning Graph

```bash
make graph
# Opens http://localhost:8000
```

### Regenerate Everything from JSON

```bash
# After editing website/data/pcp-graph.json:
make all-gen    # Regenerates both blueprint and Lean files
```

Or individually:

```bash
make blueprint  # Regenerate LaTeX only
make lean       # Regenerate Lean files only
```

### Build Lean Project (requires Lean 4)

```bash
make update     # Get mathlib cache
make build      # Build the project
```

### Build Blueprint PDF (requires LaTeX)

```bash
make pdf
```

## Typical Workflow

### 1. Planning Phase (current)

Edit the graph to refine the plan:

```bash
vim website/data/pcp-graph.json
# Edit: add nodes, update status, change difficulty, etc.

make all-gen
# Regenerates Lean files and blueprint

make graph
# View changes in browser
```

### 2. Formalization Phase (future)

Once you start formalizing:

```bash
# Edit a Lean file
vim PCP/Defs.lean
# Replace sorry with actual proof

# Build and test
make build

# Update status in JSON
# Change node status from "planned" to "proved"
vim website/data/pcp-graph.json

# Regenerate to update blueprint
make blueprint
```

### 3. Sync Status Back to JSON

After formalizing, you can:
1. Manually update status in `pcp-graph.json`
2. (Future) Run a script to auto-detect which theorems are complete
3. Regenerate blueprint to show green checkmarks

## File Organization

```
pcp-rpg/
├── website/
│   ├── data/
│   │   └── pcp-graph.json         ← EDIT THIS
│   ├── lib/
│   │   ├── generate_blueprint.py  ← Reads JSON → LaTeX
│   │   └── generate_lean.py       ← Reads JSON → Lean
│   └── static/                    ← Web visualization
│
├── blueprint/
│   └── src/
│       └── content.tex            ← Auto-generated (don't edit)
│
├── PCP/
│   ├── Defs.lean                  ← Auto-generated (edit for proofs)
│   ├── ConstraintGraph/
│   ├── Expander/
│   └── ...                        ← All auto-generated
│
├── PCP.lean                       ← Root module (maintained)
├── lakefile.toml                  ← Lean project config
└── Makefile                       ← Convenience commands
```

## The JSON-First Principle

**Always edit the JSON, never the generated files directly.**

The flow is:

```
Edit JSON → Regenerate → View/Build
```

Why?
- JSON is the single source of truth
- AI agents can edit structured JSON
- Easy to validate and version control
- Can generate multiple outputs (web, PDF, Lean)

## Adding a New Node

1. Edit `website/data/pcp-graph.json`:

```json
{
  "id": "expander.zig_zag",
  "kind": "lemma",
  "name": "Zig-Zag Product",
  "status": "planned",
  "path": "PCP/Expander/ZigZag.lean",
  "signature": "def zigZag (G H : Graph) : Graph := ...",
  "description": "Zig-zag product construction",
  "difficulty": 4,
  "workPackage": "WP-B",
  "estimatedLOC": 200
}
```

2. Add dependencies in `edges`:

```json
{
  "from": "expander.defs",
  "to": "expander.zig_zag",
  "type": "depends"
}
```

3. Regenerate:

```bash
make all-gen
```

4. The new file `PCP/Expander/ZigZag.lean` is created automatically!

## Next Steps

### Install Lean 4 (optional for now)

```bash
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
cd ~/repos/pcp-rpg
lake update
lake exe cache get
lake build
```

### Refine the Plan

- Add more intermediate lemmas
- Break down 5-star theorems
- Add missing mathlib dependencies
- Adjust difficulty ratings

### Start Formalizing

Pick an easy node (1-2 stars) and replace `sorry` with actual proof.

### Set Up Automation (future)

- Configure LeanDojo/Copilot
- Set up GitHub Actions
- Build the orchestrator from `docs/engine.md`

## Help

- See `CLAUDE.md` for detailed architecture
- See `docs/proof.md` for PCP theorem details
- Check the website: http://localhost:8000 (after `make graph`)

## Current Status

| Component | Status |
|-----------|--------|
| Planning graph (JSON) | ✅ Complete (19 nodes) |
| Web visualization | ✅ Working |
| Blueprint generator | ✅ Working |
| Lean scaffolding | ✅ Generated (14 files) |
| Lean building | ⏸️ Needs Lean 4 installed |
| Formalization | 🔲 Not started (all `sorry`) |
| Automation | 🔲 Not started |

**Ready to start formalization!**