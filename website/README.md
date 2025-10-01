# PCP Theorem - Interactive Planning Website

Static website visualizing the Repository Planning Graph (RPG) for formalizing the PCP theorem in Lean 4.

## Structure

```
website/
├── data/
│   ├── schema.json       # JSON Schema for the RPG graph
│   └── pcp-graph.json    # The actual dependency graph data
├── lib/                  # (future) Shared graph logic modules
├── static/
│   ├── index.html        # Main visualization page
│   └── graph.js          # D3.js visualization code
└── README.md
```

## Quick Start

### Option 1: Python HTTP Server

```bash
cd website/static
python3 -m http.server 8000
```

Then open: http://localhost:8000

### Option 2: npx serve

```bash
cd website
npx serve static
```

### Option 3: Any Static Server

Just serve the `static/` directory.

## Features

### Interactive Dependency Graph
- **Nodes**: Color-coded by status (planned → stated → proved → tested)
- **Edges**: Show dependencies between components
- **Click nodes**: View detailed information in sidebar
- **Drag nodes**: Reposition graph layout
- **Zoom/Pan**: Navigate large graphs

### Node Information
Each node includes:
- Status and type
- Lean file path
- Type signature
- Difficulty rating (1-5 stars)
- Estimated LOC
- Work package assignment
- Paper references
- Implementation notes

### Progress Tracking
Live stats panel showing:
- Total nodes, theorems, modules
- Estimated total LOC
- Completion percentage

## Data Format

The graph is defined in `data/pcp-graph.json` following the schema in `data/schema.json`.

### Node Types
- **module**: Lean module/file
- **theorem**: Major theorem
- **lemma**: Helper lemma
- **definition**: Core definition
- **axiom**: Axiomatized component

### Node Status
- **planned**: Not yet started
- **stated**: Type signature written
- **proved**: Proof completed
- **tested**: Verified and tested
- **blocked**: Waiting on dependencies

### Edge Types
- **depends**: Logical dependency
- **imports**: Module import
- **uses**: Uses definition/lemma
- **refines**: Strengthens statement
- **implements**: Implements interface

## Editing the Graph

To add/modify nodes:

1. Edit `data/pcp-graph.json`
2. Validate against schema (optional):
   ```bash
   npx ajv-cli validate -s data/schema.json -d data/pcp-graph.json
   ```
3. Regenerate derived artifacts:
   ```bash
   # Regenerate blueprint LaTeX
   python3 lib/generate_blueprint.py

   # Copy to static site (if you moved it)
   cp data/pcp-graph.json static/
   ```
4. Refresh the browser

## Migration Path to Dynamic Site

Current: Static HTML + D3.js + JSON file

Future (Option B):
- Keep `data/` and schema unchanged
- Extract graph logic to `lib/` as reusable modules
- Replace static HTML with React/Svelte components
- Add API layer or SQLite backend
- Wire to live orchestrator

The data format and graph algorithms remain the same.

## Dependencies

- D3.js v7 (loaded from CDN)
- Modern browser with ES6+ support

No build step required for static version.