# PCP Theorem Blueprint

LaTeX blueprint following the Massot/LTE style, auto-generated from the JSON graph.

## Structure

```
blueprint/
├── src/
│   ├── content.tex       # Auto-generated from ../website/data/pcp-graph.json
│   ├── web.tex          # Web version template
│   └── print.tex        # PDF version template
├── lean_decls/          # (future) Auto-extracted Lean declarations
└── README.md
```

## Generation Workflow

**Source of truth:** `website/data/pcp-graph.json`

To regenerate the blueprint LaTeX:

```bash
cd website
python3 lib/generate_blueprint.py
```

This reads the JSON graph and generates:
- Chapter structure based on work packages
- Proper `\lean{}`, `\leanok`, `\uses{}` markers
- Lean code signatures in lstlisting blocks
- References to papers
- Difficulty ratings and metadata

## Building the Blueprint

### Option 1: Manual LaTeX Build

```bash
cd blueprint/src
pdflatex print.tex
pdflatex print.tex  # Run twice for references
```

Produces `print.pdf` with full blueprint.

### Option 2: leanblueprint Tool

Once you have `leanblueprint` installed:

```bash
cd blueprint
leanblueprint web    # Generate web version with dep graph
leanblueprint pdf    # Generate PDF
```

The web version includes:
- Interactive dependency graph
- Hyperlinked references
- Status colors (planned/stated/proved)
- Integration with doc-gen4

### Option 3: CI Build

Add to `.github/workflows/docs.yml`:

```yaml
- name: Build blueprint
  run: |
    pip install leanblueprint
    cd blueprint
    leanblueprint web
    # Copy to gh-pages
```

## Blueprint Conventions

### Status Markers

- No marker = planned
- `\leanok` = formalized and compiles
- `\lean{Module.Name}` = links to Lean declaration

### Dependencies

```latex
\uses{constraint_graph-defs, expander-cheeger}
```

Auto-extracted from JSON edges with `type: "depends"` or `type: "uses"`.

### Code Signatures

```latex
\begin{lstlisting}[language=Lean]
theorem powering_soundness : ∃ β₂>0, UNSAT(G^t) ≥ β₂ * √t * min (UNSAT(G)) (1/t)
\end{lstlisting}
```

From `node.signature` in JSON.

## Editing Workflow

1. **Don't edit `content.tex` directly** - it's auto-generated
2. Edit `website/data/pcp-graph.json` instead:
   - Add/modify nodes
   - Update status, signatures, descriptions
   - Change dependencies (edges)
3. Run `python3 website/lib/generate_blueprint.py`
4. Rebuild PDF or web version

## Benefits of JSON-First Approach

- **Single source of truth**: JSON drives both web visualization and blueprint
- **AI-friendly**: Agents can edit structured JSON
- **Programmatic**: Can validate, analyze, auto-generate
- **Version control**: Clean diffs on JSON changes
- **Flexible**: Can generate other outputs (Lean scaffolding, etc.)

## Syncing with Lean Code

Once Lean files exist, we can:

1. **Extract declarations**: Use `lake build` + doc-gen4 to populate `lean_decls/`
2. **Auto-mark status**: Parse Lean files to detect which theorems are `sorry`-free
3. **Update JSON**: Write script to sync Lean file status back to `pcp-graph.json`
4. **Regenerate**: Blueprint stays current with actual code

## Installing leanblueprint

```bash
pip install leanblueprint
```

Or use it in CI without local install.

## Example Output

See `print.tex` and `web.tex` for full templates. The generated `content.tex` includes:

- 6 chapters (one per work package)
- 19 nodes (definitions, theorems, lemmas, modules)
- Full dependency tracking
- Paper references
- Difficulty ratings and LOC estimates