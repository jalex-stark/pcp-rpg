# PCP Theorem Formalization Project

Formalization of the classical PCP (Probabilistically Checkable Proofs) theorem `NP = PCP(log n, 1)` in Lean 4, using the Repository Planning Graph (RPG) methodology and blueprint infrastructure.

## Project Status

**Orchestrator complete, ready for testing!**

✅ **Working Now:**
- Complete proof search orchestrator (UCB1 + CPU throttling)
- Stub workers achieving 60%+ solve rate on benchmarks
- Multi-environment setup (Python 3.13 + 3.12 for LeanDojo)
- Test theorem suite in PCP/Basic.lean

⏳ **In Progress:**
- LeanDojo build (one-time, ~15min for mathlib cache)

🔲 **Next Steps:**
- Goal extraction from Lean files
- Lean Copilot integration
- Blueprint progress tracking

**Quick Test:** `make orch-init && bin/orch bank --timeout 10`

📖 **New Documentation:**
- **[QUICK_START.md](QUICK_START.md)** - 30-second test
- **[TESTING_INSTRUCTIONS.md](TESTING_INSTRUCTIONS.md)** - Full testing guide
- **[HANDOFF_SUMMARY.md](HANDOFF_SUMMARY.md)** - Complete handoff docs

## Repository Structure

```
pcp-rpg/
├── website/              # Interactive planning website (RPG visualization)
│   ├── data/            # Graph schema and data
│   ├── static/          # Static HTML/JS site
│   └── README.md
├── CLAUDE.md            # Guidance for Claude Code
├── readme-first.txt     # Project goals and approach
├── rpg.md              # RPG methodology research
├── engine.md           # Automation system design
├── proof.md            # PCP formalization plan
└── lit-review.md       # Survey of prior work
```

## Quick Start

### 1. View the Interactive Planning Graph

```bash
cd website/static
python3 -m http.server 8000
```

Open http://localhost:8000 to see the interactive dependency graph with D3.js visualization.

### 2. Generate Blueprint LaTeX

```bash
cd website
python3 lib/generate_blueprint.py
```

This reads `data/pcp-graph.json` and generates `blueprint/src/content.tex`.

### 3. Build Blueprint PDF (optional, requires LaTeX)

```bash
cd blueprint
make pdf
# Or: cd blueprint/src && pdflatex print.tex
```

Produces a traditional blueprint document with dependency tracking.

### 4. Read the Research

- **`readme-first.txt`** - Start here for project overview
- **`proof.md`** - Detailed PCP formalization plan with Lean signatures
- **`engine.md`** - Automated proof development system design
- **`rpg.md`** - RPG methodology for large-scale code generation
- **`lit-review.md`** - Survey of relevant projects and tools

## Architecture: JSON-First Blueprint (Hybrid Approach)

We use **Option B** from the research: JSON as source of truth, generate both web visualization AND blueprint LaTeX.

```
Single Source of Truth
        ↓
website/data/pcp-graph.json
        ↓
        ├──→ website/static/        (D3.js interactive graph)
        └──→ blueprint/src/          (LaTeX with \lean{} markers)
                ↓
                └──→ PDF + Web Blueprint (via leanblueprint)
```

**Benefits:**
- One canonical source (JSON)
- AI-friendly structured data
- Can generate multiple views
- Easy to validate and version control
- Supports automated orchestration (RPG methodology)

**Edit workflow:**
1. Edit `website/data/pcp-graph.json` (add nodes, update status, change dependencies)
2. Run `python3 website/lib/generate_blueprint.py` to regenerate LaTeX
3. Rebuild website/PDF as needed

## Key Concepts

### Repository Planning Graph (RPG)
A methodology where:
- Plans are graphs, not prose
- Nodes = capabilities, modules, functions with typed interfaces
- Edges = dependencies and data flows
- Code generation follows topological order
- Graph-guided localization prevents drift

### Blueprint Infrastructure
From Patrick Massot's sphere eversion:
- LaTeX + Lean hybrid documentation
- Visual dependency graphs
- Status tracking (planned → stated → proved → tested)
- Enables large-scale collaborative formalization

### Proof Strategy
**Dinur's gap amplification** via constraint graphs:
1. Preprocessing (expanderization)
2. Graph powering (gap amplification)
3. Alphabet reduction (assignment testers)
4. Iteration to constant gap
5. Gap-CSP ⇔ PCP equivalence

## Planned Workflow

1. **Planning Phase** (current)
   - ✅ Design RPG schema
   - ✅ Create interactive graph visualization
   - ✅ Define work packages
   - 🔲 Generate Lean scaffolding

2. **Foundation Phase**
   - Build expander graph library
   - Formalize spectral graph theory primitives
   - Create probabilistic reasoning toolkit
   - NP-completeness infrastructure

3. **Implementation Phase**
   - Automated proof search (Copilot, ReProver, LeanDojo)
   - Parallel exploration with multiple strategies
   - Resource-aware scheduler (~50% CPU)
   - Lemma marketplace for managing subgoals

4. **Integration Phase**
   - GitHub Actions CI/CD
   - Blueprint generation
   - Progress dashboard
   - Documentation

## Goals

- **Scale**: Handle 100k+ LOC with automation
- **Parallelism**: Many agents working simultaneously
- **Quality**: GitHub Actions verify all PRs
- **Transparency**: Public blueprint with live progress
- **Reusability**: Clean libraries for expanders, codes, gap amplification

## Work Packages

- **WP-A**: Foundations (★–★★) - PCP/CSP definitions
- **WP-B**: Expanders (★★★–★★★★) - Spectral graph theory
- **WP-C**: Powering (★★★★★) - Core amplification (hardest)
- **WP-D**: Assignment Testers (★★★–★★★★) - Alphabet reduction
- **WP-E**: Amplification (★★★) - Integration
- **WP-F**: Endgame (★★) - Final theorem

## Tech Stack

### Current (Planning)
- HTML + D3.js for graph visualization
- JSON for graph data
- Static site (easy migration to dynamic later)

### Planned (Formalization)
- Lean 4 + mathlib4
- LeanDojo + Lean Copilot + ReProver
- Python orchestrator with scheduler
- GitHub Actions CI
- leanblueprint for documentation

## Contributing

Currently in planning phase. Once we start formalization:
1. Check the interactive graph for available tasks
2. Pick a node from your skill level
3. Follow the blueprint specifications
4. Submit PR with CI passing

## References

- **Dinur (2007)**: "The PCP theorem by gap amplification"
- **Arora-Barak**: Computational Complexity textbook
- **ZeroRepo paper**: arXiv:2509.16198v2 (RPG methodology)
- **LTE/Sphere Eversion**: Blueprint methodology examples

## License

TBD - research/planning phase