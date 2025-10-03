# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Project Overview

This repository contains planning documents and research for formalizing the classical PCP (Probabilistically Checkable Proofs) theorem in Lean 4 using automated and collaborative approaches inspired by:
- The RPG (Repository Planning Graph) methodology from the ZeroRepo paper
- Large-scale collaborative Lean 4 projects (Liquid Tensor Experiment, sphere eversion)
- AI-assisted proof development tools (LeanDojo, ReProver, Lean Copilot)

**Goal**: Formalize `NP = PCP(log n, 1)` in Lean 4 with mathlib4, using blueprint infrastructure and heavy automation.

## Repository Structure

This is a Lean 4 formalization project with planning documents and interactive visualization:

- `PCP/` - Lean 4 source files for PCP theorem formalization
- `PCP.lean` - Root module file
- `lakefile.toml` - Lake build configuration
- `lean-toolchain` - Pinned Lean 4 version (synced with mathlib4)
- `docs/` - Planning documents and research
  - `readme-first.txt` - High-level project goals and experimental approach
  - `rpg.md` - Detailed ChatGPT conversation about the RPG methodology
  - `engine.md` - Comprehensive development system design
  - `proof.md` - Detailed formalization plan for the PCP theorem
  - `lit-review.md` - Survey of relevant projects, tools, and prior work
- `website/` - Interactive RPG graph visualization (static site with D3.js)
  - `data/pcp-graph.json` - Complete dependency graph
  - `data/schema.json` - JSON Schema for the graph
  - `static/` - HTML + JavaScript visualization

## Key Concepts

### RPG (Repository Planning Graph)
A structured approach to large-scale code/proof generation where:
1. Plans are persisted as dependency graphs (not prose)
2. Nodes carry functional semantics and implementation anchors
3. Edges encode data flows and dependency ordering
4. Generation follows topological order with TDD
5. Graph-guided localization for edits prevents drift

### Blueprint Infrastructure
From Patrick Massot's sphere eversion project:
- LaTeX + Lean hybrid documentation
- Dependency graphs with visual status tracking
- Public progress monitoring
- Enables crowd-sourced formalization at scale

### Automation Strategy
- Continuous background proof search using local compute (~50% CPU)
- Parallel exploration with multiple strategies (Copilot, ReProver, micro-tactics)
- Scheduler that allocates resources based on goal difficulty
- Lemma marketplace for managing helper lemma requests
- GitHub Actions for CI/CD and heavy compute dispatch

## Formalization Approach

### Chosen Proof Strategy
**Dinur's gap amplification** via constraint graphs:
- Most formalization-friendly (combinatorial, modular)
- Avoids heavy algebraic machinery
- Clean dependency structure
- Well-documented in literature

### Module Structure (Planned)
```
PCP/
├─ Defs.lean              # PCP classes, verifiers
├─ Language.lean          # Encodings, bitstrings
├─ ConstraintGraph/
│  ├─ Defs.lean          # Binary CSP, UNSAT
│  ├─ Preprocess.lean    # Expanderization
│  └─ Powering.lean      # Graph powering
├─ AssignmentTester/
│  ├─ Defs.lean          # Assignment testers
│  └─ Existence.lean     # Explicit tester construction
├─ Amplification/Main.lean
├─ Equivalences.lean      # Gap-CSP ↔ PCP
└─ Endgame.lean          # NP = PCP(log n, 1)
```

### Missing Dependencies (to formalize)
1. **Expander graphs** - explicit families, spectral bounds
2. **Spectral graph theory** - Rayleigh quotient, mixing lemmas
3. **Random walks** - finite Markov chains, bias bounds
4. **Coding theory** - linear codes with constant distance
5. **NP-completeness infrastructure** - if not in mathlib4

## Commands

### View the Planning Website

```bash
cd website/static
python3 -m http.server 8000
# Open http://localhost:8000
```

The website shows:
- Interactive dependency graph with D3.js force layout
- Node details (status, difficulty, signatures, references)
- Progress statistics
- Work package assignments

### Validate Graph Data

```bash
cd website
npx ajv-cli validate -s data/schema.json -d data/pcp-graph.json
```

## Development Workflow

### Current State

The Lean 4 project is now initialized with mathlib4 dependency. You can:

1. **Build the project**: `lake build`
2. **Update mathlib4**: `lake update && lake exe cache get`
3. **Add new Lean files**: Create files under `PCP/` directory
4. **Import mathlib**: Use `import Mathlib.Path.To.Module` in your files

**Note on `lake` commands**: If `lake` is not in your PATH or you encounter command-not-found errors, use the full path: `~/.elan/bin/lake build`, `~/.elan/bin/lake update`, etc. This is especially common in non-interactive shells or CI environments where elan's PATH modifications aren't applied.

### Planned Development Workflow

For future automation:

1. **Background proof search**: Run scheduler with ~50% CPU target
2. **Dashboard**: Monitor progress, strategy success rates, cache hits
3. **PRs**: Auto-generated branches for completed lemmas with metrics
4. **Blueprint**: Keep LaTeX blueprint in sync with code progress

### Planning Documents

The `docs/` directory contains:
- Detailed technical specifications
- Concrete type signatures for major theorems
- Work package breakdowns with difficulty ratings
- Tool recommendations and integration patterns
- Cost-benefit analyses of different approaches

## Key Recommendations from Research

1. **Use Lean 4 + mathlib** - best tooling and community support
2. **Adopt blueprint + bors + CI cache** - proven at scale (LTE, PFR)
3. **AI as copilot, not principal** - LeanDojo/Copilot for suggestions only
4. **Stage the work**: foundations → primitives → amplification → endgame
5. **Public progress tracking** - dependency graphs recruit contributors
6. **Consider Isabelle side-modules** - mature expander/NP-completeness libraries

## Important Context

- This is **not a video game** despite file names - "rpg" = Repository Planning Graph
- The project aims for **massive parallelism** with GitHub Actions and minimal human effort
- Target: Something like Patrick Massot's sphere eversion blueprint + complete proof
- Experimental focus: Figure out what works well for Claude agents at scale
- Lean 4 project is initialized with mathlib4; ready for formalization work

## Project Status

✅ **Completed:**
1. Repo scaffold (lakefile, toolchain) with mathlib4 dependency
2. Planning documents with detailed technical specifications

🔲 **Next Steps:**
1. Set up orchestrator (Python) with scheduler + workers + cache
2. Create toy lemma bank for testing strategies
3. Implement profile system (0=micro only, 1=+Copilot, 2=+ReProver)
4. Wire GitHub Actions for CI, docs, and heavy job dispatch
5. Build dashboard for progress monitoring
6. Start on actual PCP formalization following `docs/proof.md`

## Citation Key

When these docs reference papers:
- **Dinur** = "The PCP theorem by gap amplification" (main technical reference)
- **ZeroRepo/RPG** = arXiv:2509.16198v2 (RPG methodology)
- **Arora-Barak** = Computational Complexity textbook (PCP background)
- make git commits for lean files after completing proofs or adding new theorems