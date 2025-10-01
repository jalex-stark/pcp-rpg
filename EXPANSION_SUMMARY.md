# Graph Expansion Summary

## Overview

Expanded the PCP theorem formalization graph from **19 nodes** to **45 nodes** (+26 new nodes, +31 new edges).

## New Total Statistics

| Metric | Value |
|--------|-------|
| **Total Nodes** | 45 |
| **Modules** | 5 |
| **Definitions** | 17 |
| **Lemmas** | 10 |
| **Theorems** | 13 |
| **Total Edges** | 56 |
| **Est. Total LOC** | ~7,350 |

## What Was Added

### 1. Spectral Graph Theory Infrastructure (4 nodes)

Essential for expander graphs and mixing bounds:

- **Adjacency Matrix** - `spectral.adjacency_matrix` (2⭐)
- **Graph Eigenvalues** - `spectral.eigenvalues` (3⭐)
- **Rayleigh Quotient** - `spectral.rayleigh_quotient` (2⭐)
- **Second Eigenvalue vs Expansion** - `spectral.second_eigenvalue_bound` (4⭐)
  - *One direction of Cheeger's inequality*

### 2. Random Walks & Mixing (3 nodes)

Critical for powering_soundness proof:

- **Random Walk Definition** - `random_walk.definition` (2⭐)
- **Spectral Mixing Lemma** - `random_walk.mixing` (4⭐)
  - *Random walk converges exponentially fast in spectral gap*
- **Path Sampling Concentration** - `random_walk.path_sampling` (4⭐)
  - *Uses Chernoff + independence*

### 3. Expander Constructions (2 nodes)

- **Edge Expansion** - `expander.edge_expansion_def` (2⭐)
- **Explicit Expander Family Exists** - `expander.explicit_family` (5⭐)
  - *HARD - zig-zag product or port from Isabelle AFP*

### 4. Preprocessing Breakdown (4 nodes)

Splits high-level `preprocess` into implementable pieces:

- **prep1 (Vertex Cloud Expansion)** - `preprocess.prep1` (3⭐)
- **prep1 Soundness** - `preprocess.prep1_soundness` (3⭐)
- **prep2 (Edge Addition)** - `preprocess.prep2` (3⭐)
- **Regularity** - `preprocess.regularity` (2⭐)

### 5. Coding Theory Infrastructure (4 nodes)

For assignment testers:

- **Linear Code** - `codes.linear_code` (2⭐)
- **Code Distance** - `codes.distance` (2⭐)
- **Good Codes Exist** - `codes.good_codes_exist` (3⭐)
  - *Gilbert-Varshamov or expander codes*
- **Hadamard Code** - `codes.hadamard` (2⭐)

### 6. Assignment Tester Details (2 nodes)

- **Long Code** - `tester.long_code` (2⭐)
- **Long Code Linearity Test** - `tester.long_code_test` (4⭐)
  - *Fourier analysis on Boolean cube*

### 7. Probabilistic Toolkit (2 nodes)

- **Chernoff Bound** - `prob.chernoff` (3⭐)
  - *May exist in mathlib*
- **Union Bound** - `prob.union_bound` (1⭐)
  - *Basic probability*

### 8. NP-Completeness Infrastructure (3 nodes)

- **Polynomial-Time Reduction** - `np.poly_reduction` (2⭐)
- **SAT Language** - `np.sat_def` (1⭐)
- **SAT is NP-complete** - `np.sat_np_complete` (4⭐)
  - *Cook-Levin theorem - may port from Isabelle*

### 9. Powering Soundness Helpers (2 nodes)

Breaks down the 5-star `powering_soundness`:

- **Walk-Based Constraint** - `powering.walk_constraint_def` (3⭐)
- **Bad Assignment Analysis** - `powering.bad_assignment_analysis` (4⭐)
  - *Key lemma using random walk mixing*

## Critical Paths Now Visible

### Path to Powering Soundness (5⭐)

```
spectral.adjacency_matrix
  → spectral.eigenvalues
  → random_walk.mixing
  → random_walk.path_sampling (needs prob.chernoff)
  → powering.bad_assignment_analysis
  → constraint_graph.powering_soundness
```

### Path to Explicit Expanders (5⭐)

```
expander.edge_expansion_def
  → expander.explicit_family
  → preprocess.prep1
  → constraint_graph.preprocess
```

### Path to Assignment Testers (4⭐)

```
codes.hadamard
  → tester.long_code
  → tester.long_code_test
  → assignment_tester.existence
```

## Difficulty Distribution

| Stars | Count | Notes |
|-------|-------|-------|
| ⭐ | 3 | Easy foundations |
| ⭐⭐ | 11 | Moderate definitions |
| ⭐⭐⭐ | 11 | Challenging lemmas |
| ⭐⭐⭐⭐ | 12 | Hard proofs |
| ⭐⭐⭐⭐⭐ | 8 | Hardest (expanders, powering, Cheeger, etc.) |

## Work Package Breakdown

| WP | Name | Nodes | Est. LOC |
|----|------|-------|----------|
| WP-A | Foundations | 5 | 490 |
| WP-B | Expanders & Preprocessing | 15 | 2,490 |
| WP-C | Powering | 10 | 2,040 |
| WP-D | Assignment Testers | 9 | 1,430 |
| WP-E | Amplification Main | 1 | 200 |
| WP-F | Equivalences & Endgame | 5 | 700 |

## What This Means

### Before (19 nodes)
- High-level architecture only
- Many 4-5 star "black boxes"
- ~3,470 LOC estimated
- Unclear dependencies

### After (45 nodes)
- Detailed implementation plan
- Hard theorems broken into manageable pieces
- ~7,350 LOC estimated (more realistic)
- Clear dependency chains
- Explicit missing mathlib infrastructure identified

### Key Improvements

1. **`powering_soundness` (5⭐) is no longer a black box**
   - Now has 3 helper lemmas leading to it
   - Clear path through spectral theory → random walks → concentration

2. **Preprocessing is concrete**
   - prep1 and prep2 broken out separately
   - Each with soundness lemmas

3. **Missing infrastructure identified**
   - Spectral graph theory (4 nodes)
   - Random walks (3 nodes)
   - Coding theory (4 nodes)
   - Some may exist in mathlib - need to check

4. **Realistic scope**
   - Doubled LOC estimate (3.5k → 7.3k)
   - More granular work items
   - Easier to assign to different contributors

## Next Steps

1. **View the graph**
   ```bash
   make graph  # Opens interactive visualization
   ```

2. **Check mathlib for existing infrastructure**
   - Linear algebra (eigenvalues, Rayleigh quotient)
   - Probability (Chernoff, basic bounds)
   - Coding theory basics

3. **Regenerate Lean files** (optional - if you want updated scaffolding)
   ```bash
   make lean
   ```

4. **Start formalization** on easy nodes (1-2⭐)
   - `prob.union_bound`
   - `np.sat_def`
   - `codes.distance`

## Files Updated

- `website/data/pcp-graph.json` - Main graph (+26 nodes, +31 edges)
- `website/static/pcp-graph.json` - Web visualization copy
- Backup: `website/data/pcp-graph.json.backup` (original 19-node version)

View the expanded graph at http://localhost:8000 after running `make graph`!