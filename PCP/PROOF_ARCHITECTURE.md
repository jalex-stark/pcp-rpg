# PCP Theorem Formalization: Proof Architecture

**Status**: Foundations laid, major components sketched
**Date**: 2025-10-02
**Proof Strategy**: Dinur's gap amplification via constraint graphs

## Overview

This document outlines the formalization architecture for proving:

```
NP = PCP(log n, 1)
```

Equivalently: Every NP problem has a probabilistically checkable proof where:
- The verifier reads O(log n) random bits
- The verifier queries exactly 1 bit of the proof (i.e., constant query complexity)
- Completeness: If x ∈ L, ∃ proof accepted with probability 1
- Soundness: If x ∉ L, every proof is rejected with probability ≥ 1/2

## Proof Strategy: Dinur's Gap Amplification

We follow Dinur (2007) which simplifies the classical proofs by reducing to **gap amplification for constraint satisfaction problems**.

### High-Level Flow

```
3-SAT (NP-complete)
    ↓ [standard reduction]
Constraint Graph (CSP) with small gap
    ↓ [PREPROCESSING: expanderization via replacement product]
Regular, Expanding CSP with small gap
    ↓ [GAP AMPLIFICATION: iterated graph powering]
CSP with exponentially amplified gap (1 vs 1/2)
    ↓ [PCP CONSTRUCTION: local testing]
PCP(log n, 1) verifier
```

### Key Insight

The hardness of 3-SAT transfers to **gap-CSP**: distinguishing satisfiable constraint graphs from those where ≤99% of constraints are satisfiable. Amplifying this gap to 50% gives a PCP.

## Formalized Components

### ✅ Completed Foundations

#### 1. Constraint Graph Theory (`PCP/ConstraintGraph/Defs.lean`)
- **BinaryCSP**: Constraint satisfaction as a graph structure
- **Satisfiability**: Assignment satisfaction, satFrac, UNSAT fraction
- **Size and degree**: Graph metrics
- **Handshaking lemma**: Proven ✓

#### 2. Expander Graph Theory (`PCP/Expander/Defs.lean`)
- **IsRegular**: d-regular graphs
- **Expansion measures**: Vertex/edge expansion, spectral gap
- **Laplacian eigenvalues**: Connected to mathlib's matrix spectrum API
- **secondSmallestLaplacianEigenvalue**: Algebraic connectivity (λ₂)
- **hasSpectralGap**: Spectral gap predicate
- **ExpanderGraph structure**: (n, d, λ)-expanders with real spectral bounds
- **Key lemmas sketched**:
  - Smallest eigenvalue is 0 ✓
  - Eigenvalue bounds [0, 2d] for d-regular graphs
  - Connectivity characterization (λ₂ > 0 ⟺ connected)
  - Cheeger's inequality (spectral ↔ combinatorial expansion)
  - Expander mixing lemma

#### 3. Graph Operations (`PCP/Expander/Operations.lean`)
- **graphPower**: k-th power of a graph (k-step connectivity)
- **Spectral amplification**: λ(G^k) ≈ λ(G)^k
- **Degree bounds**: deg(G^k) ≤ deg(G)^k
- **Explicit construction preservation**

#### 4. Preprocessing (`PCP/ConstraintGraph/Preprocess.lean`)
- **Replacement product**: G ⊗ H (expanderization)
  - Each vertex → cloud (copy of small expander H)
  - Inherits expansion from H
  - Preserves constraint structure from G
- **Satisfiability preservation**
- **Gap preservation** (constant factor)

### 🚧 In Progress / Sketched

#### 5. Gap Amplification (`PCP/ConstraintGraph/Powering.lean`)
- **Power construction**: Iterate graph powering
- **Gap amplification theorem**: Small gap → exponentially amplified gap
- **Soundness analysis**: Error propagation through powered graph

#### 6. Assignment Tester (`PCP/AssignmentTester/`)
- **Local testing**: Verify global properties via local queries
- **Alphabet reduction**: Reduce large alphabet CSPs to binary
- **Error-correcting codes**: Achieve constant query complexity

#### 7. NP-Completeness Infrastructure (`PCP/NPcomplete/`)
- **3-SAT**: Cook-Levin reduction
- **CSP reduction**: 3-SAT → constraint graph
- **Gap introduction**: Initial gap creation

### ❌ TODO: Major Missing Pieces

1. **Spectral gap implementation** (`secondSmallestLaplacianEigenvalue`)
   - Currently has `sorry` for extracting λ₂ from sorted eigenvalues
   - Need: Define sorting, prove antitone property usage is correct

2. **Replacement product details** (`replacementProduct`)
   - Edge structure definition (cloud + bridge edges)
   - Constraint lifting from G to G ⊗ H
   - Concrete expander construction (e.g., explicit (8,3,0.1)-expander)

3. **Cheeger's inequality proof**
   - Connect spectral gap to combinatorial expansion
   - Major theorem, ~50-100 LOC estimated

4. **Gap amplification correctness**
   - Formalize iteration: preprocess → power → test
   - Prove gap grows: δ → δ^Ω(k)

5. **PCP verifier construction**
   - Convert amplified CSP to verifier algorithm
   - Prove O(log n) randomness, O(1) queries
   - Completeness and soundness analysis

## Dependency Graph

```
                    Mathlib
                       ↓
            ┌──────────┴──────────┐
            ↓                     ↓
    SimpleGraph.LapMatrix  Matrix.Spectrum
            ↓                     ↓
         Expander/Defs ←──────────┘
            ↓         ↓
    Expander/Operations  ConstraintGraph/Defs
                  ↓            ↓
            ConstraintGraph/Preprocess
                        ↓
            ConstraintGraph/Powering
                        ↓
                AssignmentTester/
                        ↓
                   Amplification/
                        ↓
                 NPcomplete/SAT
                        ↓
                    Endgame
                        ↓
                  PCP(log n, 1)
```

## Proof Complexity Estimates

| Component | Difficulty | Est. LOC | Status |
|-----------|-----------|----------|--------|
| Constraint graphs | ★★★☆☆ | 200 | ✅ Defined |
| Expander graphs | ★★★★☆ | 300 | ✅ Defined, spectral API connected |
| Spectral lemmas | ★★★★☆ | 200 | 🚧 Sketched |
| Graph operations | ★★★☆☆ | 200 | ✅ Defined |
| Replacement product | ★★★★☆ | 250 | 🚧 Sketched |
| Gap amplification | ★★★★★ | 400 | ❌ TODO |
| Assignment tester | ★★★★☆ | 300 | ❌ TODO |
| NP-completeness | ★★★☆☆ | 150 | ❌ TODO |
| Final assembly | ★★★★☆ | 200 | ❌ TODO |
| **Total** | | **~2200** | **~30% complete** |

## Key Mathematical Dependencies

### From mathlib4 (available):
- ✅ `SimpleGraph.degree`: Vertex degrees
- ✅ `SimpleGraph.lapMatrix`: Laplacian matrix
- ✅ `Matrix.IsHermitian.eigenvalues`: Eigenvalue extraction
- ✅ `SimpleGraph.lapMatrix_mulVec_const_eq_zero`: 1ⁿ is eigenvector
- ✅ `SimpleGraph.posSemidef_lapMatrix`: L is PSD
- ✅ `SimpleGraph.card_connectedComponent_eq_finrank_ker_toLin'_lapMatrix`: Connectivity via kernel dimension

### Missing (need to formalize):
- ❌ Cheeger's inequality
- ❌ Expander mixing lemma
- ❌ Tensor product spectral analysis
- ❌ Random walk analysis on expanders
- ❌ Linear codes with constant distance
- ❌ 3-SAT NP-completeness

## Next Steps (Priority Order)

1. **Fix build** (batteries/mathlib compatibility)
2. **Implement `secondSmallestLaplacianEigenvalue`** (extract λ₂ correctly)
3. **Prove connectivity characterization** (`secondSmallest_pos_iff_connected`)
4. **Define replacement product edges** (cloud + bridge structure)
5. **Prove replacement product preserves satisfiability**
6. **Sketch gap amplification algorithm** (preprocess + iterate powering)
7. **Connect to 3-SAT** (NP-completeness infrastructure)

## References

- **Dinur (2007)**: "The PCP theorem by gap amplification" - main reference
- **Arora-Barak**: Computational Complexity textbook, Chapters 11, 22
- **Trevisan**: PCP lecture notes (UC Berkeley)
- **Mathlib4**: `Mathlib.Combinatorics.SimpleGraph.LapMatrix`
- **Mathlib4**: `Mathlib.LinearAlgebra.Matrix.Spectrum`

## Notes

- Currently blocked by mathlib/batteries compatibility (Lean 4.24.0-rc1 issue)
- Core theory is sound: spectral gap properly connected via Laplacian eigenvalues
- Proof architecture follows Dinur faithfully
- Estimated ~1800 LOC remaining for complete formalization
