#!/usr/bin/env python3
"""
Expand the PCP graph with more detailed nodes.

Adds infrastructure nodes for spectral graph theory, random walks,
coding theory, and breaks down hard theorems into smaller pieces.
"""

import json
from pathlib import Path

def main():
    # Load current graph
    json_path = Path(__file__).parent.parent / 'data' / 'pcp-graph.json'
    with open(json_path) as f:
        data = json.load(f)

    print(f"Current: {len(data['nodes'])} nodes")

    # New nodes to add
    new_nodes = [
        # Spectral Graph Theory Infrastructure (WP-B)
        {
            "id": "spectral.adjacency_matrix",
            "kind": "definition",
            "name": "Adjacency Matrix",
            "status": "planned",
            "path": "PCP/Spectral/Matrix.lean",
            "signature": "def adjacencyMatrix (G : SimpleGraph V) : Matrix V V ℚ",
            "description": "Adjacency matrix of a finite graph over rationals",
            "difficulty": 2,
            "workPackage": "WP-B",
            "estimatedLOC": 80,
            "notes": "Use mathlib's Matrix library; define for undirected graphs"
        },
        {
            "id": "spectral.eigenvalues",
            "kind": "definition",
            "name": "Graph Eigenvalues",
            "status": "planned",
            "path": "PCP/Spectral/Matrix.lean",
            "signature": "def eigenvalues (G : SimpleGraph V) : Multiset ℝ",
            "description": "Eigenvalues of the adjacency matrix, sorted by magnitude",
            "difficulty": 3,
            "workPackage": "WP-B",
            "estimatedLOC": 120,
            "notes": "Requires spectral theorem for symmetric matrices"
        },
        {
            "id": "spectral.rayleigh_quotient",
            "kind": "definition",
            "name": "Rayleigh Quotient",
            "status": "planned",
            "path": "PCP/Spectral/Matrix.lean",
            "signature": "def rayleighQuotient (A : Matrix n n ℝ) (v : n → ℝ) : ℝ",
            "description": "Rayleigh quotient for characterizing eigenvalues",
            "difficulty": 2,
            "workPackage": "WP-B",
            "estimatedLOC": 60,
            "references": [{"paper": "Dinur", "section": "§2", "pages": "p. 8"}]
        },
        {
            "id": "spectral.second_eigenvalue_bound",
            "kind": "lemma",
            "name": "Second Eigenvalue vs Expansion",
            "status": "planned",
            "path": "PCP/Spectral/Expansion.lean",
            "signature": "lemma lambda2_expansion_bound : λ₂(G) ≤ d - h(G)²/(2*d)",
            "description": "Relates second eigenvalue to edge expansion (one direction of Cheeger)",
            "difficulty": 4,
            "workPackage": "WP-B",
            "estimatedLOC": 200,
            "references": [{"paper": "Dinur", "section": "Theorem 2.3", "pages": "p. 8"}],
            "notes": "Core spectral inequality; uses Rayleigh quotient"
        },

        # Random Walks and Mixing (WP-C dependencies)
        {
            "id": "random_walk.definition",
            "kind": "definition",
            "name": "Random Walk on Graph",
            "status": "planned",
            "path": "PCP/RandomWalk/Defs.lean",
            "signature": "def randomWalk (G : Graph V) (t : ℕ) : V → V → ℚ",
            "description": "t-step random walk distribution on regular graph",
            "difficulty": 2,
            "workPackage": "WP-C",
            "estimatedLOC": 100,
            "notes": "Discrete probability; use Fintype for finite state space"
        },
        {
            "id": "random_walk.mixing",
            "kind": "lemma",
            "name": "Spectral Mixing Lemma",
            "status": "planned",
            "path": "PCP/RandomWalk/Mixing.lean",
            "signature": "lemma spectral_mixing : ‖P^t - U‖ ≤ λ₂^t",
            "description": "Random walk converges to uniform exponentially fast in spectral gap",
            "difficulty": 4,
            "workPackage": "WP-C",
            "estimatedLOC": 250,
            "references": [{"paper": "Dinur", "section": "§2.3", "pages": "pp. 8-9"}],
            "notes": "Key for powering_soundness; requires operator norm bounds"
        },
        {
            "id": "random_walk.path_sampling",
            "kind": "lemma",
            "name": "Path Sampling Concentration",
            "status": "planned",
            "path": "PCP/RandomWalk/Concentration.lean",
            "signature": "lemma path_concentration : Pr[walks satisfy bad event] ≤ exp(-Ω(t))",
            "description": "Random t-step paths concentrate around expected values",
            "difficulty": 4,
            "workPackage": "WP-C",
            "estimatedLOC": 200,
            "notes": "Uses Chernoff + independence; needed for powering analysis"
        },

        # Expander Constructions (WP-B)
        {
            "id": "expander.edge_expansion_def",
            "kind": "definition",
            "name": "Edge Expansion",
            "status": "planned",
            "path": "PCP/Expander/Defs.lean",
            "signature": "def edgeExpansion (G : Graph V) : ℚ",
            "description": "Minimum ratio of edges leaving a set to its size",
            "difficulty": 2,
            "workPackage": "WP-B",
            "estimatedLOC": 100,
            "references": [{"paper": "Dinur", "section": "Definition 2.1", "pages": "p. 7"}]
        },
        {
            "id": "expander.explicit_family",
            "kind": "theorem",
            "name": "Explicit Expander Family Exists",
            "status": "planned",
            "path": "PCP/Expander/Explicit.lean",
            "signature": "theorem explicit_expanders : ∃ (family : ℕ → Graph), ∀ n, expands family(n) ∧ explicit",
            "description": "Constructive expander family (zig-zag or algebraic construction)",
            "difficulty": 5,
            "workPackage": "WP-B",
            "estimatedLOC": 400,
            "notes": "HARD - may axiomatize or port from Isabelle AFP; zig-zag product is one route",
            "references": [{"paper": "Reingold-Vadhan-Wigderson", "section": "Zig-Zag Product"}]
        },

        # Preprocessing Breakdown (WP-B)
        {
            "id": "preprocess.prep1",
            "kind": "definition",
            "name": "Vertex Cloud Expansion (prep1)",
            "status": "planned",
            "path": "PCP/ConstraintGraph/Preprocess.lean",
            "signature": "def prep1 (G : BinaryCSP V α) : BinaryCSP V' α",
            "description": "Replace each vertex with a cloud expander; add equality constraints",
            "difficulty": 3,
            "workPackage": "WP-B",
            "estimatedLOC": 150,
            "references": [{"paper": "Dinur", "section": "Definition 4.1", "pages": "p. 12"}]
        },
        {
            "id": "preprocess.prep1_soundness",
            "kind": "lemma",
            "name": "prep1 Preserves UNSAT",
            "status": "planned",
            "path": "PCP/ConstraintGraph/Preprocess.lean",
            "signature": "lemma prep1_unsat : UNSAT(G) ≤ UNSAT(prep1 G) ≤ c₁ * UNSAT(G)",
            "description": "Vertex blow-up changes UNSAT by at most constant factor",
            "difficulty": 3,
            "workPackage": "WP-B",
            "estimatedLOC": 180,
            "references": [{"paper": "Dinur", "section": "Lemma 4.1", "pages": "p. 12"}]
        },
        {
            "id": "preprocess.prep2",
            "kind": "definition",
            "name": "Edge Expander Addition (prep2)",
            "status": "planned",
            "path": "PCP/ConstraintGraph/Preprocess.lean",
            "signature": "def prep2 (G : BinaryCSP V α) : BinaryCSP V α",
            "description": "Add expander edges and self-loops to achieve spectral gap",
            "difficulty": 3,
            "workPackage": "WP-B",
            "estimatedLOC": 120,
            "references": [{"paper": "Dinur", "section": "Definition 4.2", "pages": "p. 13"}]
        },
        {
            "id": "preprocess.regularity",
            "kind": "lemma",
            "name": "Preprocessing Achieves Regularity",
            "status": "planned",
            "path": "PCP/ConstraintGraph/Preprocess.lean",
            "signature": "lemma preprocess_regular : regular (preprocess G) d",
            "description": "Combined preprocessing produces d-regular graph",
            "difficulty": 2,
            "workPackage": "WP-B",
            "estimatedLOC": 100
        },

        # Coding Theory Infrastructure (WP-D)
        {
            "id": "codes.linear_code",
            "kind": "definition",
            "name": "Linear Code",
            "status": "planned",
            "path": "PCP/Codes/Linear.lean",
            "signature": "structure LinearCode (F : Type*) [Field F] (n k : ℕ)",
            "description": "[n,k] linear code over field F with generator matrix",
            "difficulty": 2,
            "workPackage": "WP-D",
            "estimatedLOC": 120,
            "notes": "May exist in mathlib or need basic formalization"
        },
        {
            "id": "codes.distance",
            "kind": "definition",
            "name": "Code Distance",
            "status": "planned",
            "path": "PCP/Codes/Linear.lean",
            "signature": "def distance (C : LinearCode F n k) : ℕ",
            "description": "Minimum Hamming distance between distinct codewords",
            "difficulty": 2,
            "workPackage": "WP-D",
            "estimatedLOC": 80
        },
        {
            "id": "codes.good_codes_exist",
            "kind": "theorem",
            "name": "Good Codes Exist",
            "status": "planned",
            "path": "PCP/Codes/Existence.lean",
            "signature": "theorem good_linear_codes : ∃ C : LinearCode F n k, distance C ≥ δ*n ∧ k ≥ (1-ε)*n",
            "description": "Linear codes with constant rate and relative distance exist (probabilistic or explicit)",
            "difficulty": 3,
            "workPackage": "WP-D",
            "estimatedLOC": 200,
            "notes": "Gilbert-Varshamov or expander codes"
        },
        {
            "id": "codes.hadamard",
            "kind": "definition",
            "name": "Hadamard Code",
            "status": "planned",
            "path": "PCP/Codes/Hadamard.lean",
            "signature": "def hadamardCode (k : ℕ) : LinearCode F 2^k k",
            "description": "Hadamard/Walsh code: encode k bits to 2^k bits",
            "difficulty": 2,
            "workPackage": "WP-D",
            "estimatedLOC": 100,
            "notes": "Used in assignment tester constructions"
        },

        # Assignment Tester Details (WP-D)
        {
            "id": "tester.long_code",
            "kind": "definition",
            "name": "Long Code",
            "status": "planned",
            "path": "PCP/AssignmentTester/LongCode.lean",
            "signature": "def longCode (f : Bool^k → Bool) : Bool^(2^k)",
            "description": "Encodes a function as its truth table",
            "difficulty": 2,
            "workPackage": "WP-D",
            "estimatedLOC": 80,
            "references": [{"paper": "Dinur", "section": "§7", "pages": "pp. 23+"}]
        },
        {
            "id": "tester.long_code_test",
            "kind": "lemma",
            "name": "Long Code Linearity Test",
            "status": "planned",
            "path": "PCP/AssignmentTester/LongCode.lean",
            "signature": "lemma long_code_test : far_from_long_code → reject_probability ≥ ε",
            "description": "Soundness of linearity test for Long Code",
            "difficulty": 4,
            "workPackage": "WP-D",
            "estimatedLOC": 250,
            "notes": "Core of assignment tester; Fourier analysis on Boolean cube"
        },

        # Probabilistic Toolkit (WP-C)
        {
            "id": "prob.chernoff",
            "kind": "lemma",
            "name": "Chernoff Bound",
            "status": "planned",
            "path": "PCP/Probability/Chernoff.lean",
            "signature": "lemma chernoff_bound : Pr[|X - 𝔼[X]| ≥ δ] ≤ 2*exp(-δ²*n/3)",
            "description": "Concentration of sum of independent random variables",
            "difficulty": 3,
            "workPackage": "WP-C",
            "estimatedLOC": 150,
            "notes": "May exist in mathlib probability; key for random walk analysis"
        },
        {
            "id": "prob.union_bound",
            "kind": "lemma",
            "name": "Union Bound",
            "status": "planned",
            "path": "PCP/Probability/Basic.lean",
            "signature": "lemma union_bound : Pr[⋃ᵢ Aᵢ] ≤ ∑ᵢ Pr[Aᵢ]",
            "description": "Basic probability union bound",
            "difficulty": 1,
            "workPackage": "WP-A",
            "estimatedLOC": 40,
            "notes": "Should be in mathlib; include for completeness"
        },

        # NP-Completeness Infrastructure (WP-F)
        {
            "id": "np.poly_reduction",
            "kind": "definition",
            "name": "Polynomial-Time Reduction",
            "status": "planned",
            "path": "PCP/Complexity/Reductions.lean",
            "signature": "def polyReduction (L₁ L₂ : Language) : Prop",
            "description": "L₁ ≤ₚ L₂ via polynomial-time computable function",
            "difficulty": 2,
            "workPackage": "WP-F",
            "estimatedLOC": 100,
            "notes": "May exist in mathlib or need basic complexity theory setup"
        },
        {
            "id": "np.sat_def",
            "kind": "definition",
            "name": "SAT Language",
            "status": "planned",
            "path": "PCP/Complexity/SAT.lean",
            "signature": "def SAT : Language",
            "description": "Boolean satisfiability problem",
            "difficulty": 1,
            "workPackage": "WP-F",
            "estimatedLOC": 80
        },
        {
            "id": "np.sat_np_complete",
            "kind": "theorem",
            "name": "SAT is NP-complete",
            "status": "planned",
            "path": "PCP/Complexity/SAT.lean",
            "signature": "theorem sat_np_complete : SAT ∈ NP ∧ (∀ L ∈ NP, L ≤ₚ SAT)",
            "description": "Cook-Levin theorem",
            "difficulty": 4,
            "workPackage": "WP-F",
            "estimatedLOC": 300,
            "notes": "Major theorem; may port from Isabelle or axiomatize initially",
            "references": [{"paper": "Arora-Barak", "section": "Theorem 2.9"}]
        },

        # Powering Soundness Breakdown (WP-C)
        {
            "id": "powering.walk_constraint_def",
            "kind": "definition",
            "name": "Walk-Based Constraint",
            "status": "planned",
            "path": "PCP/ConstraintGraph/Powering.lean",
            "signature": "def walkConstraint (e : Edge) (t : ℕ) : Constraint (α^t)",
            "description": "Constraint checking consistency along t-step paths",
            "difficulty": 3,
            "workPackage": "WP-C",
            "estimatedLOC": 120
        },
        {
            "id": "powering.bad_assignment_analysis",
            "kind": "lemma",
            "name": "Bad Assignment Structure",
            "status": "planned",
            "path": "PCP/ConstraintGraph/Powering.lean",
            "signature": "lemma bad_assignment_concentration : assignments far from good → many violated walks",
            "description": "Assignments with high UNSAT have many violated random walks",
            "difficulty": 4,
            "workPackage": "WP-C",
            "estimatedLOC": 200,
            "notes": "Key lemma for powering_soundness; uses random walk mixing"
        }
    ]

    # Add new nodes
    data['nodes'].extend(new_nodes)

    # Add corresponding edges (dependencies)
    new_edges = [
        # Spectral infrastructure dependencies
        {"from": "spectral.adjacency_matrix", "to": "spectral.eigenvalues", "type": "depends"},
        {"from": "spectral.adjacency_matrix", "to": "spectral.rayleigh_quotient", "type": "depends"},
        {"from": "spectral.eigenvalues", "to": "spectral.second_eigenvalue_bound", "type": "depends"},
        {"from": "spectral.rayleigh_quotient", "to": "spectral.second_eigenvalue_bound", "type": "depends"},

        # Expander dependencies
        {"from": "expander.edge_expansion_def", "to": "expander.defs", "type": "depends"},
        {"from": "spectral.second_eigenvalue_bound", "to": "expander.cheeger", "type": "depends"},
        {"from": "expander.edge_expansion_def", "to": "expander.cheeger", "type": "depends"},
        {"from": "expander.explicit_family", "to": "preprocess.prep1", "type": "depends"},

        # Random walk dependencies
        {"from": "spectral.eigenvalues", "to": "random_walk.mixing", "type": "depends"},
        {"from": "random_walk.definition", "to": "random_walk.mixing", "type": "depends"},
        {"from": "prob.chernoff", "to": "random_walk.path_sampling", "type": "depends"},
        {"from": "random_walk.mixing", "to": "random_walk.path_sampling", "type": "depends"},

        # Preprocessing breakdown
        {"from": "preprocess.prep1", "to": "constraint_graph.preprocess", "type": "implements"},
        {"from": "preprocess.prep2", "to": "constraint_graph.preprocess", "type": "implements"},
        {"from": "preprocess.prep1", "to": "preprocess.prep1_soundness", "type": "depends"},
        {"from": "preprocess.prep2", "to": "preprocess.regularity", "type": "depends"},
        {"from": "spectral.second_eigenvalue_bound", "to": "preprocess.prep2", "type": "uses"},

        # Powering dependencies
        {"from": "powering.walk_constraint_def", "to": "constraint_graph.power", "type": "depends"},
        {"from": "random_walk.mixing", "to": "powering.bad_assignment_analysis", "type": "depends"},
        {"from": "random_walk.path_sampling", "to": "powering.bad_assignment_analysis", "type": "depends"},
        {"from": "powering.bad_assignment_analysis", "to": "constraint_graph.powering_soundness", "type": "depends"},

        # Coding theory dependencies
        {"from": "codes.linear_code", "to": "codes.distance", "type": "depends"},
        {"from": "codes.linear_code", "to": "codes.hadamard", "type": "depends"},
        {"from": "codes.distance", "to": "codes.good_codes_exist", "type": "depends"},
        {"from": "codes.hadamard", "to": "tester.long_code", "type": "uses"},

        # Assignment tester dependencies
        {"from": "tester.long_code", "to": "tester.long_code_test", "type": "depends"},
        {"from": "tester.long_code_test", "to": "assignment_tester.existence", "type": "depends"},
        {"from": "codes.good_codes_exist", "to": "assignment_tester.composition", "type": "depends"},

        # NP-completeness
        {"from": "np.poly_reduction", "to": "np.sat_np_complete", "type": "depends"},
        {"from": "np.sat_def", "to": "np.sat_np_complete", "type": "depends"},
        {"from": "np.sat_np_complete", "to": "constraint_graph.three_color_np_hard", "type": "uses"},
    ]

    data['edges'].extend(new_edges)

    # Update metadata
    data['metadata']['updated'] = "2025-09-30T00:00:00Z"

    # Write back
    with open(json_path, 'w') as f:
        json.dump(data, f, indent=2)

    print(f"Added {len(new_nodes)} new nodes")
    print(f"Added {len(new_edges)} new edges")
    print(f"New total: {len(data['nodes'])} nodes, {len(data['edges'])} edges")

if __name__ == '__main__':
    main()