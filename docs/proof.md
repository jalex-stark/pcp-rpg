Skip to content
Chat history

You said:
Develop a detailed formalization plan for proving the classical PCP theorem (NP = PCP(log n, 1)) in Lean 4, following the crowd-sourced formalization techniques pioneered by Massot/Buzzard/Scholze/Tao, specifically targeting the blueprint infrastructure.
Requirements:

Write concrete Lean 4 type signatures for all major statements (using mathlib4)
Structure output to be blueprint-compatible with clear dependency graphs
For each lemma: provide formalization notes, referencing specific papers/pages where appropriate (math details can be brief with citations)
Identify the most formalization-friendly proof approach with justification
Flag missing mathlib4 dependencies and suggest intermediate milestones
Mark difficulty levels and natural work boundaries for collaboration
Note where computational aspects need special handling"
ChatGPT said:
Request for GPT-5 Pro
Reasoned for 6m 13s
Below is a blueprint‑style formalization plan for the classical PCP theorem

N
P
=
P
C
P
(
log
⁡
n
,
1
)
NP=PCP(logn,1)
in Lean 4 / mathlib4, following the Liquid Tensor Experiment blueprint practices (clear dependency DAG, lemma‑level notes, cross‑refs, difficulty tags, and work‑packages). The plan takes Dinur’s “gap amplification” route (combinatorial) with assignment‑tester composition, which is the most formalization‑friendly path at present.
Key references are cited inline at each lemma.

0) Chosen approach & why
Approach: Dinur’s proof by gap amplification on constraint graphs + alphabet reduction via assignment testers + conversion Gap‑CSP ↔ PCP.
Why this is formalization‑friendly:

It organizes the proof into modular transformations on finite combinatorial objects (constraint graphs), which Lean handles well.

Core analytic steps are discrete: expander replacement, graph powering, uniform edge sampling.

Algebraic heavy machinery (low‑degree extensions, sum‑check) is avoided; the only “algebraic” block is an explicit constant‑size assignment tester, for which Dinur gives a self‑contained construction (via Long Code) that we can treat as a separate work package. 
Weizmann Institute of Science - Wisdom
+2
Weizmann Institute of Science - Wisdom
+2

We rely on the standard equivalence between NP‑PCP and Gap‑CSP (q‑CSP with completeness 1 and constant soundness) to get O(log n) randomness by sampling a random constraint. 
Weizmann Institute of Science - Wisdom

1) Repository structure (Lean modules)
pcp/
├─ Blueprint.md                         -- narrative + DAG + checklists
├─ PCP/Defs.lean                        -- PCP classes, verifiers, trivial inclusions
├─ PCP/Language.lean                    -- encodings, inputs as bitstrings
├─ PCP/ConstraintGraph/Defs.lean       -- constraint graphs, assignments, UNSAT
├─ PCP/ConstraintGraph/Preprocess.lean -- expanderization (prep1, prep2)
├─ PCP/ConstraintGraph/Powering.lean   -- graph powering G ↦ G^t
├─ PCP/AssignmentTester/Defs.lean      -- assignment testers, composition operator
├─ PCP/AssignmentTester/Existence.lean -- explicit constant-size tester (Long Code)
├─ PCP/Amplification/Main.lean         -- Dinur main step (Theorem 1.5)
├─ PCP/Equivalences.lean               -- Gap-CSP ↔ PCP(log n, O(1))
├─ PCP/NPcomplete/SAT.lean             -- (stub or import) SAT NP-completeness
├─ PCP/Endgame.lean                    -- NP = PCP(log n, 1)
2) Core definitions (Lean type signatures)
Note: All signatures are written to be mathlib4‑compatible and finite/combinatorial. We use SimpleGraph and Sym2 for undirected edges, Fintype for finiteness, and rationals for probabilities via counting.

-- PCP classes ---------------------------------------------------------------

abbrev Bitstring := List Bool
abbrev Language  := Set Bitstring

/-- A q-query *local* decision: which addresses to read and how to decide. -/
structure LocalRule (q : ℕ) :=
  (addrs  : Fin q → ℕ)                      -- addresses in the proof
  (decide : (Fin q → Bool) → Bool)

structure Oracle := (read : ℕ → Bool)

/-- A (non-adaptive) PCP verifier with fixed query budget q and randomness function r. -/
structure PCPVerifier :=
  (q   : ℕ)
  (r   : ℕ → ℕ)                                   -- # random bits as a function of |x|
  (query_rule :
     Π (x : Bitstring), BitVec (r x.length) → LocalRule q)
  (accepts :
     Π (x : Bitstring), BitVec (r x.length) → (Oracle → Bool))
  (correctness_nonadaptive :
     ∀ x ρ, ∀ o o', (∀ i, o.read ( (query_rule x ρ).addrs i ) =
                        o'.read ( (query_rule x ρ).addrs i )) →
           accepts x ρ o = accepts x ρ o')

/-- PCP(r,q) class; completeness c=1 and some fixed soundness s<1. -/
def PCP (r q : ℕ → ℕ) (L : Language) : Prop :=
  ∃ (V : PCPVerifier) (s : ℚ),                   -- soundness bound (0 < s < 1)
    (∀ x ∈ L, ∃ o, (Nat.card {ρ // V.accepts x ρ o}) = 2 ^ (V.r x.length)) ∧
    (∀ x ∉ L, ∀ o, (Nat.card {ρ // V.accepts x ρ o}) ≤ s.num / s.den * 2 ^ (V.r x.length)) ∧
    (V.r = r ∧ V.q = q  -- syntactic equality of resource bounds
    )

-- Constraint graphs / 2-CSP ------------------------------------------------

/-- Binary constraint on alphabet α: a subset of α×α. -/
structure BinRel (α : Type*) :=
  (carrier : α × α → Prop)
  (decidable_carrier : DecidablePred carrier := by infer_instance)

/-- A labeled edge with a binary constraint. -/
structure EdgeC (V α : Type*) :=
  (e   : Sym2 V)
  (rel : BinRel α)

/-- Finite binary CSP on vertices `V` over alphabet `α`. -/
structure BinaryCSP (V α : Type*) [Fintype V] [Fintype α] :=
  (E        : Finset (EdgeC V α))
  (nonempty : 0 < E.card)

abbrev Assignment (V α : Type*) := V → α

/-- Satisfaction of a single constrained edge by an assignment. -/
def EdgeC.sat {V α} (σ : Assignment V α) (ec : EdgeC V α) : Prop :=
  let (u, v) := (Classical.choice ec.e.exists_rep)  -- any endpoint pair
  ec.rel.carrier (σ u, σ v)

/-- Fraction of constraints satisfied by σ. -/
def BinaryCSP.satFrac {V α} [Fintype V] [Fintype α]
  (G : BinaryCSP V α) (σ : Assignment V α) : ℚ :=
  ((G.E.filter (fun ec => Decidable.decide (EdgeC.sat σ ec))).card : ℚ) / G.E.card

/-- UNSAT value of a CSP (minimum fraction of unsatisfied constraints). -/
def BinaryCSP.unsat {V α} [Fintype V] [Fintype α] (G : BinaryCSP V α) : ℚ :=
  1 - sSup {BinaryCSP.satFrac G σ | True}    -- over finitely many σ since V,α finite

-- Graph operations used by Dinur -------------------------------------------

/-- Preprocessing: degree-regularization + expanderization (prep). -/
def preprocess {V α} [Fintype V] [Fintype α]
  (G : BinaryCSP V α) : Σ (V' : Type*) [Fintype V'], BinaryCSP V' α := by
  -- (definition elided; lemma below states its properties)
  admit

/-- Powering: G ↦ G^t (walk-based constraints). Alphabet changes to tuples. -/
def power {V α} [Fintype V] [Fintype α]
  (t : ℕ) (G : BinaryCSP V α) :
  BinaryCSP V (Fin (Gdegree G) → α) := by
  admit

/-- Composition with an assignment tester P (reduces alphabet). -/
structure AssignmentTester :=
  (Σ0        : Type*)
  [fΣ0       : Fintype Σ0]
  (ε         : ℚ)                -- rejection probability coefficient
  (reduce :
     ∀ {V α} [Fintype V] [Fintype α],
       BinaryCSP V α → BinaryCSP (Σ (e : EdgeC V α), Unit) Σ0)
  (sound_complete :
     ∀ {V α} [Fintype V] [Fintype α] (G : BinaryCSP V α),
       ∃ (β : ℚ) (c : ℕ),  -- β>0 soundness factor; linear size factor c
         BinaryCSP.unsat (reduce G) ≥ β * BinaryCSP.unsat G
         ∧ (reduce G).E.card ≤ c * G.E.card)

-- Gap-CSP ↔ PCP ------------------------------------------------------------

/-- From a polynomial-size BinaryCSP over a constant alphabet, we get PCP(log n, O(1)). -/
theorem PCP_of_gapCSP
  {α : Type*} [Fintype α] (hα : Fintype.card α > 1)
  (q : ℕ) :
  (∃ (p : ℕ → ℕ) (Σ : Type*) [Fintype Σ],
     ∀ (x : Bitstring),
       ∃ (G : BinaryCSP (Fin (p x.length)) Σ),
         (G.E.card ≤ (p x.length)) ∧
         -- Gap: either 0 or ≥ 1/2
         (x ∈ someNPcompleteLang → G.unsat = 0) ∧
         (x ∉ someNPcompleteLang → G.unsat ≥ (1 : ℚ) / 2)) →
  ∀ L ∈ {someNPcompleteLang}, PCP (fun n => O(log n)) (fun _ => q) L := by
  admit
(We intentionally keep someNPcompleteLang abstract in this signature: we can instantiate it with SAT or 3‑Colorability; see §7 work packages.)

3) Dependency DAG (chapter‑level)
[PCP/Language] ─┬─> [PCP/Defs] ──────────┬─> [PCP/Equivalences]
                │                        └─> [PCP/Endgame]
[ConstraintGraph/Defs] ─┬─> [Preprocess] ─┬─> [Amplification/Main]
                         ├─> [Powering]   ┤
                         └─> [AssignmentTester/Defs] ─┬─> [AssignmentTester/Existence]
                                                      └─> [Amplification/Main]
[NPcomplete/SAT] ───────────────────────────────┘
4) Lemma‑level plan (with Lean statements, notes, and refs)
Below, each item has: (signature), notes, difficulty, dependencies.

A. Equivalence & trivial inclusions
A1. PCP(log n, 1) ⊆ NP (trivial inclusion).
theorem PCP_subset_NP : ∀ L, PCP (λ n, O(log n)) (λ _, O(1)) L → L ∈ NP
Notes: Enumerate all 2^{O(log n)} random strings and include the proof bits on all queried addresses in the NP certificate. See Arora–Barak, Ch. 11, Remark 11.6(3). 
MIMUW

Diff: ★☆☆☆☆.
Deps: PCP/Defs.

A2. PCP‑view ⇔ Gap‑CSP‑view.
theorem PCP_gapCSP_equiv : (NP ⊆ PCP(log, O(1))) ↔ (Gap-2CSP with constant gap is NP-hard)
Notes: Follow Dinur Lemma 1.3 (§1.1, pp. 2–3): “Theorem 1.1 and 1.2 are equivalent.” The verifier picking a random constraint uses O(log |C|) randomness. 
Weizmann Institute of Science - Wisdom

Diff: ★★☆☆☆.
Deps: ConstraintGraph/Defs, PCP/Defs.

B. Constraint graphs & UNSAT
B1. Definitions of BinaryCSP, satFrac, UNSAT (above).
Notes: Finite maximization via [Fintype (V → α)].
Diff: ★☆☆☆☆.
Deps: mathlib4 finiteness.

B2. 3‑Colorability ≤ₚ BinaryCSP with |Σ|=3 (NP‑hardness of 2‑CSP satisfiability).
theorem threeColor_to_csp : 3Color ≤p (G ↦ (UNSAT(G)=0))
Notes: Dinur Prop. 1.4 (p. 3). Edges get inequality constraints over Σ={1,2,3}. 
Weizmann Institute of Science - Wisdom

Diff: ★☆☆☆☆.
Deps: ConstraintGraph/Defs, basic graph encoding.

C. Preprocessing (regularization + expansion)
C1. prep1: vertex blow‑up with cloud expanders; equality constraints within clouds.
theorem prep1_regular_and_unsat : ∃ c d0, ... c * UNSAT(G) ≤ UNSAT(prep1 G) ≤ UNSAT(G)
Notes: Dinur Def. 4.1 and Lemma 4.1 (p. 12). Requires an explicit family of constant‑degree expanders. 
Weizmann Institute of Science - Wisdom

Diff: ★★★☆☆.
Deps: Expander existence (Lemma 2.1), Sym2 API.

C2. prep2: add expander edges + self‑loops to obtain spectral gap λ(G) ≤ λ₀ < d.
theorem prep2_expander : λ(prep2 (prep1 G)) ≤ λ0 ∧ ... ∧ UNSAT inequalities
Notes: Dinur Lemma 4.2 and Theorem 2.3 (Cheeger‑style spectral bound). We need adjacency matrices, Rayleigh quotient. 
Weizmann Institute of Science - Wisdom

Diff: ★★★★☆ (requires spectral graph primitives).
Deps: Linear algebra (eigenvalues), expanders.

C3. Combined:
lemma preprocess_spec : ∃ λ d β₁, ... (β₁*UNSAT(G) ≤ UNSAT(preprocess G) ≤ UNSAT(G)) ∧ regular ∧ λ ≤ const
Notes: Dinur Lemma 1.7 (pp. 5, 10–12). 
Weizmann Institute of Science - Wisdom

Diff: ★★★★☆.
Deps: C1, C2.

D. Powering (gap amplification)
D1. Define Gᵗ (walk‑based constraints; alphabet grows).
def power (t : ℕ) (G : BinaryCSP V α) : BinaryCSP V (α^(d^{⌈t/2⌉}))
Notes: Dinur §1.2 “Graph Powering” (pp. 4–5). Multi‑edges allowed. 
Weizmann Institute of Science - Wisdom

Diff: ★★☆☆☆.
Deps: ConstraintGraph/Defs, SimpleGraph walks.

D2. Soundness of powering (amplifies UNSAT by ~√t).
theorem powering_soundness : ∃ β₂>0, UNSAT(G^t) ≥ β₂ * √t * min (UNSAT(G)) (1/t)
Notes: Dinur Lemma 1.6 (pp. 4–5), with proof relying on expansion / mixing bounds; optional remark about Radhakrishnan variant to get Θ(t) using weighted edges (p. 23). 
Weizmann Institute of Science - Wisdom

Diff: ★★★★★ (core analytic step; needs random walk mixing, spectral bound).
Deps: C3 + spectral inequality.

E. Alphabet reduction via assignment testers (composition)
E1. Assignment tester interface.
structure AssignmentTester (see signatures above).
Notes: Matches Dinur Def. 2.2 (p. 10 / p. 16), with robustness scaled into ε. 
Weizmann Institute of Science - Wisdom

Diff: ★★☆☆☆.

E2. Composition G ∘ P reduces alphabet while preserving UNSAT up to a constant.
theorem composition_lemma : ∃ β₃>0 c, UNSAT(G ∘ P) ≥ β₃ * UNSAT(G) ∧ size ≤ c * size(G)
Notes: Dinur Lemma 1.8 and Def. 5.1 (pp. 16–17). Requires error‑correcting codes with linear dimension; routine. 
Weizmann Institute of Science - Wisdom

Diff: ★★★☆☆.
Deps: E1, basic coding theory (existence of linear‑distance codes, e.g. expander‑based).

E3. Existence of a constant‑alphabet assignment tester.
theorem tester_exists : ∃ P : AssignmentTester, Fintype.card P.Σ0 = O(1) ∧ P.ε ≥ ε0
Notes: Dinur Theorem 5.1 (p. 16) + §7 outline (pp. 23–). Uses the Long Code; purely combinatorial black box OK. 
Weizmann Institute of Science - Wisdom

Diff: ★★★★☆ (but largely decouplable module).

F. Main amplification step and endgame
F1. Dinur Main Theorem (gap‑doubling with linear growth).
theorem dinur_main : ∃ Σ0, ∀ Σ, ∃ C α∈(0,1), ∀ G, ∃ G', size(G') ≤ C*size(G) ∧ (UNSAT(G') ≥ min(2*UNSAT(G), α))
Notes: Combine C3 (preprocess), D2 (powering), E2/E3 (composition) with a fixed constant t, as in proof of Thm 1.5 (pp. 10–11). 
Weizmann Institute of Science - Wisdom

Diff: ★★★☆☆.
Deps: C3, D2, E2, E3.

F2. From Main to NP‑hard Gap‑2CSP (constant gap).
theorem gap2csp_hard : ∃ Σ0, NP-hard ( {G | UNSAT(G)=0} vs UNSAT(G)≥α )
Notes: Iterate F1 O(log n) times to boost the gap; see proof of Theorem 1.2 (pp. 11–12). 
Weizmann Institute of Science - Wisdom

Diff: ★★☆☆☆.

F3. Gap‑2CSP ⇒ PCP(log n, O(1)).
theorem from_gap_to_pcp : SAT ∈ PCP(λ n, O(log n), λ _, O(1))
Notes: Build verifier that (i) computes G, (ii) samples a random constraint (O(log |G|) bits), (iii) queries q=O(1) symbols of the assignment, and accepts iff satisfied. This is exactly Lemma 1.3 (⇐ direction). 
Weizmann Institute of Science - Wisdom

Diff: ★★☆☆☆.
Deps: PCP_of_gapCSP (A2).

F4. Final equality NP = PCP(log n, 1).
theorem PCP_theorem : NP = { L | PCP (λ n, O(log n)) (λ _, O(1)) L }
Notes: Combine A1 (⊆) with F3 and SAT NP‑completeness. The “1” stands for constant queries (q=O(1)). Arora–Barak Theorem 11.5. 
MIMUW

Diff: ★★☆☆☆.
Deps: A1, F3, NP‑completeness.

5) Missing / weak mathlib4 dependencies (and milestones)

5.1) AVAILABLE in mathlib4 (use these)

Graph infrastructure:
- Mathlib.Combinatorics.SimpleGraph.Basic - graph adjacency, walks, degrees, subgraphs
- Mathlib.Combinatorics.SimpleGraph.AdjMatrix - adjacency matrices, "Aⁿ counts n-walks" theorem
- Mathlib.Combinatorics.SimpleGraph.DegreeSum - degree properties
- Mathlib.Combinatorics.SimpleGraph.Maps - graph homomorphisms

Linear algebra / spectral theory (general):
- LinearAlgebra.Matrix.spectrum - matrix eigenvalues
- Analysis.InnerProductSpace.spectrum - spectral theorem for self-adjoint operators
- LinearAlgebra.Eigenspace - eigenspace decomposition

Probability foundations:
- Mathlib.Probability.Kernel.Defs - probability kernels, IsFiniteKernel
- probability.* - measure theory, conditional probability, martingales, variance
- Use for: general Markov chain machinery (transition kernels, finite-state chains)

Note: mathlib has general probability/Markov infrastructure but NOT graph-specific random walks. You'll need to bridge SimpleGraph to Markov kernels for walk distributions.

5.2) MISSING / to be built

Expander graphs (explicit family, combinatorial expansion h(G) ≥ h0).
Needed for C1/C2.
Plan: Formalize zig‑zag product (Reingold–Vadhan–Wigderson) or adopt a "black‑box expander family" interface ExpanderFamily with a placeholder instance, then fill with zig‑zag in a separate mini‑project.
Milestone: Expander.Basic: definitions, existence lemma ∃ d0 h0, explicit family.
Weizmann Institute of Science - Wisdom

Difficulty: ★★★★☆.

Graph Laplacian.
NOT in mathlib4 (as of Jan 2025).
Plan: Define L = D - A using existing SimpleGraph.adjMatrix and degree matrix. Connect to eigenvalues.
Difficulty: ★★☆☆☆.

Spectral graph theory (Cheeger bounds, mixing).
Needed for C2 and D2.
Plan: Build on mathlib4's LinearAlgebra.Matrix.spectrum and SimpleGraph.AdjMatrix. Add: Rayleigh quotient for graphs, bound λ₁ ≤ d − h²/(2d) as in Dinur Theorem 2.3 (p. 8), spectral gap definition.
Weizmann Institute of Science - Wisdom

Difficulty: ★★★★★.

Random walks on graphs (finite, spectral mixing bounds).
Needed for D2.
Plan: Bridge SimpleGraph.AdjMatrix to Probability.Kernel infrastructure. Define walk distribution over t-step neighbors using matrix powers. Prove mixing lemmas: bias bounds from eigenvalues (avoid heavy measure theory; use counting on Finset).
Difficulty: ★★★★☆.
Dependencies: Graph Laplacian, spectral bounds, mathlib4 Markov kernels.

Coding theory basics.
Needed for E2/E3.
Plan: Add: linear codes with linear dimension, constant distance; decoding circuits existence in a “theory‑agnostic” way (as a spec). Much of E2 only needs existence and simple properties. 
Weizmann Institute of Science - Wisdom

Difficulty: ★★☆☆☆.

NP / SAT infrastructure.
If not already available in mathlib4.
Plan: Provide a lightweight NP definition (“polytime verifier + witness length polynomial”) sufficient for SAT NP‑completeness and reductions. Or import an existing Lean formalization if one is available.
Difficulty: ★★★☆☆.

6) Work packages (collaboration boundaries & difficulty)
WP‑A (Foundations): PCP/Defs, Language, basic BinaryCSP + UNSAT.
Diff: ★–★★. Owner style: API‑oriented.

WP‑B (Expanders): Expander.Basic (existence), Preprocess.prep1/prep2.
Diff: ★★★–★★★★. Owner style: graph theory + linear algebra.

WP‑C (Powering): ConstraintGraph/Powering + powering_soundness.
Diff: ★★★★★ (hardest). Owner style: spectral/mixing arguments.

WP‑D (Assignment testers): Defs + Existence (Theorem 5.1).
Diff: ★★★–★★★★. Decoupled; use Long Code tester per Dinur §7. 
Weizmann Institute of Science - Wisdom

WP‑E (Amplification Main): glue C+B+D to prove dinur_main.
Diff: ★★★.

WP‑F (Equivalences & Endgame): Gap‑CSP ⇒ PCP(log n, O(1)), trivial inclusion, NP‑completeness hook, final statement.
Diff: ★★.

7) Formalization‑friendly proof choices & justifications
Constraint‑graph semantics instead of RAM/TM verifiers for most of the development. This keeps everything finite and eliminates measure theory; probabilities are rational counts. (Matches Dinur’s presentation.) 
Weizmann Institute of Science - Wisdom

Expanderization via vertex clouds + equality constraints (prep1) + adding expander edges/self‑loops (prep2) mirrors Dinur’s Lemma 4.1/4.2 exactly and isolates spectral facts to C2. 
Weizmann Institute of Science - Wisdom

Powering step treated with spectral bounds (λ‑based mixing), avoiding parallel repetition and heavy algebra. 
Weizmann Institute of Science - Wisdom

Assignment testers: use Dinur’s explicit but modular tester (Theorem 5.1). This keeps the algebraic content quarantined, and the rest of the pipeline treats it as a black box. 
Weizmann Institute of Science - Wisdom

8) Computational aspects & where to be careful
Randomness accounting: Our verifiers always sample a uniform constraint index; encode randomness as ρ : Fin (E.card) ≃ BitVec (⌈log₂ E.card⌉) to get exact O(log n) bits. No measure theory; just counting on finite types.

Polynomial bounds: Keep explicit size fields (e.g., number of constraints) and prove linear/poly blow‑ups structurally in each transformation (prep1, prep2, power, compose). Dinur’s main theorem does this line‑by‑line (pp. 10–11). 
Weizmann Institute of Science - Wisdom

Self‑loops and multi‑edges: Use Finset (EdgeC V α) (multi‑edges allowed) to match Dinur’s powering definition; be explicit that UNSAT uses multiplicity in the denominator (cardinality of E).

Spectral dependence: Isolate all eigenvalue/expansion lemmas behind a namespace Expander API; do not leak matrices into the combinatorial files.

Encoding choices: Inputs as List Bool; addresses are ℕ. Proof oracles are total ℕ → Bool; local rules ensure only q indices are ever read (we expose and prove this property).

9) Concrete Lean statements for major results (endgame)
/-- Dinur main amplification step (Theorem 1.5). -/
theorem dinur_main
  {V α : Type*} [Fintype V] [Fintype α] :
  ∃ (Σ0 : Type*) [Fintype Σ0],
    ∀ (G : BinaryCSP V α),
      ∃ (G' : BinaryCSP V Σ0),
        G'.E.card ≤ C * G.E.card
      ∧ BinaryCSP.unsat G' ≥ min (2 * BinaryCSP.unsat G) α
      := by admit
-- (C, α are global positive constants)

/-- NP-hardness of constant-gap 2-CSP (Dinur Theorem 1.2 via Theorem 1.5). -/
theorem gap_2csp_constant_hard :
  ∃ (Σ0 : Type*) [Fintype Σ0] (α : ℚ) (q : ℕ),
    NP_hard (fun G : BinaryCSP (Fin _) Σ0 => G.unsat = 0)
            (fun G : BinaryCSP (Fin _) Σ0 => G.unsat ≥ α) := by
  admit

/-- PCP(log n, O(1)) for SAT via Gap-2CSP verifier (sample a random constraint). -/
theorem SAT_in_PCP_log_const :
  PCP (fun n => O(log n)) (fun _ => O(1)) SAT := by
  admit

/-- Trivial inclusion PCP(log n, 1) ⊆ NP. -/
theorem PCP_log_const_subset_NP :
  { L : Language // PCP (fun n => O(log n)) (fun _ => O(1)) L } ⊆ NP := by
  admit

/-- Final statement: NP = PCP(log n, 1). -/
theorem PCP_theorem :
  NP = { L : Language | PCP (fun n => O(log n)) (fun _ => O(1)) L } := by
  admit
10) Formalization notes per lemma (citations)
Equivalence PCP↔Gap‑CSP: Dinur §1.1, Lemma 1.3 (pp. 2–3). 
Weizmann Institute of Science - Wisdom

Constraint‑graph NP‑hard seed: Prop. 1.4 (3‑Color) (p. 3). 
Weizmann Institute of Science - Wisdom

Preprocess (regular/expander): Def. 4.1, Lemma 4.1, Def. prep2 + Lemma 4.2 (pp. 12–14). Uses edge‑expansion and eigenvalue bounds from §2 (Def. 2.1, Lemma 2.1, Thm 2.3). 
Weizmann Institute of Science - Wisdom

Powering: §1.2 “Graph Powering”, Lemma 1.6 (pp. 4–5), with remark p. 23. 
Weizmann Institute of Science - Wisdom

Composition & testers: Def. 2.2, Theorem 5.1, Def. 5.1, Lemma 1.8 (pp. 10, 16–17, 23ff). 
Weizmann Institute of Science - Wisdom

Main theorem assembly + size bounds: Proof of Thm 1.5 (pp. 10–11). 
Weizmann Institute of Science - Wisdom

From gap‑CSP to PCP(log n,O(1)) and trivial inclusion to NP: Arora–Barak Ch. 11 (pp. 4–5). 
MIMUW

11) Testing strategy (blueprint “sanity checks”)
Unit tests (computational): tiny CSPs (paths/cycles) where powering and preprocess can be run and UNSAT computed exactly; check inequalities in lemmas numerically.

Spectral checks: for small graphs, compute adjacency matrices over ℚ and verify Rayleigh inequalities with exact arithmetic to confirm the statement instances.

LocalRule safety: confirm the verifier’s accepts only inspects addresses generated by query_rule (already encoded in correctness_nonadaptive).

12) Natural intermediate milestones
Milestone M0: BinaryCSP formalized; UNSAT well‑defined; NP‑hard seed (3‑Color→UNSAT=0).

M1: preprocess completed with constants (β₁,d,λ); expanders available.

M2: power defined + statement of soundness (admit proof).

M3: assignment‑tester API + composition lemma (assuming tester existence).

M4: dinur_main proven assuming D2.

M5: complete D2 (powering soundness).

M6: tester_exists module filled (Dinur §7).

M7: endgame: Gap‑CSP ⇒ PCP(log n,O(1)), trivial inclusion, NP‑equality.

13) Where composition/randomness affects resource bounds
Random bits are ⌈log₂ |E|⌉ to sample a uniform random edge; since size blow‑ups are linear and the number of amplification rounds is Θ(log n), final |E| is polynomial in input size, giving O(log n) randomness.

Query complexity is the arity of the constraints (2 after powering + composition), thus O(1).
(Dinur also discusses “short PCPs” with log² randomness; that’s a separate length‑optimization layer not needed for NP = PCP(log n, 1).) 
Weizmann Institute of Science - Wisdom

Short glossary of constants (to track in Lean):
β₁ from preprocessing (C3);

β₂ from powering (D2);

β₃ from composition (E2);

α target constant gap in F1; choose t = ⌈(2/(β₁β₂β₃))²⌉ as in Dinur (pp. 10–11). 
Weizmann Institute of Science - Wisdom

14) Final remarks
This blueprint keeps the analytic burden localized (spectral mixing for powering; expander existence) and treats the assignment tester as a self‑contained block. Once the spectral library is in place, the rest are finite combinatorial arguments with exact counting, ideal for Lean. The PCP(log n, 1) equality then follows from the Gap‑CSP constant‑gap reduction plus the standard PCP↔Gap‑CSP equivalence and the trivial inclusion to NP. 
Weizmann Institute of Science - Wisdom
MIMUW

If you want, I can turn this into a Blueprint.md skeleton with checkboxes and PR granularity per file.

You said:
yeah do extract me the immediate drag-and-drop repo initialization, ty
ChatGPT said:
Request for GPT-5 Pro
Reasoned for 5m 34s
Done. Here’s a drop‑in repo scaffold that builds as a stub and mirrors the blueprint’s module boundaries.

Download: pcp-blueprint.zip

What you get
pcp-blueprint/
├─ Blueprint.md
├─ README.md
├─ lean-toolchain                -- uses leanprover/lean4:stable
├─ lakefile.lean                 -- depends on mathlib4
├─ .gitignore
├─ Main.lean                     -- optional, imports PCP aggregator
├─ PCP.lean                      -- imports all submodules
└─ PCP/
   ├─ Defs.lean                  -- Bitstring/Language, LocalRule, Oracle, PCPVerifier, PCP
   ├─ Language.lean             -- placeholder SAT language
   ├─ Amplification/Main.lean   -- axiom dinur_main (signature)
   ├─ AssignmentTester/
   │  ├─ Defs.lean              -- AssignmentTester interface
   │  └─ Existence.lean         -- axiom tester_exists
   └─ ConstraintGraph/
      ├─ Defs.lean              -- BinRel, EdgeC, BinaryCSP, size, unsat (stub)
      ├─ Powering.lean          -- axiom power (signature)
      └─ Preprocess.lean        -- axiom preprocess (signature)
Quickstart
# unzip, cd into it
lake update
lake build
This builds as a clean stub (no proofs required yet). The heavy theorems/transformations are declared as axioms with the exact signatures you’ll replace by defs/theorems + by sorry during the real formalization:

preprocess (regularization/expanderization)

power (graph powering)

AssignmentTester + tester_exists

dinur_main (Dinur’s amplification step)

PCP/Defs.lean already provides the verifier/oracle structures and a PCP predicate (with a stubbed acceptProb) so you can start wiring equivalences and endgame layers without touching the combinatorial side.

Next moves (fast)
Pin a mathlib commit in lakefile.lean once you pick a CI baseline.

Replace axioms with concrete defs/theorems and by sorry to preserve compilation while filling proofs.

If you want CI, drop in a minimal GitHub Action later; not included here to keep the zip lean.

If you want me to pre‑pin mathlib to a known good commit and add a minimal CI workflow, say so and I’ll ship a second zip. 

You said:
> If you want me to pre‑pin mathlib to a known good commit and add a minimal CI workflow, say so and I’ll ship a second zip. 
yeah go for it
ChatGPT said:
Request for GPT-5 Pro
Reasoned for 4m 15s
Pinned and wired.

Download (pinned + CI): pcp-blueprint-pinned.zip

What I changed
Lean toolchain pinned to leanprover/lean4:v4.22.0 in lean-toolchain. 
GitHub

mathlib4 pinned to the tag v4.22.0 in lakefile.lean:

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.22.0"
(This follows the wiki’s advice to pin to mathlib tags matching Lean releases, avoiding breakage from master.) 
GitHub

Verified that v4.22.0 is an official tag. 
GitHub

CI added at .github/workflows/ci.yml using leanprover/lean-action@v1. It:

installs the toolchain from lean-toolchain

restores .lake cache

pulls mathlib’s prebuilt cache (lake exe cache get) automatically

runs lake build
(All per the action’s README.) 
GitHub

Dependabot configured to keep Actions up to date at .github/dependabot.yml.

Quickstart (unchanged)
lake update
lake build
CI workflow (already in the repo)
.github/workflows/ci.yml:

name: CI
on:
  push: { branches: ["main"] }
  pull_request: { branches: ["main"] }
  workflow_dispatch:
jobs:
  build:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4
      - name: Lean build (with mathlib cache)
        uses: leanprover/lean-action@v1
        with:
          use-mathlib-cache: true
          build: true
          test: false
          lint: false
The action auto-detects mathlib and runs lake exe cache get so your CI pulls the precompiled olean artifacts. 
GitHub
+1

Notes / rationale
Pinned pairing: Using a Lean release + matching mathlib tag is the least-friction combo for collaborators and CI. If you need to move later, the mathlib wiki recommends stepping through release(-candidate) tags rather than jumping to master. 
GitHub

Tags available now: v4.22.0 is a stable tag; v4.23.0-rc2 also exists but I avoided RCs unless you want to ride the edge. 
GitHub

Switch versions later (1‑liner edits)
Lean: edit lean-toolchain to leanprover/lean4:vX.Y.Z (or the RC tag).

mathlib: change the tag in lakefile.lean to @ "vX.Y.Z" and run:

rm -rf lake-manifest.json .lake
lake update
(Cleaning the manifest ensures Lake doesn’t cling to the old resolution; then fetch cache.) 
Proof Assistants Stack Exchange

If you want me to also drop a status badge for the workflow into the README or tweak the CI to run lake test/lint when you introduce those targets, say the word. 




No file chosenNo file chosen
ChatGPT can make mistakes. Check important info.
