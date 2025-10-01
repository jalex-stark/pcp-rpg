raw

Skip to content
Chat history

You said:
2509.16198v2.pdf
PDF
how can i use the stuff rom this paper to get gpt-5 and claude code to Just Do Better on zero -> 100k LOC projects? I'm keeping in mind the cases of a lean4 proof of pcp conjecture and a video game with nontrivial physics engine
ChatGPT said:
Request for GPT-5 Pro
Reasoned for 6m 19s
Short answer: stop letting the model “plan in prose.” Persist the plan as a graph and force GPT‑5 / Claude Code to read–write that graph at every step. Then traverse the graph to generate tests → skeletons → implementations in topological order. That’s the whole win in the RPG/ZeroRepo paper, and you can lift it directly. 
2509.16198v2


Below is a concrete, production‑ready playbook you can drop into your agent stack. I’ll tailor the parts that differ for (a) a Lean4 formalization and (b) a game with a non‑trivial physics engine.

0) Core idea you’re reusing
Repository Planning Graph (RPG): graph nodes carry both functional semantics (capabilities) and implementation anchors (folders, files, classes/functions); edges carry data flows / dependency orderings, giving you a DAG to walk. Replace natural‑language plans with this persistent, machine‑checked blueprint. (See Fig. 1 and Fig. 2; also §3.1–3.3.) 
2509.16198v2


Three stages you must enforce on the agent:

Proposal‑level graph = “what to build” (capabilities).

Implementation‑level graph = “how to build” (folders/files/interfaces + typed flows, base classes).

Graph‑guided generation & TDD in topological order, with graph‑guided localization for edits. (Fig. 1C; §4.) 
2509.16198v2


Why this works: it avoids plan drift and scales near‑linearly in features/LOC; ZeroRepo’s results dwarf terminal agents like Claude Code CLI unless you give those agents an RPG‑like scaffold. (Table 2; §6–§7.) 
2509.16198v2


1) Minimal schema you actually need
Use a single JSON (or a small graph DB) that your prompts read and write. Keep it boring and strict:

{
  "nodes": [
    {
      "id": "algorithms.linear_models.lasso",
      "kind": "capability|folder|file|class|function",
      "name": "Lasso",
      "path": "src/algorithms/regression/linear_models/lasso.py",
      "iface": {
        "type": "class|function",
        "signature": "class LassoRegressor(BaseEstimator): ...",
        "doc": "..."
      },
      "io": {
        "inputs": [{"name": "X", "type": "ndarray"}, {"name": "y", "type": "ndarray"}],
        "outputs": [{"name": "coef_", "type": "ndarray"}]
      },
      "meta": {"owner": "agent", "status": "planned|skeleton|implemented|tested"}
    }
  ],
  "edges": [
    {"from": "data.load.csv", "to": "algorithms.linear_models.lasso", "type": "data_flow", "data_id": "training_matrix"},
    {"from": "algorithms.linear_models.base", "to": "algorithms.linear_models.lasso", "type": "inherits"}
  ],
  "constraints": {
    "acyclic": true,
    "folder_includes_files": true,
    "file_declares_all_ifaces": true
  }
}
This mirrors the paper’s file‑augmented graph → data‑flow/function‑augmented graph (Fig. 1B; §3.3.1–3.3.2). 
2509.16198v2


2) Wrap GPT‑5 / Claude Code with graph‑first prompts
You’ll run two system prompts (one “Planner”, one “Builder”) and a tiny controller:

Planner (proposal → implementation)

Input: high‑level goal, current graph, and a feature tree (see §3.2 Explore–Exploit; Alg. 2).

Output: diff to the graph: new capability nodes, module partitions, then folder/file mapping, then function/class interfaces and typed flows.

Guardrails: “Respond only with a valid JSON diff against the RPG schema; do not emit code; maintain DAG acyclicity; fill io for every leaf.”

Builder (code + tests)

Input: graph (subtree), target leaf, upstream/downstream IO contracts.

Output: unit test first → file skeleton → implementation; update status. If tests fail, propose minimal graph edits before editing code (the paper’s graph‑guided localization/editing, §4, App. C). 
2509.16198v2


Controller

In each loop: (1) Planner expands or refines graph. (2) Topologically sort leaves whose parents are tested or implemented. (3) For each leaf, call Builder. (4) Run tests; on failure, call Builder’s localization routine using the graph (App. C.1–C.3; Algorithms 3–4). 
2509.16198v2


Why two roles? You’re reproducing the paper’s staged behavior while still using GPT‑5/Claude Code as the engine. The graph is the state.

3) Bootstrap the feature tree without EpiCoder
ZeroRepo grounds planning in a 1.5M‑node feature tree; you don’t have that. Do the minimum viable version:

Lean4 tree seed: scrape/hand‑curate Mathlib4 table of contents → branches for foundations / finiteness / graphs / PCP prerequisites (probabilistically checkable proofs) / reductions / coding theory / PCP composition framework / gap amplification / verifier & soundness/complete statements; leaves are lemmas/theorems/tactics you expect.

Physics/game tree seed: math primitives, shapes, broadphase, narrowphase, contact manifold, constraint solver, integrators (semi‑implicit Euler, RK), continuous collision detection, joints, ECS systems, scene graph, networking (rollback?), determinism, asset pipeline, scripting, rendering glue.

Implement the paper’s explore–exploit expansion: retrieve top‑k from the seed by semantic match to user goals; add deliberate “explore” branches to avoid tunnel vision; then refactor into coherent modules (Fig. 1A; §3.2; prompts in App. A.3). 
2509.16198v2


You don’t need perfection—just a structured prior that the Planner extends.

4) Make the graph enforce interfaces before code exists
Two constraints give you 80% of the benefit:

Every file‑level node must list imports, public symbols, and leaf interfaces before generation.

Every edge of type data_flow must carry a data_id, data_type (formal), and a short transformation string (App. B.1 prompt; §3.3.2 “Data‑Flow Encoding”). 
2509.16198v2


The Builder prompt refuses to implement if these are missing → Plan gets fixed first (that’s what stops drift).

5) Topological TDD and regression gates
Enforce the exact testing cadence from §4 and App. C:

Unit tests from docstrings/signatures per leaf; on re‑edits, run regression + integration tests for the affected subgraph (Algorithms 3–4).

Majority‑vote diagnosis to separate test/env failures from implementation bugs (paper’s judge loop). If it’s env/test, let the Builder repair tests only. (Fig. 1C; §4.) 
2509.16198v2


6) What changes for Lean4 (PCP)
RPG mapping for proofs

Node kinds: theory (folder), file (Lean module), def|thm|lemma|tactic (interfaces).

Edges: imports (DAG), uses (lemma dependencies), refines (strengthening), equivalence (for alternative statements), and “semantic data flow” = types (expected goals).

IO types: Lean expressions of the goal and context: {context : List Expr, goal : Expr} (or structured MetaM tactics).

Base classes analogue: tactic combinators / typeclasses / locales → define a small set of global abstractions (e.g., Verifier structure with fields for randomness, queries, proof‑oracle access), just like the paper’s BaseEstimator idea (§3.3.2 “Abstracting Global Interfaces”). 
2509.16198v2


Planning specifics

Proposal level: graph out the composition framework (inner/outer verifiers, PCP of proximity if used), gap amplification, encoding (long code / Hadamard / Reed–Muller), reduction spine from SAT, plus soundness/completeness lemmas and the final theorem statement.

Implementation level: decide module split (e.g., PCP/Verifier, PCP/Composition, Code/ReedMuller, Prob/Randomness, Complexity/Reductions, Soundness, Completeness). Force every theorem node to list prereq lemmas (edges) and the exact goal type.

Tests: you can’t unit‑test the theorem, but you can test computable fragments (encoders/decoders, combinatorial bounds, small models) and run Lean lints + compilation per module. Treat #eval examples and small decision procedures as “unit tests”. The regression layer is import graph rebuild + lean --make of impacted modules.

Failure modes & guardrails

Circular proof deps: your acyclicity checker catches cycles in imports/uses.

Non‑terminating tactics: require every new tactic to carry a fuel parameter in its interface; CI rejects if fuelless.

Foundational drift: lock a small nucleus (e.g., foundations, basic probability) as read_only = true nodes in the graph; the Planner can depend on them but never rewrites them.

7) What changes for Game + physics engine
RPG mapping

Modules (folders): core_math/, geometry/, broadphase/, narrowphase/, contacts/, solver/, integration/, ecs/, scene/, io/, render/, netcode/, scripting/, tooling/.

Edges: strict frame pipeline data flows: input → ecs systems → integration → broadphase → narrowphase → contacts → solver → postsolve events → render. Each edge must specify data_id (e.g., AABBList, ContactManifold, VelocityConstraints) and data_type (your math types).

Base abstractions: IRigidBody, ICollider, ISolver, IIntegrator, IShape (just like the paper’s global anchors). Keep it to 3–5. (§3.3.2.) 
2509.16198v2


Tests you require

Unit: geometry kernels (intersection, EPA/GJK), integrators preserve invariants on toy systems.

Property: momentum/energy bounds, restitution/penetration constraints; determinism across seeds.

Integration: record/replay a fixed scene → checksums of state over N frames; networking rollback smoke tests.

Performance gates (only later): per‑system frame budgets as “tests” that fail when exceeded.

Failure modes & guardrails

Physics correctness drift: every edit that touches contacts/ or solver/ triggers the integration replay test.

Determinism: CI runs with fixed seeds on two machines/containers and diffs state hashes.

Architecture entropy: the Planner is forbidden to introduce new “engine loops”; only new ECS systems connected to the existing pipeline.

8) Glue to Claude Code / GPT‑5 you actually run
State file: rpg.json is the single source of truth.

Controller script (your code):

Loads rpg.json, runs topological sort, chooses next build target(s).

Calls Planner when goals change or edges are underspecified; otherwise calls Builder leaf‑by‑leaf.

Writes files; runs tests; updates node status.

Claude Code CLI / GPT‑5: always given: (a) the relevant RPG subtree, (b) the current file contents, (c) the edge contracts. Prompt templates can be lifted almost verbatim from the paper’s Appendix (B.1 “skeleton mapping”; “mapping feature paths to interfaces”; C.2 “editing tools” patterns). 
2509.16198v2


When you use Claude Code interactively, the command you type is just:
“Do not generate code. Emit an RPG diff for these goals …” or “Implement node <id> respecting these upstream/downstream contracts …” The rest is enforced by the controller.

9) A small set of checks that keep you scaling to 100k LOC
Graph invariants: acyclic; every file node owns every symbol it exports; every edge has typed IO; base classes < 5 global; per‑folder file count thresholds trigger subfoldering (paper’s skeleton rules). 
2509.16198v2


Stop drift: the Builder refuses to code if the node’s IO or parent edges are incomplete.

Progress metric: %leaf nodes tested and #edges with verified data flows (mirrors the paper’s “coverage/pass” framing). (§5.1.2–§6.) 
2509.16198v2


Localization discipline: any bug report is first mapped to RPG nodes via graph‑guided search before opening files (App. C.1). This alone cuts the “where is it?” time ~30–50% in their ablation (Table 4). 
2509.16198v2


10) Two concrete prompt stubs (drop‑in)
Planner — add/repair graph (JSON‑only)

You are the Repository Planner. Input: (a) current RPG JSON, (b) goal, (c) seed feature paths.
Task: 1) select + reorganize features into modules (capability nodes),
2) map to folders/files, 3) design interfaces (signatures, docstrings),
4) add typed data_flow edges, 5) propose at most 3 global base classes.
Output ONLY a valid RPG JSON diff (add/update/remove nodes/edges). No code.
Hard rules: DAG acyclic; every leaf has iface+io; every data_flow has data_id,data_type.
Builder — implement one leaf (tests first)

You are the Repository Builder. Input: RPG subtree for node <id>, parent/child edges with io,
current file text (if any). Produce:
(1) A unit test that exercises the iface contract. (2) A file patch with complete skeleton
(imports; class/function with full docstring). (3) A minimal implementation that passes the test.
If tests fail, propose an RPG patch first (if the contract is wrong), else a code patch.
These mirror the paper’s Appendix prompts and the TDD loop in §4. 
2509.16198v2


11) What you’ll actually see improve
Sustained growth: features and LOC keep climbing rather than stalling after a few rounds (Fig. 5–6).

Higher pass rate: your tests will pass more often because the plan is enforced as structure (Table 2).

Faster localization for edits/bugs (Table 4). 
2509.16198v2


12) Edge cases / pitfalls (and fixes)
Spec creep: only the Planner can mutate the RPG; Builder can suggest diffs but your controller must apply them via the Planner.

Over‑abstracting: cap global base classes at 3–5; reject new ones unless >3 leaves reuse them (§3.3.2 guidance). 
2509.16198v2


Flaky tests: adopt the paper’s majority‑vote classification of failures; quarantine env/test issues and auto‑repair those first (Algorithm 4). 
2509.16198v2


Graph bloat: archive nodes with status=orphaned; collapse long single‑child chains during refactors.

If you want a starter repo
rpg.json schema as above.

planner/ prompt + script (reads rpg.json, applies JSON Patch).

builder/ prompt + script (per‑leaf generation).

runner.py that: toposort(rpg) → build → pytest/lean --make → update rpg statuses.

constraints.py that enforces the invariants and fails the CI if violated.

This is the smallest possible “RPG layer” that lets GPT‑5 or Claude Code “just do better” on zero→100k‑LOC builds while remaining auditable and debuggable. It’s exactly what the paper’s pipeline operationalizes—now attached to the models you already use. (Fig. 1 end‑to‑end; §3–§4; App. B–C.) 
2509.16198v2


If you want, I’ll sketch the initial Lean4/physics feature seeds and the first RPG for each so you can run the loop immediately.


Sources
You said:
is there buzz about this?
ChatGPT said:

Thought
Short version: yes—early buzz, not a full-on hype cycle yet.

Official posts: arXiv went up within the week; MSR published a summary page. 
arXiv
+1

Aggregator traction: HuggingFace “Papers” card and Emergent Mind topic page both picked it up. 
Hugging Face
+1

Social: a few X/Medium explainers circulating (TuringPost, Wes Roth; one Medium breakdown). 
X (formerly Twitter)
+2
X (formerly Twitter)
+2

Tech press: light coverage (e.g., QuantumZeitgeist-style blogs), but no big outlets yet. 
Quantum Zeitgeist

HN/Reddit: I don’t see a front-page HN thread or large Reddit discussion tied to this DOI yet. (I checked; nothing substantive surfaced beyond generic agent threads.)

Substance-wise, the claims people are quoting are the paper’s own: ZeroRepo’s RPG plan → 36k LOC repos, ~81.5% coverage, ~69.7% pass rate vs Claude Code CLI. If you reference numbers, attribute them to the paper, not third-party replications. 
2509.16198v2


If you want signal beyond press posts, two things to watch:

a code release / demo repo from the authors;

benchmarks reproduced by third parties (even a subset of RepoCraft).


Sources




No file chosenNo file chosen
ChatGPT can make mistakes. Check important info.
