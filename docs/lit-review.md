Skip to content
Chat history

You said:
"Conduct a comprehensive survey of existing projects, papers, and tools that overlap with large-scale collaborative formalization efforts, particularly those relevant to formalizing complexity theory results like the PCP theorem in proof assistants.
Core areas to investigate:
1. Large-scale formalization projects:

Liquid Tensor Experiment (Scholze's project - blueprint methodology, collaboration patterns)
Sphere Eversion project (blueprint infrastructure origins)
FLT (Fermat's Last Theorem) formalization efforts
Busy Beaver challenge formalization
IMO Grand Challenge and related competition math formalizations
Formal Abstracts project
Any attempts at formalizing complexity theory (Cook-Levin, IP=PSPACE, etc.)

2. AI-assisted proof development:

LeanDojo, ReProver, Lean Copilot - capabilities and limitations
Magnushammer and Thor (proof search tools)
Minerva/Llemma for mathematical reasoning
Draft-Sketch-Prove and similar architectures
Baldur and other neural theorem provers
Any papers on LLM + ITP (Interactive Theorem Prover) integration

3. Proof engineering infrastructure:

Blueprint software (technical details, best practices, limitations)
Alectryon and other literate proof tools
Mathematical Components methodology
Hierarchy Builder and similar automation
Lean 4 metaprogramming techniques for large proofs
CI/CD for formal proofs (what exists, what works)

4. Distributed/collaborative formalization:

Formal Proof Web initiatives
Crowdsourcing approaches in Coq/Lean/Isabelle
Version control patterns for large formal developments
Modularization strategies from successful projects
Communication protocols between human/AI collaborators

5. Complexity theory formalization specifically:

Any PCP-related formalization attempts (even failed/incomplete)
Formalized probabilistic proof systems
Expander graphs in proof assistants
Error-correcting codes formalization
Gap amplification techniques in formal settings
NP-completeness results already formalized

6. Relevant tooling innovations:

Proof repair and adaptation tools
Automatic lemma extraction/generalization
Proof mining from informal sources
Natural language to formal statement translation
Progress tracking for large formalizations

For each relevant project/paper provide:

Brief summary of approach and current status
What worked well vs. pain points encountered
Reusable components (code, techniques, lessons learned)
Contact points or active communities
Estimated human/compute resources used
Key technical innovations we could adopt

Special attention to:

Projects that failed or stalled (why?)
Unexpected bottlenecks in large formalizations
Social/coordination innovations not just technical ones
Cost-benefit analyses of different approaches

Output as structured survey with clear recommendations for what to adopt, what to avoid, and what gaps our project could fill."
You might also want specialized variants:
For the technical deep-dive:
"Focus specifically on the blueprint software stack - how does it work internally, what are its limitations, who's extending it, and what alternatives exist?"
For the social/coordination aspect:
"Survey how successful collaborative formalization projects handled contributor onboarding, credit assignment, conflict resolution, and maintaining momentum"
For the AI tooling landscape:
"Create a capability matrix of all available AI tools for Lean 4, including setup complexity, hardware requirements, success rates on different proof types, and integration patterns"
ChatGPT said:
Request for GPT-5 Pro
Reasoned for 10m 4s
Below is a decision‑oriented survey of projects, papers, and tools that materially overlap with a large, collaborative formalization effort aimed at complexity theory (e.g., a PCP‑theorem scale effort). I’ve organized each item into: What it is & status → What worked → Pain points → Reusable bits (code/methods) → People/where to reach them → Resources (very rough) → Technical innovations. I end each section with recommendations and a gap analysis focused on formalizing PCP and adjacent results.

0) Executive takeaways (actionable)
Pick Lean 4 for collaboration & tooling; Isabelle/HOL for pre‑existing complexity libraries. For PCP‑scale work, Isabelle has mature libraries for NP‑completeness and expanders; Lean 4 has the strongest blueprint + community CI + LLM tooling momentum. Consider a Lean core plus Isabelle side cars for specific facts (e.g., expanders) if re‑formalization burden in Lean is too high.

Adopt the “blueprint + merge‑queue (bors) + CI cache” stack from day one. It unlocked the Liquid Tensor Experiment (LTE) and PFR efforts. Use it to carve PCP into dependency‑tracked modules with publicly visible progress and PR gates.

AI helpers are ready for “inner loop” productivity, not end‑to‑end proofs. Use LeanDojo/Lean Copilot/ ReProver to propose steps, search premises, repair fragments, and mine lemmas; don’t budget them as primary provers for PCP‑critical lemmas. Keep all AI under CI with rate‑limited experiments.

Scope PCP as a staged program: (A) foundations for randomized/probabilistic reasoning + graph expansion + codes; (B) parallel repetition / gap amplification; (C) one (Dinur‑style) proof skeleton. Expect to upstream reusable libraries (expanders, codes, gap amplification primitives).

1) Large‑scale formalization projects (what to copy, what to avoid)
Liquid Tensor Experiment (LTE)
What & status. Community Lean project that completed a difficult theorem in Clausen–Scholze’s “liquid” mathematics (completed July 14, 2022). The full blueprint and code are public. ~“about a dozen mathematicians and several computer scientists” involved.

What worked.

Blueprint: human‑readable plan tightly linked to Lean code and a dependency graph to visualize status/critical paths.

Public, iterative build: frequent merges under a maintained queue and cache sped contributor feedback loops.

Pain points. CI/blueprint plumbing occasionally stalled; keeping blueprint and code in sync requires maintenance.

Reusable bits. The blueprint site, doc generation, and dependency graph pattern; contributor playbook (PR review, bors).

People/where. Lean Zulip (#liquid, mathlib maintainers).

Resources (rough). Multi‑month effort, dozens of contributors; steady CI time.

Technical innovations. Social/process innovation more than new automation; blueprint as “live spec.”
Recommendation: Adopt the LTE blueprint+CI pattern outright. It’s the best proven template for a PCP‑scale project. Avoid bespoke infra; reuse Massot’s blueprint tool.

Sphere Eversion project (Lean)
What & status. Complete Lean formalization of the h‑principle for open/ample differential relations, yielding sphere eversion. The blueprint pioneered the dependency‑graph style later used widely.

What worked. Dependency‑graph visualization and a public blueprint; small, tightly knit core team.

Pain points. Requires LaTeX + plasTeX + custom pipeline; contributors must learn the tooling.

Reusable bits. The exact build recipe for blueprint sites (plasTeX + leanblueprint).

People/where. Project pages & Lean Zulip.

Resources. Core authors (Massot, Nash, van Doorn) over sustained period.

Technical innovations. The original blueprint infrastructure.
Recommendation: Adopt the same blueprint stack; copy the site template and dep‑graph conventions.

Fermat’s Last Theorem — regular primes (Lean, “FLT‑regular”)
What & status. Completed Lean 4 formalization of the regular‑prime case, including Kummer’s lemma (AFM 2025); public blueprint. An ongoing wider FLT project also exists.

What worked. Reused modern algebraic‑number‑theory infra in mathlib; explicit blueprint for contributors.

Pain points. Choosing proof routes “amenable to formalization” (e.g., avoiding heavy class field theory).

Reusable bits. Number theory infrastructure patterns (class groups, cyclotomic fields) and blueprint structure.

People/where. Repo + Lean Zulip (talks at Lean Together).

Resources. Medium team, multi‑year cadence; CI bound to mathlib evolution.

Technical innovations. Strategy selection for formalizability; upstreaming abstractions.
Recommendation: Emulate the “choose the formalizable proof” policy for PCP (favor Dinur‑style primitives with clean combinatorial lemmas).

Busy Beaver (BB(5)): massive collaborative + Coq formalization
What & status. The 5‑state busy beaver value S(5)=47,176,870 established (2024), with a Coq‑formalized proof; BB Challenge method + reproducibility notes public.

What worked. Open, distributed problem‑slicing + a formal checker as acceptance gate. Community onboarding via a single portal.

Pain points. Large formal artifacts (reports of ~10h compile of the Coq proof on a laptop); significant engineering to make deciders reproducible.

Reusable bits. Decider patterns, reproducibility/validation protocols.

People/where. bbchallenge.org and associated forums.

Resources. Long‑running crowd effort; nontrivial compute to validate.

Technical innovations. Community method + formal acceptance loop; narrative documentation.
Recommendation: Copy the “method” page concept for PCP: clear contribution rules, validation criteria, and formal acceptance conditions tied to CI.

Olympiad/competition math (for corpora & progress tracking)
What & status. IMO Grand Challenge (F2F variant envisions machine‑checkable proofs); miniF2F provides cross‑system formalized statements; several groups are now publishing new Lean 4 formal proofs of IMO problems; additional “Lean Workbook” datasets exist.

What worked. Benchmarks that translate cleanly to Lean/Isabelle; publishing proof counts and checkability constraints.

Pain points. Autoformalization noise and data contamination risks; heterogeneous encodings across systems.

Reusable bits. Datasets (miniF2F; Lean‑Workbook) and competition‑style “progress dashboards.”

People/where. IMO Grand Challenge site; math AI communities.

Resources. Ongoing; mostly data curation and targeted formalizations.

Technical innovations. F2F “machine‑checkable in ≤10 min” constraint is a useful standard for PCP sublemmas.
Recommendation: Use miniF2F‑style gating on PCP sub‑results (time‑bounded checking and standardized encodings).

Formal Abstracts (Hales et al.)
What & status. Program to publish “formal abstracts” linked to formal artifacts; positions formal abstracts as an on‑ramp (“golden gate”) to formalization.

What worked. Low‑barrier front matter that anchors readers and contributors.

Pain points. Needs consistent linking to living proofs.

Reusable bits. Write a PCP formal abstract early, keep it hot‑linked to blueprint and CI.

2) AI‑assisted proof development (Lean‑centric, with relevant Isabelle/Coq)
Lean‑native / directly useful:

LeanDojo — retrieval‑augmented Lean environment + dataset + tooling (NeurIPS D&B). Helps premise search, proof‑state extraction, and LLM‑driven step proposals; integrates with Lean 4. Use for local search & data generation.

ReProver / ReProver v2 — artifacts and preference datasets for ranking candidate proofs, guiding selection/repair. Plug into CI as a linter for AI‑proposed patches.

Lean Copilot — runs LLM inference inside Lean, supports local GPUs or cloud; framework to build your own tactics/agents. Use as a “lint‑and‑suggest” copilot, not a one‑click prover.

Lean4trace — proof‑state extraction inside elaborator for better training/analysis; useful for your PCP corpus.

Process‑Driven Autoformalization in Lean 4 & Type‑checking‑gated autoformalization — pipelines that leverage compiler feedback and type‑check filtering to drastically reduce noise in NL→Lean translation. Use for statement skeletons and lemma mining, under strict checking.

REAL‑Prover / Apollo (2025) — open‑source Lean 4 provers orchestrating LLMs, retrieval, and auto‑repair loops; early but promising for college‑level and structured problems; good pattern libraries to reuse.

Cross‑system but informative:

MagnusHammer (Isabelle) + Thor (neural‑guided connection prover) — strong premise selection + external ATP backbone; a model for “hammer‑style” hybrids that Lean lacks at the same maturity. Architectural inspiration for a Lean “hammer.”

Baldur — whole‑proof generation with Coq/Isabelle integration; evidence that whole‑proof + lemma extraction can beat pure step‑by‑step. Borrow the scaffold → refine → reconstruct loop.

Draft‑Sketch‑Prove — use informal sketches to steer formal proving. Adopt for PCP “big‑picture” lemmas (gap amplification sketches).

Minerva / Llemma — large math LLMs; helpful for informal derivations, but require tight guardrails when touching formal code.

Bottom line. These tools boost the inner loop (premise selection, single‑goal tactics, autoformalization of statements, proof repair). None removes the need for hand‑tooled libraries for expanders, codes, and probabilistic checkers.

3) Proof engineering infrastructure
Blueprint software (Lean) — plasTeX‑based tool to author a LaTeX/Lean hybrid “plan” with hyperlinks to code and auto‑generated dependency graphs + status colors (ready/statement/proved). Well‑worn in Sphere Eversion, LTE, PFR. Adopt as your primary task board.

Alectryon (best with Coq) — literate proof rendering; great for expository docs and papers; Lean support is limited/experimental; in Lean, blueprint + doc‑gen has become the norm.

MathComp methodology (Coq) — SSReflect + canonical structures; still the reference for large algebraic hierarchies and proof discipline (inspired “Hierarchy Builder”). Use its design ideas when shaping Lean modules.

Hierarchy Builder (Coq) — high‑level commands to evolve algebraic hierarchies without breaking users; drives MathComp‑Analysis. Lessons for API stability & refactoring.

Lean 4 metaprogramming & automation — Aesop (white‑box proof search), lake build & package manager, mathlib olean cache via CI; adopt all for PCP.

CI/CD for proofs — bors merge queue + GitHub Actions build + lake exe cache get to distribute compiled artifacts; PR review guidelines are documented. Non‑negotiable for scale.

4) Distributed / collaborative patterns
Where collaboration happens — Lean Zulip is the hub for onboarding, review routing, and day‑to‑day triage; public contributor docs outline PR/credit processes; teams and maintainers are listed. Mirror this structure in a dedicated PCP stream.

Merge discipline — reviewers + maintainers use bors; delegation patterns let authors finalize merges; reduces merge conflicts on big libraries.

Progress visibility — public blueprint dep graph and per‑module checklists; this matters for recruitment and momentum.

Onboarding — “Where to start” documentation + community map; assign small, non‑blocking lemmas as tickets.
Recommendation: Stand up: a PCP Zulip stream; blueprint site; labeled GitHub board; automated doc builds; and a contributor ladder (reviewer → maintainer).

5) Complexity theory formalization (state of play)
NP‑Completeness library (Isabelle/HOL). A modern framework with many Karp reductions and a complete formalization of Cook–Levin (SAT NP‑completeness) added in 2025, plus SAT→3SAT. Strong baseline to copy definitions/encodings.

Expander graphs (Isabelle/AFP). A full theory including Cheeger’s inequality and explicit constructions; ideal for Dinur‑style PCP proof components.

Error‑correcting codes (Coq/MathComp). Systematic formalization of linear codes in the Coq ecosystem; useful for PCP encoding steps.

Probabilistic proof systems / SNARK soundness (Coq, 2024). Machine‑checked security proofs of modern polynomial‑commitment SNARKs; relevant techniques for probabilistic verifiers and reductions.

IP=PSPACE. Partial formal verification exists (as discussed in 2024 complexity blog coverage), but no complete Lean/Isabelle formalization is public. Treat as future stage, after foundations.

PCP theorem proper. No end‑to‑end formal proof known; however all ingredients (expanders, codes, gap amplification, parallel repetition) are amenable—some already formalized in parts. Focus the project on assembling and standardizing these primitives first.

Gaps to fill for PCP

Lean‑native expanders (with spectral and combinatorial facets unified). 2) Probabilistic method toolkit (Chernoff/hoeffding; random walks on expanders) in Lean. 3) Coding theory primitives (unique list decoding bounds used in PCP pipelines). 4) Parallel repetition/gap amplification libraries. 5) Randomized verifier semantics (step‑indexed coupling with probabilistic outcomes).

6) Tooling innovations relevant to a PCP program
Proof repair. Coq’s Pumpkin Pi and follow‑ups support automated repair across datatype changes and (recently) some behavior changes; use the paradigm for API‑stable libraries and refactors. Lean needs an analog.

Whole‑proof generation + lemma extraction. Coq/Isabelle experiments (Baldur; guided proof search) show that generate→mine lemmas→reconstruct can outperform pure step tactics. Consider this for routine subgoals.

NL→formal translation with type‑checking gates. ProofNet, process‑driven pipelines, and type‑check filtering reduce noisy autoformalization; good for statement harvesting from survey notes.

Progress tracking. The blueprint dep graph is the gold standard for live status.

Recommendations (PCP‑targeted)
Adopt (immediately)
Lean 4 + mathlib + blueprint + bors + cache as core stack; create a public blueprint with dep graph, and wire CI to reject any PR that regresses checked modules.

LeanDojo + Lean Copilot + ReProver inside CI as suggestion/repair tools; gate them behind “no sorry, builds clean, ≤timeout” rules.

Design PCP in staged modules: (i) probabilistic calculus; (ii) expanders; (iii) codes; (iv) gap amplification; (v) verifier skeletons. Assign each its own blueprint chapter with done/ready colors.

Consider / pilot
Isabelle side‑modules for expanders/NP‑C to accelerate early progress; either port to Lean later or keep a “formal citation” to the Isabelle results.

Autoformalization pipelines (statement only) to harvest conjecture lists and sub‑claims from PCP texts, with type‑checking filters.

Avoid / de‑prioritize
Betting on end‑to‑end LLM proof for PCP. Keep LLMs as copilots, not principals.

Building new infra when leanblueprint + mathlib CI already solve the problems.

What your project can uniquely contribute
A Lean‑native expander/codes/gap‑amplification library engineered with PCP in mind (clean APIs, canonical constructions, prob. bounds).

A proof‑engineering playbook for randomized verifiers (semantics + testing idioms) and live dashboards (blueprint).

Appendix A — Brief entries (by topic)
AI + ITP integration (selected)
Draft‑Sketch‑Prove: use informal sketches to guide formal proof search; helpful template for PCP’s high‑level skeleton + local lemmas.

Baldur: whole‑proof generation w/ post‑hoc formal reconstruction; adapt the generate→extract lemmas→reprove loop on sublemmas.

FVEL (Isabelle + LLMs): code→Isabelle translation and LLM ATP; a model for structured LLM use under a proof assistant’s guardrails.

Proof‑engineering & social
PR review + credit: mathlib’s public PR Review Guide and bors delegation are proven mechanisms to keep momentum and fair credit assignment.

Community onboarding: “Where to start” and Zulip map keep a healthy contributor pipeline.

Complexity‑specific building blocks
Cook–Levin / NP‑C framework (Isabelle 2025) — leverage definitions & reduction skeletons.

Expander graphs (Isabelle/AFP) — Cheeger, random walks, explicit constructions.

Linear codes (Coq/MathComp) — linear‑algebraic code theory groundwork.

SNARK soundness (Coq) — formal probabilistic arguments with modern crypto verifiers.

Appendix B — Blueprint stack deep‑dive (how it works; limits; who’s extending it; alternatives)
What it is. leanblueprint is a plasTeX plugin + scripts producing a web blueprint: LaTeX/Lean hybrid text where each lemma/def is linked to code; status colors encode “statement ready / proof ready / formalized,” and the dependency graph is auto‑built. Used in Sphere Eversion, LTE, PFR.

Workflow. Authors maintain a LaTeX blueprint alongside Lean code; CI builds the site and the graph; contributors pick items from the graph and open PRs; maintainers keep blueprint/code in sync.

Limitations. Extra toolchain (LaTeX + plasTeX); sync can drift; CI sometimes breaks until someone tends it. Lean‑only users may prefer just doc‑gen, but you lose the plan.

Extensions/in‑progress. Extraction helpers (embed blueprint chunks inside Lean and extract them), tutorials for blueprint‑driven projects.

Alternatives. Alectryon (great for Coq literate outputs, less for planning), plain doc‑gen sites, GitHub project boards (not dependency‑aware).
Recommendation: Use leanblueprint as the master project plan; keep doc‑gen for API docs.

Appendix C — Social/coordination patterns (onboarding, credit, conflict resolution, momentum)
Onboarding: Stand up a dedicated Zulip stream; pin a “Start here” message with (1) build instructions, (2) first tickets (tiny lemmas), (3) coding standards, (4) blueprint link. Lean’s community pages show how this is run.

Credit: Follow mathlib’s PR review and bors delegation norms; encourage non‑maintainer reviews; keep an AUTHORS file aligned with PRs.

Conflict resolution: Escalate disagreements to maintainers teams (documented governance); use public review threads.

Momentum: Public dependency graph and “sprint weeks” (announce and assign subgraphs). Visible progress is a strong recruit magnet.

Appendix D — AI tooling capability matrix for Lean 4 (today’s practical view)
Tool	Proof granularity	Works offline?	Setup burden	Where it helps most	Integration pattern	Notes
LeanDojo	step/tactic & retrieval	Yes	Med	premise search, state extraction, data gen	python+Lean bridge	Strong dataset; good for training your in‑house agents.
Lean Copilot	suggestion/repair	Yes (or cloud)	Med	“try this” steps, micro‑repairs	runs in Lean	Framework to bring your own models.
ReProver(v2)	artifact ranking	Yes	Low	choose best of K candidate proofs	CI linter/evaluator	Use to filter AI outputs before PR.
REAL‑Prover	step‑wise prover	Yes	Med	college‑level problems	CLI + retrieval	Early, but promising for structured domains.
Apollo (2025)	orchestration/repair	Yes	Med/High	isolate failing subgoals, retry loop	agentic pipeline	Good pattern library for PCP sublemmas.
Lean4trace	data extraction	Yes	Low	dataset creation, tactic eval	elaborator plugin	Use to build your PCP corpus.
(Reference) MagnusHammer/Thor (Isabelle)	premise+ATP	N/A	N/A	inspiration for a future Lean “hammer”	Isabelle only	Architectural north star.
Integration guidance. Put Lean Copilot & LeanDojo behind a stateless bot that comments “Try this:” diffs on PRs; run ReProver to rank; only auto‑merge if all CI proofs reconstruct within the sandbox time limit.

Appendix E — Early PCP work plan (6–12 months)
Project infra (Week 0–2). Repo scaffold, lake + mathlib cache, blueprint with top‑level dependency graph, CI + bors, Zulip stream.

Libraries (Month 1–4).

Expanders in Lean: define combinatorial/spectral expansions; port Cheeger inequalities; basic explicit families. (Use Isabelle AFP as reference.)

Probabilistic toolkit: Chernoff/Hoeffding; random walks on expanders.

Codes: linear codes (syndromes, distance); interfaces needed for reductions (draw from Coq work).

Verifier semantics (Month 3–6). A small probabilistic verifier monad + coupling lemmas; formalize “query complexity” and soundness/completeness definitions.

Gap amplification & parallel repetition (Month 5–9). Formalize one amplification step; benchmark on a toy PCP.

Dinur‑style skeleton (Month 9–12). Wire the steps; track progress with blueprint colors; publish formal abstract + status.

Sources (selected, inline above)
LTE completion & blueprint; Sphere Eversion blueprint & infra; leanblueprint tool; mathlib CI, bors queue; Lean Zulip; Aesop; lake; and contributor docs.

Complexity libraries: Isabelle Cook–Levin and Expander Graphs, Coq linear codes, Coq SNARK soundness.

AI tooling: LeanDojo, ReProver v2, Lean Copilot, MagnusHammer/Thor, Baldur, Draft‑Sketch‑Prove, REAL‑Prover, Lean4trace, autoformalization pipelines.

Collaborative proofs: Busy Beaver (BB(5)) method, formal Coq proof.

Want deeper slices?
Technical deep‑dive (blueprint stack). See Appendix B—internals, limits, extensions, and alternatives.

Social/coordination (onboarding, credit, conflict, momentum). See Appendix C.

Lean‑4 AI capability matrix. See Appendix D.

If you want, I can spin up the initial PCP blueprint skeleton (chapters + dep‑graph stubs + CI recipe) so you can start assigning tasks immediately.




No file chosenNo file chosen
ChatGPT can make mistakes. Check important info.
