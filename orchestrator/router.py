"""Router: Main orchestration engine for the PCP-RPG multi-agent system.

This module:
1. Reads RPG graph (pcp-graph.json) and unit.yaml files
2. Routes work to specialized agents (decomposer, prover, failure_analyst, api_curator)
3. Tracks progress and win rates
4. Applies heuristics for resource allocation
"""

import asyncio
import json
import yaml
from pathlib import Path
from typing import Dict, List, Optional
from dataclasses import dataclass

from orchestrator.agents import decompose_spec, try_close_lemmas, analyze_failures, curate_api
from orchestrator.tools import prove_lemmas, top_level_lemmas, extract_lemma_info, lake_build


@dataclass
class UnitConfig:
    """Configuration for a single unit."""

    id: str
    name: str
    work_package: str
    difficulty: int
    namespace: str
    imports: List[str]
    spec: str
    max_lemmas: int
    tactic_budget: int
    tags: List[str]
    slop_files: List[str]
    api_file: str
    api_comment: str
    unit_dir: Path


@dataclass
class UnitResults:
    """Results from proving a unit."""

    lemmas_attempted: int
    lemmas_proven: int
    win_rate: float
    avg_tactics: float
    errors: List[str]
    churn_count: int


def load_heuristics(playbooks_dir: Path) -> dict:
    """Load heuristics from playbooks/heuristics.yaml."""
    heuristics_path = playbooks_dir / "heuristics.yaml"
    if not heuristics_path.exists():
        return {}
    return yaml.safe_load(heuristics_path.read_text())


def load_unit_config(unit_dir: Path) -> UnitConfig:
    """Load unit configuration from unit.yaml."""
    unit_yaml = unit_dir / "unit.yaml"
    if not unit_yaml.exists():
        raise FileNotFoundError(f"unit.yaml not found in {unit_dir}")

    cfg = yaml.safe_load(unit_yaml.read_text())

    return UnitConfig(
        id=cfg.get("id", unit_dir.name),
        name=cfg.get("name", unit_dir.name),
        work_package=cfg.get("work_package", "WP-A"),
        difficulty=cfg.get("difficulty", 2),
        namespace=cfg["namespace"],
        imports=cfg.get("imports", []),
        spec=cfg["spec"],
        max_lemmas=cfg.get("max_lemmas", 30),
        tactic_budget=cfg.get("tactic_budget", 5),
        tags=cfg.get("tags", []),
        slop_files=cfg.get("slop_files", ["Slop_1.lean"]),
        api_file=cfg.get("api_file", "API.lean"),
        api_comment=cfg.get("api_comment", ""),
        unit_dir=unit_dir,
    )


def get_effective_tactic_budget(unit_cfg: UnitConfig, heuristics: dict) -> int:
    """Calculate effective tactic budget based on difficulty and heuristics."""
    # Base budget from work package
    wp_cfg = heuristics.get("work_packages", {}).get(unit_cfg.work_package, {})
    base_budget = wp_cfg.get("tactic_budget", unit_cfg.tactic_budget)

    # Apply difficulty scaling
    difficulty_scale = heuristics.get("difficulty_scaling", {}).get(
        unit_cfg.difficulty, {}
    )
    multiplier = difficulty_scale.get("tactic_multiplier", 1.0)

    return int(base_budget * multiplier)


async def run_unit(unit_dir: Path, heuristics: Optional[dict] = None) -> UnitResults:
    """
    Run the full pipeline for a single unit.

    Pipeline:
    1. Decompose spec into slop file(s)
    2. Prover attempts to complete proofs
    3. Failure analyst proposes fixes (if needed)
    4. Specialized prover (Copilot) attempts each lemma
    5. API curator creates API.lean

    Args:
        unit_dir: Directory containing unit.yaml
        heuristics: Heuristics dict (loaded from playbooks/heuristics.yaml)

    Returns:
        UnitResults with metrics
    """
    if heuristics is None:
        playbooks_dir = Path(__file__).parent.parent / "playbooks"
        heuristics = load_heuristics(playbooks_dir)

    # Load configuration
    unit_cfg = load_unit_config(unit_dir)
    tactic_budget = get_effective_tactic_budget(unit_cfg, heuristics)

    print(f"\n{'='*60}")
    print(f"Running unit: {unit_cfg.name}")
    print(f"Work package: {unit_cfg.work_package}")
    print(f"Difficulty: {unit_cfg.difficulty}")
    print(f"Tactic budget: {tactic_budget}")
    print(f"{'='*60}\n")

    # Step 1: Decompose
    print("Step 1: Decomposing spec into micro-lemmas...")
    slop_code = decompose_spec(
        spec=unit_cfg.spec,
        imports=unit_cfg.imports,
        namespace=unit_cfg.namespace,
        max_lemmas=unit_cfg.max_lemmas,
        tactic_budget=tactic_budget,
    )

    slop_path = unit_cfg.unit_dir / unit_cfg.slop_files[0]
    slop_path.write_text(slop_code)
    print(f"  → Generated {slop_path.name}")

    # Step 2: Prover tries to complete proofs
    print("\nStep 2: Attempting to complete proofs with Claude...")
    proved_code, errors = try_close_lemmas(slop_code, tactic_budget=tactic_budget)

    if errors:
        print(f"  → {len(errors)} errors, invoking failure analyst...")

        # Step 3: Failure analyst
        error_log = "\n".join(errors)
        analysis = analyze_failures(proved_code, error_log)
        print(f"  → Analysis complete")

        # Apply patch (simple version for now)
        # In a full version, this would parse and apply structured patches
        proved_code = proved_code  # Keep original for now

    slop_path.write_text(proved_code)
    print(f"  → Updated {slop_path.name}")

    # Step 3.5: Build with Lake to check for Lean errors
    print("\nStep 3.5: Building with Lake...")
    build_ok, build_log = lake_build(unit_cfg.unit_dir)
    if not build_ok:
        print(f"  ✗ Build failed")
        print(f"  → Check build errors (future: feed to failure analyst)")
    else:
        print(f"  ✓ Build succeeded")

    # Step 4: Index lemmas
    print("\nStep 4: Indexing lemmas...")
    lemma_names = top_level_lemmas(proved_code)
    print(f"  → Found {len(lemma_names)} lemmas")

    # Step 5: Specialized prover (Copilot)
    print("\nStep 5: Proving lemmas with specialized prover (Copilot)...")
    results = prove_lemmas(unit_cfg.unit_dir, lemma_names, prover="copilot")

    proven = sum(results.values())
    attempted = len(results)
    win_rate = proven / attempted if attempted > 0 else 0.0

    print(f"  → Proven: {proven}/{attempted} ({win_rate:.1%})")

    # Step 6: Curate API
    print("\nStep 6: Curating API...")
    stable_lemmas = [
        {"name": name, "file": unit_cfg.slop_files[0]}
        for name, ok in results.items()
        if ok
    ]

    if stable_lemmas:
        api_code = curate_api(
            namespace=unit_cfg.namespace,
            slop_files=unit_cfg.slop_files,
            proven_lemmas=stable_lemmas,
            module_comment=unit_cfg.api_comment,
        )

        api_path = unit_cfg.unit_dir / unit_cfg.api_file
        api_path.write_text(api_code)
        print(f"  → Generated {api_path.name} with {len(stable_lemmas)} exports")
    else:
        print(f"  → No stable lemmas to export")

    # Step 7: Record results
    print("\nStep 7: Recording results...")
    results_data = {
        "unit_id": unit_cfg.id,
        "unit_name": unit_cfg.name,
        "work_package": unit_cfg.work_package,
        "difficulty": unit_cfg.difficulty,
        "tags": unit_cfg.tags,
        "lemmas_attempted": attempted,
        "lemmas_proven": proven,
        "win_rate": win_rate,
        "tactic_budget": tactic_budget,
        "results": results,
    }

    results_path = unit_cfg.unit_dir / "results.json"
    results_path.write_text(json.dumps(results_data, indent=2))
    print(f"  → Saved results to {results_path.name}")

    print(f"\n{'='*60}")
    print(f"✓ Unit complete: {win_rate:.1%} win rate")
    print(f"{'='*60}\n")

    return UnitResults(
        lemmas_attempted=attempted,
        lemmas_proven=proven,
        win_rate=win_rate,
        avg_tactics=0.0,  # TODO: compute from proven lemmas
        errors=[],
        churn_count=0,
    )


def score_unit(
    unit_cfg: UnitConfig,
    rpg_graph: dict,
    win_rates: Dict[str, float],
    heuristics: dict,
) -> float:
    """
    Score a unit to determine priority.

    Higher score = higher priority.

    Scoring factors:
    - Impact: Number of dependent nodes in RPG
    - Blockers: Number of unsatisfied dependencies
    - Win rate: Historical success for this work package/tags
    - Freshness: Recency of last work
    - Difficulty: Prefer easier units (warm-up)
    """
    weights = heuristics.get("director_scoring", {}).get("weights", {})

    # Impact: count dependents in RPG graph
    impact = 0
    for node in rpg_graph.get("nodes", []):
        deps = node.get("dependencies", [])
        if unit_cfg.id in deps:
            impact += 1

    # Blockers: count unsatisfied dependencies
    blockers = 0
    # TODO: look up dependencies and check their status

    # Win rate: lookup historical win rate for work package
    wp_win_rate = win_rates.get(unit_cfg.work_package, 0.5)

    # Freshness: TODO - track last modified time
    freshness = 1.0

    # Difficulty: inverse (prefer easier)
    difficulty_score = 1.0 / unit_cfg.difficulty if unit_cfg.difficulty > 0 else 1.0

    # Weighted sum
    score = (
        weights.get("impact", 0.3) * impact
        + weights.get("blockers", 0.25) * (1.0 / (1.0 + blockers))
        + weights.get("win_rate", 0.25) * wp_win_rate
        + weights.get("freshness", 0.15) * freshness
        + weights.get("difficulty", 0.05) * difficulty_score
    )

    return score


async def run_all_units(project_root: Path):
    """
    Discover and run all units in the project.

    Units are discovered by finding directories with unit.yaml files.
    """
    playbooks_dir = project_root / "playbooks"
    heuristics = load_heuristics(playbooks_dir)

    # Discover units
    unit_dirs = []
    for unit_yaml in project_root.rglob("unit.yaml"):
        unit_dirs.append(unit_yaml.parent)

    print(f"Discovered {len(unit_dirs)} units")

    # Load RPG graph
    rpg_path = project_root / "website" / "data" / "pcp-graph.json"
    rpg_graph = {}
    if rpg_path.exists():
        rpg_graph = json.loads(rpg_path.read_text())

    # Score and sort units
    win_rates = {}  # TODO: load from previous results
    unit_scores = []
    for unit_dir in unit_dirs:
        try:
            unit_cfg = load_unit_config(unit_dir)
            score = score_unit(unit_cfg, rpg_graph, win_rates, heuristics)
            unit_scores.append((score, unit_cfg))
        except Exception as e:
            print(f"Warning: Could not load {unit_dir}: {e}")

    unit_scores.sort(reverse=True, key=lambda x: x[0])

    # Run units in priority order
    for score, unit_cfg in unit_scores:
        print(f"\n[Priority: {score:.2f}] {unit_cfg.name}")
        try:
            results = await run_unit(unit_cfg.unit_dir, heuristics)
            # Update win rates for future scoring
            win_rates[unit_cfg.work_package] = results.win_rate
        except Exception as e:
            print(f"Error running unit {unit_cfg.name}: {e}")
            import traceback

            traceback.print_exc()


if __name__ == "__main__":
    import sys

    if len(sys.argv) < 2:
        print("Usage:")
        print("  python -m orchestrator.router <unit_dir>  # Run single unit")
        print("  python -m orchestrator.router --all        # Run all units")
        sys.exit(1)

    project_root = Path(__file__).parent.parent

    if sys.argv[1] == "--all":
        asyncio.run(run_all_units(project_root))
    else:
        unit_dir = Path(sys.argv[1])
        result = asyncio.run(run_unit(unit_dir))
        print(f"\nFinal win rate: {result.win_rate:.1%}")
