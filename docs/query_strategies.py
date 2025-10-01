#!/usr/bin/env python3
"""
Query and visualize proof strategy knowledge graph.

Usage:
  python query_strategies.py --tactic linarith
  python query_strategies.py --error "omega could not prove"
  python query_strategies.py --goal "rational inequality"
  python query_strategies.py --pattern bounds_proof
"""

import json
import argparse
from pathlib import Path
from typing import Any, Dict, List


def load_knowledge_graph(path: Path = Path("proof-strategy-graph.json")) -> Dict[str, Any]:
    """Load the proof strategy knowledge graph."""
    with open(path) as f:
        return json.load(f)


def query_tactic(kg: Dict[str, Any], tactic_name: str) -> None:
    """Query information about a tactic."""
    tactics = kg.get("tactics", {})

    # Try exact match first
    if tactic_name in tactics:
        info = tactics[tactic_name]
        print(f"\n=== {info['name']} ===")
        print(f"\n{info['description']}")

        if "works_with_types" in info:
            print(f"\nWorks with: {', '.join(info['works_with_types'])}")

        if "does_not_work_with" in info:
            print(f"❌ Does NOT work with: {', '.join(info['does_not_work_with'])}")

        if "typical_usage" in info:
            print(f"\nTypical usage: {info['typical_usage']}")

        if "common_mistake" in info:
            print(f"\n⚠️  Common mistake: {info['common_mistake']}")

        if "examples" in info:
            print(f"\nExamples:")
            for ex in info["examples"]:
                print(f"  - {ex}")

        if "references" in info:
            print(f"\nReferences:")
            for ref in info["references"]:
                print(f"  - {ref}")
    else:
        # Fuzzy search
        matches = [name for name in tactics if tactic_name.lower() in name.lower()]
        if matches:
            print(f"\nDid you mean: {', '.join(matches)}?")
        else:
            print(f"\nNo tactic found matching '{tactic_name}'")


def query_error(kg: Dict[str, Any], error_text: str) -> None:
    """Query solutions for a common error."""
    errors = kg.get("common_errors", {})

    # Search for matching error
    matches = []
    for err_id, err_info in errors.items():
        if error_text.lower() in err_info.get("error_message", "").lower() or \
           error_text.lower() in err_info.get("description", "").lower():
            matches.append((err_id, err_info))

    if matches:
        for err_id, err_info in matches:
            print(f"\n=== {err_id} ===")
            print(f"\n{err_info['description']}")

            if "error_message" in err_info:
                print(f"\nError message: {err_info['error_message']}")

            if "solution" in err_info:
                print(f"\n✅ Solution: {err_info['solution']}")

            if "solutions" in err_info:
                print(f"\n✅ Solutions:")
                for sol in err_info["solutions"]:
                    print(f"  - {sol}")

            if "references" in err_info:
                print(f"\nSee also: {', '.join(err_info['references'])}")
    else:
        print(f"\nNo known error matching '{error_text}'")
        print("\nAvailable errors:")
        for err_id in errors:
            print(f"  - {err_id}")


def query_goal(kg: Dict[str, Any], goal_pattern: str) -> None:
    """Query recommended tactics for a goal pattern."""
    goals = kg.get("goal_to_tactic", {})

    # Search for matching goal pattern
    matches = []
    for goal_id, goal_info in goals.items():
        if goal_pattern.lower() in goal_info.get("pattern", "").lower() or \
           goal_pattern.lower() in goal_id.lower():
            matches.append((goal_id, goal_info))

    if matches:
        for goal_id, goal_info in matches:
            print(f"\n=== {goal_info['pattern']} ===")

            print(f"\n✅ Recommended tactics:")
            for tactic in goal_info.get("recommended_tactics", []):
                print(f"  - {tactic}")

            if "not_recommended" in goal_info:
                print(f"\n❌ Not recommended:")
                for tactic in goal_info["not_recommended"]:
                    print(f"  - {tactic}")

            if "references" in goal_info:
                print(f"\nSee patterns: {', '.join(goal_info['references'])}")
    else:
        print(f"\nNo goal pattern matching '{goal_pattern}'")
        print("\nAvailable goal patterns:")
        for goal_id, goal_info in goals.items():
            print(f"  - {goal_info['pattern']}")


def query_pattern(kg: Dict[str, Any], pattern_name: str) -> None:
    """Query a proof pattern."""
    patterns = kg.get("patterns", {})

    if pattern_name in patterns:
        info = patterns[pattern_name]
        print(f"\n=== {info['name']} ===")
        print(f"\n{info['description']}")

        print(f"\nSteps:")
        for i, step in enumerate(info["steps"], 1):
            print(f"  {i}. {step}")

        if "tactics_used" in info:
            print(f"\nTactics used: {', '.join(info['tactics_used'])}")

        if "requires" in info:
            print(f"\nRequires: {', '.join(info['requires'])}")

        if "examples" in info:
            print(f"\nExamples:")
            for ex in info["examples"]:
                print(f"  - {ex}")
    else:
        # Fuzzy search
        matches = [name for name in patterns if pattern_name.lower() in name.lower()]
        if matches:
            print(f"\nDid you mean: {', '.join(matches)}?")
        else:
            print(f"\nNo pattern found matching '{pattern_name}'")
            print("\nAvailable patterns:")
            for pat_id in patterns:
                print(f"  - {pat_id}")


def list_all_tactics(kg: Dict[str, Any]) -> None:
    """List all available tactics."""
    tactics = kg.get("tactics", {})
    print("\n=== Available Tactics ===\n")
    for tactic_name, info in tactics.items():
        desc = info.get("description", "")
        print(f"  {tactic_name:20s} - {desc[:60]}")


def generate_graphviz(kg: Dict[str, Any]) -> str:
    """Generate Graphviz DOT format for visualization."""
    lines = ["digraph ProofStrategies {"]
    lines.append('  rankdir=LR;')
    lines.append('  node [shape=box];')
    lines.append('')

    # Tactics
    lines.append('  subgraph cluster_tactics {')
    lines.append('    label="Tactics";')
    lines.append('    style=filled;')
    lines.append('    color=lightgrey;')
    for tactic_id in kg.get("tactics", {}):
        lines.append(f'    "{tactic_id}" [color=blue];')
    lines.append('  }')
    lines.append('')

    # Patterns
    lines.append('  subgraph cluster_patterns {')
    lines.append('    label="Patterns";')
    lines.append('    style=filled;')
    lines.append('    color=lightblue;')
    for pattern_id in kg.get("patterns", {}):
        lines.append(f'    "{pattern_id}" [color=green];')
    lines.append('  }')
    lines.append('')

    # Lemma dependencies
    lines.append('  subgraph cluster_lemmas {')
    lines.append('    label="Lemmas";')
    lines.append('    style=filled;')
    lines.append('    color=lightyellow;')
    for lemma_id in kg.get("lemma_dependencies", {}):
        lines.append(f'    "{lemma_id}" [color=orange];')
    lines.append('  }')
    lines.append('')

    # Edges: patterns use tactics
    for pattern_id, pattern_info in kg.get("patterns", {}).items():
        for tactic in pattern_info.get("tactics_used", []):
            lines.append(f'  "{pattern_id}" -> "tactic:{tactic}" [label="uses"];')

    # Edges: lemmas depend on other lemmas
    for lemma_id, lemma_info in kg.get("lemma_dependencies", {}).items():
        for dep in lemma_info.get("depends_on", []):
            lines.append(f'  "{lemma_id}" -> "{dep}" [label="depends on"];')
        if "pattern" in lemma_info:
            lines.append(f'  "{lemma_id}" -> "{lemma_info["pattern"]}" [label="follows"];')

    lines.append("}")
    return "\n".join(lines)


def main():
    parser = argparse.ArgumentParser(description="Query proof strategy knowledge graph")
    parser.add_argument("--tactic", help="Query a tactic")
    parser.add_argument("--error", help="Query a common error")
    parser.add_argument("--goal", help="Query tactics for a goal pattern")
    parser.add_argument("--pattern", help="Query a proof pattern")
    parser.add_argument("--list-tactics", action="store_true", help="List all tactics")
    parser.add_argument("--graphviz", action="store_true", help="Generate Graphviz DOT format")
    parser.add_argument("--kg-path", type=Path, default=Path(__file__).parent / "proof-strategy-graph.json",
                       help="Path to knowledge graph JSON")

    args = parser.parse_args()

    kg = load_knowledge_graph(args.kg_path)

    if args.tactic:
        query_tactic(kg, args.tactic)
    elif args.error:
        query_error(kg, args.error)
    elif args.goal:
        query_goal(kg, args.goal)
    elif args.pattern:
        query_pattern(kg, args.pattern)
    elif args.list_tactics:
        list_all_tactics(kg)
    elif args.graphviz:
        print(generate_graphviz(kg))
    else:
        parser.print_help()


if __name__ == "__main__":
    main()
