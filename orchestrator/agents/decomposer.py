"""Decomposer agent: Breaks high-level specs into micro-lemmas."""

import os
from pathlib import Path
from anthropic import Anthropic


def decompose_spec(
    spec: str,
    imports: list[str],
    namespace: str,
    max_lemmas: int = 30,
    tactic_budget: int = 5,
    prefix: str = "",
    model: str = "claude-sonnet-4-5-20250929",
) -> str:
    """
    Decompose a high-level specification into AI slop lemma file.

    Args:
        spec: High-level specification (what to prove)
        imports: List of Mathlib/PCP imports
        namespace: Lean namespace for lemmas
        max_lemmas: Maximum number of lemmas to generate
        tactic_budget: Max tactics per lemma proof
        prefix: Name prefix for lemmas (default: derived from namespace)
        model: Claude model to use

    Returns:
        Lean 4 code (string) with lemma statements (proofs may be sorries)
    """
    client = Anthropic(api_key=os.environ.get("ANTHROPIC_API_KEY"))

    # Load prompts
    playbooks_dir = Path(__file__).parent.parent.parent / "playbooks"
    system_prompt = (playbooks_dir / "prompts/system/decomposer.txt").read_text()
    user_template = (playbooks_dir / "prompts/decomposer/user.txt").read_text()

    # Substitute template variables
    system_prompt = system_prompt.replace("{{tactic_budget}}", str(tactic_budget))

    if not prefix:
        prefix = namespace.split(".")[-1].lower()

    user_prompt = (
        user_template.replace("{{SPEC}}", spec)
        .replace("{{IMPORTS}}", "\n".join(f"  - {imp}" for imp in imports))
        .replace("{{NAMESPACE}}", namespace)
        .replace("{{MAX_LEMMAS}}", str(max_lemmas))
        .replace("{{tactic_budget}}", str(tactic_budget))
        .replace("{{PREFIX}}", prefix)
    )

    # Call Claude
    response = client.messages.create(
        model=model,
        max_tokens=8000,
        temperature=0.0,  # Deterministic
        system=system_prompt,
        messages=[{"role": "user", "content": user_prompt}],
    )

    code = response.content[0].text

    # Clean up markdown fences if present
    if code.startswith("```lean"):
        code = code[7:]
    if code.startswith("```"):
        code = code[3:]
    if code.endswith("```"):
        code = code[:-3]

    return code.strip()


if __name__ == "__main__":
    # Test decomposer
    import sys
    import yaml

    if len(sys.argv) < 2:
        print("Usage: python -m orchestrator.agents.decomposer <unit.yaml>")
        sys.exit(1)

    unit_path = Path(sys.argv[1])
    unit_cfg = yaml.safe_load(unit_path.read_text())

    code = decompose_spec(
        spec=unit_cfg["spec"],
        imports=unit_cfg["imports"],
        namespace=unit_cfg["namespace"],
        max_lemmas=unit_cfg.get("max_lemmas", 30),
        tactic_budget=unit_cfg.get("tactic_budget", 5),
    )

    print(code)
