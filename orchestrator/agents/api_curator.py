"""API curator agent: Curates stable lemmas into human-readable API files."""

import os
from pathlib import Path
from anthropic import Anthropic


def curate_api(
    namespace: str,
    slop_files: list[str],
    proven_lemmas: list[dict],
    module_comment: str = "",
    model: str = "claude-sonnet-4-5-20250929",
) -> str:
    """
    Curate an API.lean file from proven slop lemmas.

    Args:
        namespace: Lean namespace (e.g., "ConstraintGraph.Unit01")
        slop_files: List of slop file paths to import
        proven_lemmas: List of dicts with keys: 'name', 'statement', 'file'
        module_comment: High-level module guidance
        model: Claude model to use

    Returns:
        Lean 4 code for API.lean
    """
    client = Anthropic(api_key=os.environ.get("ANTHROPIC_API_KEY"))

    # Load prompts
    playbooks_dir = Path(__file__).parent.parent.parent / "playbooks"
    system_prompt = (playbooks_dir / "prompts/system/api_curator.txt").read_text()
    user_template = (playbooks_dir / "prompts/api_curator/user.txt").read_text()

    # Format proven lemmas
    lemmas_text = "\n".join(
        f"- {lem['name']}: {lem.get('statement', '?')} (from {lem.get('file', '?')})"
        for lem in proven_lemmas
    )

    # Substitute template variables
    user_prompt = (
        user_template.replace("{{NAMESPACE}}", namespace)
        .replace("{{SLOP_FILES}}", "\n".join(f"  - {f}" for f in slop_files))
        .replace("{{INDEX_OF_PROVEN_LEMMAS}}", lemmas_text)
        .replace("{{MODULE_COMMENT}}", module_comment)
    )

    # Call Claude
    response = client.messages.create(
        model=model,
        max_tokens=4000,
        temperature=0.0,
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
    # Test API curator
    import sys
    import yaml

    if len(sys.argv) < 2:
        print("Usage: python -m orchestrator.agents.api_curator <unit.yaml>")
        sys.exit(1)

    unit_path = Path(sys.argv[1])
    unit_cfg = yaml.safe_load(unit_path.read_text())

    # Mock proven lemmas
    proven_lemmas = [
        {"name": "satFrac_nonneg", "statement": "0 ≤ satFrac G σ", "file": "Slop_Bounds.lean"},
        {"name": "satFrac_le_one", "statement": "satFrac G σ ≤ 1", "file": "Slop_Bounds.lean"},
    ]

    code = curate_api(
        namespace=unit_cfg["namespace"],
        slop_files=unit_cfg.get("slop_files", ["Slop_1.lean"]),
        proven_lemmas=proven_lemmas,
        module_comment=unit_cfg.get("api_comment", ""),
    )

    print(code)
