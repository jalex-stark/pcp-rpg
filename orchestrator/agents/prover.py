"""Prover agent: Completes lemma proofs with short tactics."""

import os
from pathlib import Path
from anthropic import Anthropic


def try_close_lemmas(
    file_contents: str,
    tactic_budget: int = 5,
    model: str = "claude-sonnet-4-5-20250929",
) -> tuple[str, list[str]]:
    """
    Try to close lemmas in a file with short, deterministic tactics.

    Args:
        file_contents: Lean 4 code with lemmas (may have sorries)
        tactic_budget: Max tactics per lemma proof
        model: Claude model to use

    Returns:
        (completed_code, errors)
        - completed_code: Lean 4 code with proofs filled in
        - errors: List of error messages (empty if successful)
    """
    client = Anthropic(api_key=os.environ.get("ANTHROPIC_API_KEY"))

    # Load prompts
    playbooks_dir = Path(__file__).parent.parent.parent / "playbooks"
    system_prompt = (playbooks_dir / "prompts/system/prover.txt").read_text()
    user_template = (playbooks_dir / "prompts/prover/user.txt").read_text()

    # Substitute template variables
    system_prompt = system_prompt.replace("{{tactic_budget}}", str(tactic_budget))
    user_prompt = user_template.replace("{{FILE_CONTENTS}}", file_contents).replace(
        "{{tactic_budget}}", str(tactic_budget)
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

    # TODO: Run lean to check for errors
    # For now, return empty error list
    errors = []

    return code.strip(), errors


if __name__ == "__main__":
    # Test prover
    import sys

    if len(sys.argv) < 2:
        print("Usage: python -m orchestrator.agents.prover <file.lean>")
        sys.exit(1)

    file_path = Path(sys.argv[1])
    file_contents = file_path.read_text()

    code, errors = try_close_lemmas(file_contents, tactic_budget=5)

    if errors:
        print("ERRORS:")
        for err in errors:
            print(f"  {err}")
        print()

    print(code)
