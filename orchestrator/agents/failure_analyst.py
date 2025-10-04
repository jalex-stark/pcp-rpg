"""Failure analyst agent: Diagnoses proof failures and proposes fixes."""

import os
from pathlib import Path
from anthropic import Anthropic


def analyze_failures(
    file_contents: str,
    error_log: str,
    model: str = "claude-sonnet-4-5-20250929",
) -> dict:
    """
    Analyze proof failures and propose minimal fixes.

    Args:
        file_contents: Lean 4 code with failing proofs
        error_log: Lean error messages
        model: Claude model to use

    Returns:
        Dictionary with:
        - 'diagnosis': List of (error, diagnosis) pairs
        - 'fixes': List of proposed fixes (imports/attributes/aux lemmas)
        - 'justifications': Explanations for each fix
        - 'patch': Structured patch to apply
    """
    client = Anthropic(api_key=os.environ.get("ANTHROPIC_API_KEY"))

    # Load prompts
    playbooks_dir = Path(__file__).parent.parent.parent / "playbooks"
    system_prompt = (playbooks_dir / "prompts/system/failure_analyst.txt").read_text()
    user_template = (playbooks_dir / "prompts/failure_analyst/user.txt").read_text()

    # Substitute template variables
    user_prompt = user_template.replace("{{ERROR_LOG}}", error_log).replace(
        "{{FILE_CONTENTS}}", file_contents
    )

    # Call Claude
    response = client.messages.create(
        model=model,
        max_tokens=4000,
        temperature=0.0,
        system=system_prompt,
        messages=[{"role": "user", "content": user_prompt}],
    )

    analysis_text = response.content[0].text

    # Parse the response
    # For now, return structured dict (parsing can be improved)
    return {
        "diagnosis": [],
        "fixes": [],
        "justifications": [],
        "patch": analysis_text,  # Raw text patch for now
    }


def apply_patch(file_contents: str, patch: dict) -> str:
    """
    Apply a patch from failure analysis to file contents.

    Args:
        file_contents: Original Lean 4 code
        patch: Patch dictionary from analyze_failures

    Returns:
        Patched Lean 4 code
    """
    # TODO: Implement intelligent patching
    # For now, return original + patch as comment
    patch_text = patch.get("patch", "")
    return file_contents + "\n\n/- SUGGESTED FIXES:\n" + patch_text + "\n-/"


if __name__ == "__main__":
    # Test failure analyst
    import sys

    if len(sys.argv) < 3:
        print("Usage: python -m orchestrator.agents.failure_analyst <file.lean> <error.log>")
        sys.exit(1)

    file_path = Path(sys.argv[1])
    error_path = Path(sys.argv[2])

    file_contents = file_path.read_text()
    error_log = error_path.read_text()

    result = analyze_failures(file_contents, error_log)

    print("ANALYSIS:")
    print(result["patch"])
