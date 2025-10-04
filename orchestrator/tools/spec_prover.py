"""Wrapper around specialized provers (Copilot, LeanDojo)."""

import subprocess
import json
from pathlib import Path
from typing import Dict


def prove_lemmas(
    unit_dir: Path,
    lemma_names: list[str],
    prover: str = "copilot",
    timeout: int = 30,
) -> Dict[str, bool]:
    """
    Prove a list of top-level lemmas using the specialized prover.

    Args:
        unit_dir: Directory containing the unit files
        lemma_names: List of lemma names to prove
        prover: Which prover to use ('copilot', 'leandojo', 'tactics')
        timeout: Timeout per lemma in seconds

    Returns:
        Dictionary mapping lemma_name -> success (bool)
    """
    results = {}

    if prover == "copilot":
        return prove_with_copilot(unit_dir, lemma_names, timeout)
    elif prover == "leandojo":
        return prove_with_leandojo(unit_dir, lemma_names, timeout)
    elif prover == "tactics":
        return prove_with_tactics(unit_dir, lemma_names, timeout)
    else:
        raise ValueError(f"Unknown prover: {prover}")


def prove_with_copilot(
    unit_dir: Path, lemma_names: list[str], timeout: int
) -> Dict[str, bool]:
    """
    Prove lemmas using Lean Copilot (bin/copilot-prove).

    This calls bin/copilot-prove which should accept:
      --file <path>
      --lemma <name>
      --timeout <seconds>

    Returns 0 on success, non-zero on failure.
    """
    results = {}
    copilot_bin = Path(__file__).parent.parent.parent / "bin" / "copilot-prove"

    # Find lean files in unit_dir
    lean_files = list(unit_dir.glob("*.lean"))
    if not lean_files:
        # No files found
        for name in lemma_names:
            results[name] = False
        return results

    for lemma_name in lemma_names:
        # Try to find which file contains this lemma
        file_found = None
        for lean_file in lean_files:
            content = lean_file.read_text()
            if f"lemma {lemma_name}" in content:
                file_found = lean_file
                break

        if not file_found:
            results[lemma_name] = False
            continue

        # Call copilot-prove
        try:
            result = subprocess.run(
                [
                    str(copilot_bin),
                    "--file",
                    str(file_found),
                    "--lemma",
                    lemma_name,
                    "--timeout",
                    str(timeout),
                ],
                capture_output=True,
                text=True,
                timeout=timeout + 5,
                cwd=unit_dir.parent.parent.parent,  # Project root
            )
            results[lemma_name] = result.returncode == 0
        except (subprocess.TimeoutExpired, FileNotFoundError):
            results[lemma_name] = False

    return results


def prove_with_leandojo(
    unit_dir: Path, lemma_names: list[str], timeout: int
) -> Dict[str, bool]:
    """
    Prove lemmas using LeanDojo (bin/orch-lean).

    TODO: Implement LeanDojo integration.
    """
    # Placeholder
    results = {}
    for lemma_name in lemma_names:
        results[lemma_name] = False
    return results


def prove_with_tactics(
    unit_dir: Path, lemma_names: list[str], timeout: int
) -> Dict[str, bool]:
    """
    Prove lemmas by trying common tactics in sequence.

    This is a fallback prover that doesn't use ML models.
    """
    # Placeholder
    results = {}
    for lemma_name in lemma_names:
        results[lemma_name] = False
    return results


if __name__ == "__main__":
    # Test spec_prover
    import sys

    if len(sys.argv) < 2:
        print("Usage: python -m orchestrator.tools.spec_prover <unit_dir>")
        sys.exit(1)

    unit_dir = Path(sys.argv[1])

    # Find all lemmas
    from .index import top_level_lemmas

    lean_files = list(unit_dir.glob("*.lean"))
    all_lemmas = []
    for lean_file in lean_files:
        lemmas = top_level_lemmas(lean_file.read_text())
        all_lemmas.extend(lemmas)

    print(f"Found {len(all_lemmas)} lemmas: {all_lemmas}")

    # Try to prove them
    results = prove_lemmas(unit_dir, all_lemmas, prover="copilot")

    print("\nResults:")
    for lemma, success in results.items():
        status = "✓" if success else "✗"
        print(f"  {status} {lemma}")

    win_rate = sum(results.values()) / len(results) if results else 0.0
    print(f"\nWin rate: {win_rate:.1%}")
