"""Tools for indexing Lean files (extracting lemma names, statements)."""

import re
from typing import List, Dict


# Regex to match top-level lemmas
LEMMA_RE = re.compile(r"^\s*lemma\s+([A-Za-z0-9_'\.]+)\b", re.MULTILINE)

# Regex to match lemma with statement (more detailed)
LEMMA_FULL_RE = re.compile(
    r"^\s*(?:@\[[^\]]+\]\s*)?lemma\s+([A-Za-z0-9_'\.]+)"
    r"(?:\s+\{[^}]+\}|\s+\([^)]+\)|\s+\[[^\]]+\])*\s*:\s*([^:=]+)",
    re.MULTILINE,
)


def top_level_lemmas(lean_text: str) -> List[str]:
    """
    Extract top-level lemma names from Lean code.

    Args:
        lean_text: Lean 4 source code

    Returns:
        List of lemma names
    """
    return LEMMA_RE.findall(lean_text)


def extract_lemma_info(lean_text: str) -> List[Dict[str, str]]:
    """
    Extract detailed lemma information from Lean code.

    Args:
        lean_text: Lean 4 source code

    Returns:
        List of dicts with keys: 'name', 'statement'
    """
    lemmas = []

    # Try to match full lemmas (name + statement)
    matches = LEMMA_FULL_RE.findall(lean_text)
    for name, statement in matches:
        lemmas.append({"name": name.strip(), "statement": statement.strip()})

    # Fallback: just names
    if not lemmas:
        names = top_level_lemmas(lean_text)
        lemmas = [{"name": name, "statement": "?"} for name in names]

    return lemmas


def count_tactics(proof_text: str) -> int:
    """
    Count the number of tactic lines in a proof.

    Args:
        proof_text: The proof body (between 'by' and end)

    Returns:
        Number of tactic lines (heuristic)
    """
    # Simple heuristic: count non-empty, non-comment lines
    lines = proof_text.split("\n")
    count = 0
    for line in lines:
        stripped = line.strip()
        if stripped and not stripped.startswith("--") and not stripped.startswith("/-"):
            count += 1
    return count


def extract_proof_body(lean_text: str, lemma_name: str) -> str:
    """
    Extract the proof body for a specific lemma.

    Args:
        lean_text: Lean 4 source code
        lemma_name: Name of the lemma

    Returns:
        Proof body text (between 'by' and next lemma/end)
    """
    # Find lemma declaration
    pattern = rf"lemma\s+{re.escape(lemma_name)}\b.*?:=\s*by\s*(.*?)(?=\n\s*lemma|\n\s*theorem|\n\s*def|\n\s*end\s+|\Z)"
    match = re.search(pattern, lean_text, re.DOTALL)

    if match:
        return match.group(1).strip()
    else:
        return ""


if __name__ == "__main__":
    # Test indexing
    import sys
    from pathlib import Path

    if len(sys.argv) < 2:
        print("Usage: python -m orchestrator.tools.index <file.lean>")
        sys.exit(1)

    lean_file = Path(sys.argv[1])
    lean_text = lean_file.read_text()

    lemmas = extract_lemma_info(lean_text)

    print(f"Found {len(lemmas)} lemmas in {lean_file.name}:")
    for lem in lemmas:
        print(f"  - {lem['name']}: {lem['statement'][:60]}...")
