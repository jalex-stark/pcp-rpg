"""Tools for running Lean/Lake commands and parsing output."""

import subprocess
from pathlib import Path
from typing import Tuple, Optional


def lake_build(
    unit_dir: Path, timeout: int = 120
) -> Tuple[bool, str]:
    """
    Run 'lake build' in the unit directory.

    Args:
        unit_dir: Directory containing lakefile.toml (or parent)
        timeout: Timeout in seconds

    Returns:
        (success, output)
    """
    # Find project root (where lakefile.toml is)
    project_root = unit_dir
    while project_root != project_root.parent:
        if (project_root / "lakefile.toml").exists():
            break
        project_root = project_root.parent

    if not (project_root / "lakefile.toml").exists():
        return False, "lakefile.toml not found"

    # Use ~/.elan/bin/lake if lake not in PATH
    lake_cmd = "lake"
    elan_lake = Path.home() / ".elan" / "bin" / "lake"
    if elan_lake.exists():
        lake_cmd = str(elan_lake)

    try:
        result = subprocess.run(
            [lake_cmd, "build"],
            cwd=project_root,
            capture_output=True,
            text=True,
            timeout=timeout,
        )
        return result.returncode == 0, result.stdout + result.stderr
    except subprocess.TimeoutExpired:
        return False, f"Timeout after {timeout}s"
    except FileNotFoundError:
        return False, "lake command not found"


def lake_env_lean(
    lean_file: Path, timeout: int = 60
) -> Tuple[bool, str]:
    """
    Run 'lake env lean <file>' to check a single file.

    Args:
        lean_file: Path to .lean file
        timeout: Timeout in seconds

    Returns:
        (success, output)
    """
    # Find project root
    project_root = lean_file.parent
    while project_root != project_root.parent:
        if (project_root / "lakefile.toml").exists():
            break
        project_root = project_root.parent

    if not (project_root / "lakefile.toml").exists():
        return False, "lakefile.toml not found"

    # Use ~/.elan/bin/lake if lake not in PATH
    lake_cmd = "lake"
    elan_lake = Path.home() / ".elan" / "bin" / "lake"
    if elan_lake.exists():
        lake_cmd = str(elan_lake)

    try:
        result = subprocess.run(
            [lake_cmd, "env", "lean", str(lean_file)],
            cwd=project_root,
            capture_output=True,
            text=True,
            timeout=timeout,
        )
        return result.returncode == 0, result.stdout + result.stderr
    except subprocess.TimeoutExpired:
        return False, f"Timeout after {timeout}s"
    except FileNotFoundError:
        return False, "lake command not found"


def parse_lean_errors(output: str) -> list[dict]:
    """
    Parse Lean error messages from output.

    Args:
        output: stdout/stderr from lake/lean

    Returns:
        List of dicts with keys: 'file', 'line', 'col', 'message'
    """
    errors = []

    # Pattern: <file>:<line>:<col>: error: <message>
    import re

    error_pattern = re.compile(
        r"^([^:]+):(\d+):(\d+):\s*error:\s*(.*)$", re.MULTILINE
    )

    for match in error_pattern.finditer(output):
        errors.append(
            {
                "file": match.group(1),
                "line": int(match.group(2)),
                "col": int(match.group(3)),
                "message": match.group(4).strip(),
            }
        )

    return errors


if __name__ == "__main__":
    # Test lean_runner
    import sys

    if len(sys.argv) < 2:
        print("Usage: python -m orchestrator.tools.lean_runner <file.lean or dir>")
        sys.exit(1)

    path = Path(sys.argv[1])

    if path.is_file():
        print(f"Checking {path}...")
        success, output = lake_env_lean(path)
        print(f"Success: {success}")
        if not success:
            print(f"\nOutput:\n{output}")
            errors = parse_lean_errors(output)
            print(f"\nParsed {len(errors)} errors:")
            for err in errors:
                print(f"  {err['file']}:{err['line']}:{err['col']} - {err['message']}")
    else:
        print(f"Building {path}...")
        success, output = lake_build(path)
        print(f"Success: {success}")
        if not success:
            print(f"\nOutput:\n{output}")
