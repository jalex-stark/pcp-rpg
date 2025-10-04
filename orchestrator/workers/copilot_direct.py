"""
Direct LeanCopilot worker - bypasses LeanDojo tracing.

Instead of using LeanDojo to invoke tactics on existing theorems,
this worker creates temporary .lean files with search_proof calls
and compiles them directly.

This allows automated proof search on theorems with 'sorry' bodies.
"""

import asyncio
import subprocess
import tempfile
from pathlib import Path
from typing import Optional
import re

from ..scheduler import Goal, Result, StrategyType


async def run_copilot_direct(goal: Goal, timeout: float = 30.0) -> Result:
    """
    Run LeanCopilot proof search without LeanDojo tracing.

    Creates a temporary .lean file with the theorem and search_proof tactic,
    then compiles it to see if a proof is found.

    Args:
        goal: Goal to solve
        timeout: Max seconds to search

    Returns:
        Result with proof script if found
    """
    start_time = asyncio.get_event_loop().time()

    # Get theorem info from goal metadata
    theorem_name = goal.metadata.get("theorem_name", goal.id)
    file_path = goal.metadata.get("file_path", "PCP/Basic.lean")

    # Extract context and goal text
    context = goal.context if goal.context else []
    goal_text = goal.text

    # Build theorem statement
    context_str = " ".join(context)
    if context_str:
        theorem_decl = f"theorem {theorem_name} {context_str} : {goal_text} := by"
    else:
        theorem_decl = f"theorem {theorem_name} : {goal_text} := by"

    # Create temp file with search_proof
    temp_content = f"""import LeanCopilot
import Mathlib.Tactic

{theorem_decl}
  search_proof (beam := 4) (temperature := 0.2) (maxSteps := 20)
"""

    try:
        # Write to temp file
        with tempfile.NamedTemporaryFile(
            mode='w',
            suffix='.lean',
            dir='.',
            delete=False
        ) as f:
            temp_path = Path(f.name)
            f.write(temp_content)

        # Set library path for LeanCopilot
        env = {
            **subprocess.os.environ,
            'DYLD_LIBRARY_PATH': '.lake/packages/LeanCopilot/.lake/build/lib'
        }

        # Compile with lake
        proc = await asyncio.create_subprocess_exec(
            'lake', 'build', temp_path.stem,
            stdout=asyncio.subprocess.PIPE,
            stderr=asyncio.subprocess.PIPE,
            env=env
        )

        try:
            stdout, stderr = await asyncio.wait_for(
                proc.communicate(),
                timeout=timeout
            )

            output = stdout.decode() + stderr.decode()

            # Check if proof was found
            if proc.returncode == 0:
                # Parse the proof from output
                proof = _extract_proof_from_output(output)
                if proof:
                    elapsed = asyncio.get_event_loop().time() - start_time
                    return Result(
                        success=True,
                        strategy=StrategyType.COPILOT,
                        tactics=[proof],
                        time_seconds=elapsed,
                    )

            # Failed to find proof
            elapsed = asyncio.get_event_loop().time() - start_time
            return Result(
                success=False,
                strategy=StrategyType.COPILOT,
                tactics=[],
                time_seconds=elapsed,
                error="search_proof failed to find proof"
            )

        except asyncio.TimeoutError:
            proc.kill()
            await proc.wait()
            elapsed = asyncio.get_event_loop().time() - start_time
            return Result(
                success=False,
                strategy=StrategyType.COPILOT,
                tactics=[],
                time_seconds=elapsed,
                error="Timeout"
            )

    except Exception as e:
        elapsed = asyncio.get_event_loop().time() - start_time
        return Result(
            success=False,
            strategy=StrategyType.COPILOT,
            tactics=[],
            time_seconds=elapsed,
            error=f"Exception: {e}"
        )
    finally:
        # Cleanup temp file
        if temp_path.exists():
            temp_path.unlink()


def _extract_proof_from_output(output: str) -> Optional[str]:
    """
    Extract the proof script from LeanCopilot search output.

    LeanCopilot prints the found proof to stdout/info messages.

    Args:
        output: Combined stdout/stderr from compilation

    Returns:
        Proof string if found, None otherwise
    """
    # Look for proof in info messages
    # Format: "info: Try this: <proof>"
    match = re.search(r'info:.*Try this:\s*(.+?)(?:\n|$)', output, re.DOTALL)
    if match:
        proof = match.group(1).strip()
        return proof

    return None


async def run_copilot_suggest(goal: Goal, timeout: float = 10.0) -> Result:
    """
    Run LeanCopilot suggest_tactics to get tactic suggestions.

    Similar to run_copilot_direct but uses suggest_tactics instead
    of full proof search (faster, for getting hints).

    Args:
        goal: Goal to solve
        timeout: Max seconds

    Returns:
        Result with suggested tactics
    """
    start_time = asyncio.get_event_loop().time()

    theorem_name = goal.metadata.get("theorem_name", goal.id)
    context = goal.context if goal.context else []
    goal_text = goal.text

    context_str = " ".join(context)
    if context_str:
        theorem_decl = f"theorem {theorem_name} {context_str} : {goal_text} := by"
    else:
        theorem_decl = f"theorem {theorem_name} : {goal_text} := by"

    temp_content = f"""import LeanCopilot
import Mathlib.Tactic

{theorem_decl}
  suggest_tactics
  sorry
"""

    try:
        with tempfile.NamedTemporaryFile(
            mode='w',
            suffix='.lean',
            dir='.',
            delete=False
        ) as f:
            temp_path = Path(f.name)
            f.write(temp_content)

        env = {
            **subprocess.os.environ,
            'DYLD_LIBRARY_PATH': '.lake/packages/LeanCopilot/.lake/build/lib'
        }

        proc = await asyncio.create_subprocess_exec(
            'lake', 'build', temp_path.stem,
            stdout=asyncio.subprocess.PIPE,
            stderr=asyncio.subprocess.PIPE,
            env=env
        )

        try:
            stdout, stderr = await asyncio.wait_for(
                proc.communicate(),
                timeout=timeout
            )

            output = stdout.decode() + stderr.decode()

            # Extract suggestions from output
            suggestions = _extract_suggestions(output)

            elapsed = asyncio.get_event_loop().time() - start_time

            if suggestions:
                return Result(
                    success=False,  # Not a complete proof
                    strategy=StrategyType.COPILOT,
                    tactics=suggestions,
                    time_seconds=elapsed,
                    error="Suggestions only (not complete proof)"
                )
            else:
                return Result(
                    success=False,
                    strategy=StrategyType.COPILOT,
                    tactics=[],
                    time_seconds=elapsed,
                    error="No suggestions found"
                )

        except asyncio.TimeoutError:
            proc.kill()
            await proc.wait()
            elapsed = asyncio.get_event_loop().time() - start_time
            return Result(
                success=False,
                strategy=StrategyType.COPILOT,
                tactics=[],
                time_seconds=elapsed,
                error="Timeout"
            )

    except Exception as e:
        elapsed = asyncio.get_event_loop().time() - start_time
        return Result(
            success=False,
            strategy=StrategyType.COPILOT,
            tactics=[],
            time_seconds=elapsed,
            error=f"Exception: {e}"
        )
    finally:
        if temp_path.exists():
            temp_path.unlink()


def _extract_suggestions(output: str) -> list[str]:
    """Extract tactic suggestions from suggest_tactics output."""
    suggestions = []

    # Look for suggestion lines
    for match in re.finditer(r'info:.*?([a-z_]+(?:\s+[a-z_]+)*)', output):
        tactic = match.group(1).strip()
        if tactic and tactic not in ['sorry', 'by', 'theorem']:
            suggestions.append(tactic)

    return suggestions[:5]  # Top 5 suggestions


# Simplified functions for command-line use

async def suggest_tactics_direct(
    file_path: str,
    theorem_name: str,
    num_suggestions: int = 5,
    timeout: float = 10.0
) -> list[str]:
    """
    Get tactic suggestions from LeanCopilot for a specific theorem.

    This reads the file, finds the theorem, and tries to compile it
    with suggest_tactics to get hints.

    Args:
        file_path: Path to .lean file (e.g., "PCP/ConstraintGraph/Defs.lean")
        theorem_name: Name of theorem to get suggestions for
        num_suggestions: Number of suggestions to request
        timeout: Timeout in seconds

    Returns:
        List of suggested tactics
    """
    # For now, return empty list - proper implementation would require
    # parsing the .lean file and extracting the theorem's goal state
    return []


async def search_proof_direct(
    file_path: str,
    theorem_name: str,
    beam: int = 4,
    max_steps: int = 20,
    timeout: float = 30.0
) -> Optional[str]:
    """
    Run LeanCopilot's search_proof tactic on a theorem.

    This attempts to prove a theorem by temporarily replacing its body
    with `by search_proof` and checking if Lean accepts it.

    Args:
        file_path: Path to .lean file
        theorem_name: Name of theorem to prove
        beam: Beam width for search
        max_steps: Maximum proof steps
        timeout: Timeout in seconds

    Returns:
        Proof script if found, None otherwise
    """
    # Read the file
    with open(file_path, 'r') as f:
        content = f.read()

    # Check if LeanCopilot is already imported
    has_copilot = 'import LeanCopilot' in content

    # Find the theorem - simple regex approach
    theorem_pattern = rf'(theorem|lemma)\s+{re.escape(theorem_name)}\s'
    if not re.search(theorem_pattern, content):
        return None

    # Create modified content with search_proof
    lines = content.split('\n')

    # Add LeanCopilot import if needed
    if not has_copilot:
        # Find first import line
        import_idx = 0
        for i, line in enumerate(lines):
            if line.startswith('import '):
                import_idx = i + 1
        lines.insert(import_idx, 'import LeanCopilot')

    # Find the theorem and replace proof with search_proof
    new_lines = []
    in_target_theorem = False
    theorem_indent = 0

    for line in lines:
        if f'theorem {theorem_name}' in line or f'lemma {theorem_name}' in line:
            in_target_theorem = True
            theorem_indent = len(line) - len(line.lstrip())
            new_lines.append(line)
            # Add search_proof on next line
            indent = ' ' * (theorem_indent + 2)
            search_tactic = f"search_proof (beam := {beam}) (maxSteps := {max_steps})"
            new_lines.append(f"{indent}{search_tactic}")
            continue

        if in_target_theorem:
            # Skip lines until we're out of the theorem body
            current_indent = len(line) - len(line.lstrip()) if line.strip() else theorem_indent + 2

            # Check if we're back to top-level
            if current_indent <= theorem_indent and line.strip() and not line.strip().startswith('--'):
                in_target_theorem = False
                new_lines.append(line)
        else:
            new_lines.append(line)

    # Write to temporary file
    temp_file = Path(file_path).parent / f".{Path(file_path).stem}_copilot_temp.lean"

    try:
        with open(temp_file, 'w') as f:
            f.write('\n'.join(new_lines))

        # Set library path
        env = {
            **subprocess.os.environ,
            'DYLD_LIBRARY_PATH': '.lake/packages/LeanCopilot/.lake/build/lib'
        }

        # Try to build it
        proc = await asyncio.create_subprocess_exec(
            'lake', 'build', str(temp_file.relative_to(Path.cwd())),
            stdout=asyncio.subprocess.PIPE,
            stderr=asyncio.subprocess.PIPE,
            env=env,
            cwd=str(Path.cwd())
        )

        try:
            stdout, stderr = await asyncio.wait_for(
                proc.communicate(),
                timeout=timeout
            )

            output = stdout.decode() + stderr.decode()

            if proc.returncode == 0:
                # Success! Check if there's a proof suggestion
                proof = _extract_proof_from_output(output)
                if proof:
                    return proof
                # Otherwise return the search_proof tactic itself
                return f"search_proof (beam := {beam}) (maxSteps := {max_steps})"
            else:
                return None

        except asyncio.TimeoutError:
            proc.kill()
            await proc.wait()
            return None

    except Exception:
        return None
    finally:
        # Clean up temp file
        if temp_file.exists():
            temp_file.unlink()
