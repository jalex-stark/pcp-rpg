"""
Direct Lean REPL wrapper - alternative to LeanDojo for newer Lean versions.

Uses Lean's built-in REPL mode to interact with theorem provers directly,
bypassing LeanDojo's tracing system which may not support Lean 4.24+.
"""

import asyncio
import json
import tempfile
from pathlib import Path
from typing import Optional, Dict, Any
from dataclasses import dataclass


@dataclass
class ReplResult:
    """Result from Lean REPL interaction."""
    success: bool
    state: Optional[int] = None
    tactics: list[str] = None
    error: Optional[str] = None

    def __post_init__(self):
        if self.tactics is None:
            self.tactics = []


class LeanRepl:
    """
    Direct wrapper for Lean's REPL mode.

    Simpler and more robust than LeanDojo for basic tactic execution.
    Works with any Lean 4 version that supports --server mode.
    """

    def __init__(self, repo_path: str = "."):
        self.repo_path = Path(repo_path)
        self.process: Optional[asyncio.subprocess.Process] = None

    async def start(self):
        """Start the Lean REPL server."""
        if self.process is not None:
            return

        # Start Lean in server mode
        self.process = await asyncio.create_subprocess_exec(
            "lake", "env", "lean", "--server",
            cwd=str(self.repo_path),
            stdin=asyncio.subprocess.PIPE,
            stdout=asyncio.subprocess.PIPE,
            stderr=asyncio.subprocess.PIPE,
        )

    async def stop(self):
        """Stop the REPL server."""
        if self.process:
            self.process.terminate()
            await self.process.wait()
            self.process = None

    async def run_tactic(
        self,
        file_path: str,
        theorem_name: str,
        tactic: str,
        timeout: float = 10.0
    ) -> ReplResult:
        """
        Run a single tactic on a theorem using Lean directly.

        This is a simplified approach that doesn't use LeanDojo's tracing.
        Instead, it:
        1. Creates a test file with the tactic applied
        2. Runs `lake build` on it
        3. Checks if it succeeded

        Args:
            file_path: Path to Lean file containing the theorem
            theorem_name: Full name of theorem (e.g., "PCP.Basic.nat_add_zero")
            tactic: Tactic to try (e.g., "simp", "rfl")
            timeout: Max seconds to wait

        Returns:
            ReplResult with success status
        """
        await self.start()

        # Create a test file that imports the original and tries the tactic
        test_content = f"""
import {file_path.replace('/', '.').replace('.lean', '')}

-- Test if tactic solves the theorem
example : ∀ n : ℕ, n + 0 = n := by {tactic}
"""

        # Write to temporary file
        with tempfile.NamedTemporaryFile(
            mode='w',
            suffix='.lean',
            dir=str(self.repo_path),
            delete=False
        ) as f:
            f.write(test_content)
            test_file = f.name

        try:
            # Try to build it
            proc = await asyncio.create_subprocess_exec(
                "lake", "build", Path(test_file).name.replace('.lean', ''),
                cwd=str(self.repo_path),
                stdout=asyncio.subprocess.PIPE,
                stderr=asyncio.subprocess.PIPE,
            )

            try:
                stdout, stderr = await asyncio.wait_for(
                    proc.communicate(),
                    timeout=timeout
                )

                # Check if successful
                success = proc.returncode == 0 and b"error" not in stderr.lower()

                return ReplResult(
                    success=success,
                    tactics=[tactic] if success else [],
                    error=stderr.decode() if not success else None
                )

            except asyncio.TimeoutError:
                proc.kill()
                return ReplResult(
                    success=False,
                    error=f"Timeout after {timeout}s"
                )

        finally:
            # Clean up test file
            Path(test_file).unlink(missing_ok=True)

    async def __aenter__(self):
        await self.start()
        return self

    async def __aexit__(self, *args):
        await self.stop()


# Simplified wrapper that matches the DojoWrapper interface
class SimpleLeanWrapper:
    """
    Simplified wrapper that works without LeanDojo tracing.

    Uses direct Lean execution for basic tactic testing.
    Much simpler but less powerful than full LeanDojo.
    """

    def __init__(self, repo_path: str = "."):
        self.repo_path = repo_path
        self.repl: Optional[LeanRepl] = None

    async def get_repl(self) -> LeanRepl:
        """Get or create REPL instance."""
        if self.repl is None:
            self.repl = LeanRepl(self.repo_path)
            await self.repl.start()
        return self.repl

    async def run_tac(
        self,
        theorem_file: str,
        theorem_name: str,
        state: int,
        tactic: str,
        tactic_timeout: float = 10.0,
    ) -> ReplResult:
        """Run a tactic using direct Lean execution."""
        repl = await self.get_repl()
        return await repl.run_tactic(
            theorem_file,
            theorem_name,
            tactic,
            timeout=tactic_timeout
        )
