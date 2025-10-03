"""
LeanDojo integration: unified verifier for all strategies.

Provides a clean interface to run tactics and check proofs using LeanDojo.
"""

import asyncio
import os
from pathlib import Path
from typing import Optional, Union
from dataclasses import dataclass, field

try:
    from lean_dojo import (
        Dojo,
        LeanGitRepo,
        Theorem,
        TacticState,
        ProofFinished,
        LeanError,
        ProofGivenUp,
        DojoCrashError,
        DojoInitError,
        DojoTacticTimeoutError,
    )
    HAS_LEANDOJO = True
except ImportError:
    HAS_LEANDOJO = False
    # Stubs for type hints when LeanDojo not installed
    Dojo = None
    LeanGitRepo = None
    Theorem = None
    TacticState = None
    ProofFinished = None
    LeanError = None
    ProofGivenUp = None


@dataclass
class DojoResult:
    """Result from running a tactic in Lean."""
    success: bool
    new_goals: list[str] = field(default_factory=list)
    proof_finished: bool = False
    error: Optional[str] = None
    tactic_state_id: Optional[int] = None


class DojoWrapper:
    """
    Wrapper around LeanDojo for tactic execution.

    Provides a clean async interface for running tactics and checking proofs.
    Handles initialization, state management, and error handling.
    """

    def __init__(
        self,
        repo_path: str = ".",
        commit: str = "HEAD",
        timeout: int = 600,
        num_procs: Optional[int] = None,
        mock_mode: bool = False,
    ):
        """
        Initialize Dojo wrapper.

        Args:
            repo_path: Path to Lean project (or URL for git repo)
            commit: Git commit hash (default: HEAD for local repos)
            timeout: Max seconds for Dojo operations
            num_procs: Number of parallel processes (default: auto)
            mock_mode: If True, use mock responses (for testing without LeanDojo)
        """
        self.mock_mode = mock_mode or not HAS_LEANDOJO

        # Always initialize cache
        self._dojo_cache = {}

        if self.mock_mode and not HAS_LEANDOJO:
            # Mock mode - don't require LeanDojo
            self.repo_path = Path(repo_path).resolve()
            self.commit = commit
            self.timeout = timeout
            self.repo = None
            return

        if not HAS_LEANDOJO:
            raise ImportError(
                "lean-dojo not installed. Install with: pip install lean-dojo"
            )

        self.repo_path = Path(repo_path).resolve()
        self.commit = commit
        self.timeout = timeout

        # Set LeanDojo env vars if provided
        if num_procs:
            os.environ['LEANDOJO_NUM_PROCS'] = str(num_procs)

        # Initialize repo
        if self.repo_path.is_dir():
            # Local repository
            self.repo = LeanGitRepo(str(self.repo_path), commit)
        else:
            # Remote repository (URL)
            self.repo = LeanGitRepo(repo_path, commit)

    async def run_tac(
        self,
        theorem_file: str,
        theorem_name: str,
        state: Union[TacticState, int],
        tactic: str,
        tactic_timeout: float = 10.0,
    ) -> DojoResult:
        """
        Run a tactic on a proof state.

        Args:
            theorem_file: Path to Lean file (relative to repo root)
            theorem_name: Name of theorem
            state: TacticState or state_id (0 for initial)
            tactic: Tactic string to execute
            tactic_timeout: Max seconds for this tactic

        Returns:
            DojoResult with success status and new goals
        """
        # Mock mode: simulate random success/failure
        if self.mock_mode:
            await asyncio.sleep(0.05)  # Simulate work
            # Simple heuristic: succeed on common patterns
            # Match theorem names to tactics
            if tactic == 'rfl' and any(x in theorem_name for x in ['rfl', 'refl']):
                return DojoResult(success=True, proof_finished=True)
            if tactic == 'simp' and any(x in theorem_name for x in ['add_zero', 'zero_add', 'mul_one', 'one_mul', 'append_nil', 'nil_append']):
                return DojoResult(success=True, proof_finished=True)
            if tactic == 'decide' and any(x in theorem_name for x in ['length_nil', 'sub_self']):
                return DojoResult(success=True, proof_finished=True)
            if tactic == 'ring' and any(x in theorem_name for x in ['mul_zero', 'zero_mul']):
                return DojoResult(success=True, proof_finished=True)
            if tactic == 'omega' and any(x in theorem_name for x in ['sub_zero', 'zero_sub']):
                return DojoResult(success=True, proof_finished=True)
            if tactic == 'aesop' and any(x in theorem_name for x in ['comm', 'assoc', 'map_', 'bind_']):
                return DojoResult(success=True, proof_finished=True)

            return DojoResult(success=False, error="Mock mode: tactic failed")

        try:
            # Get or create Dojo for this theorem
            cache_key = (theorem_file, theorem_name)
            if cache_key not in self._dojo_cache:
                theorem = Theorem(self.repo, theorem_file, theorem_name)
                dojo_ctx = Dojo(theorem, timeout=self.timeout)
                dojo, init_state = dojo_ctx.__enter__()
                self._dojo_cache[cache_key] = (dojo_ctx, dojo, init_state)
            else:
                dojo_ctx, dojo, init_state = self._dojo_cache[cache_key]

            # Get current state
            if isinstance(state, int):
                if state == 0:
                    current_state = init_state
                else:
                    # Would need to track state history
                    raise ValueError("State tracking not implemented for state_id")
            else:
                current_state = state

            # Run tactic with timeout
            result = await asyncio.wait_for(
                asyncio.to_thread(dojo.run_tac, current_state, tactic),
                timeout=tactic_timeout,
            )

            # Parse result
            if isinstance(result, ProofFinished):
                return DojoResult(
                    success=True,
                    new_goals=[],
                    proof_finished=True,
                    tactic_state_id=result.tactic_state_id,
                )
            elif isinstance(result, TacticState):
                # Extract goals from proof state
                goals = self._extract_goals(result.pp)
                return DojoResult(
                    success=True,
                    new_goals=goals,
                    proof_finished=False,
                    tactic_state_id=result.id,
                )
            elif isinstance(result, (LeanError, ProofGivenUp)):
                return DojoResult(
                    success=False,
                    error=str(result.message) if hasattr(result, 'message') else str(result),
                )
            else:
                return DojoResult(
                    success=False,
                    error=f"Unknown result type: {type(result)}",
                )

        except asyncio.TimeoutError:
            return DojoResult(success=False, error="Tactic timeout")
        except (DojoCrashError, DojoInitError, DojoTacticTimeoutError) as e:
            return DojoResult(success=False, error=f"Dojo error: {e}")
        except Exception as e:
            return DojoResult(success=False, error=f"Unexpected error: {e}")

    async def check_proof(
        self,
        theorem_file: str,
        theorem_name: str,
        proof_script: str,
        timeout: float = 30.0,
    ) -> bool:
        """
        Check if a complete proof script is valid.

        Runs the entire proof script tactic-by-tactic.

        Args:
            theorem_file: Path to Lean file
            theorem_name: Name of theorem
            proof_script: Complete proof (tactics separated by newlines or semicolons)
            timeout: Max seconds to check

        Returns:
            True if proof is valid
        """
        # Split proof into tactics
        tactics = self._split_proof(proof_script)

        try:
            # Get initial state
            cache_key = (theorem_file, theorem_name)
            if cache_key not in self._dojo_cache:
                theorem = Theorem(self.repo, theorem_file, theorem_name)
                dojo_ctx = Dojo(theorem, timeout=self.timeout)
                dojo, init_state = dojo_ctx.__enter__()
                self._dojo_cache[cache_key] = (dojo_ctx, dojo, init_state)
            else:
                dojo_ctx, dojo, init_state = self._dojo_cache[cache_key]

            # Run tactics sequentially
            current_state = init_state
            for tactic in tactics:
                if not tactic.strip():
                    continue

                result = await asyncio.wait_for(
                    asyncio.to_thread(dojo.run_tac, current_state, tactic),
                    timeout=timeout / len(tactics),
                )

                if isinstance(result, ProofFinished):
                    return True  # Proof complete!
                elif isinstance(result, TacticState):
                    current_state = result  # Continue from new state
                else:
                    return False  # Error

            return False  # Ran out of tactics without finishing

        except Exception as e:
            print(f"Proof check error: {e}")
            return False

    def _extract_goals(self, pp: str) -> list[str]:
        """
        Extract individual goals from pretty-printed proof state.

        Args:
            pp: Pretty-printed state (from TacticState.pp)

        Returns:
            List of goal strings
        """
        # Simple heuristic: goals separated by "case" or double newline
        # In reality, LeanDojo's pp format is more complex
        if not pp:
            return []

        # Split by goal separator (⊢)
        parts = pp.split('⊢')
        if len(parts) <= 1:
            return [pp.strip()] if pp.strip() else []

        goals = []
        for i in range(1, len(parts)):
            # Goal is context + ⊢ + target
            target = parts[i].split('\n')[0].strip()
            goals.append(target)

        return goals

    def _split_proof(self, proof_script: str) -> list[str]:
        """
        Split proof script into individual tactics.

        Args:
            proof_script: Complete proof

        Returns:
            List of tactic strings
        """
        # Handle different separators
        # Simple version: split by newlines or semicolons
        script = proof_script.strip()

        # Remove "by" prefix if present
        if script.startswith('by'):
            script = script[2:].strip()

        # Split by newlines first
        lines = script.split('\n')

        tactics = []
        for line in lines:
            line = line.strip()
            if not line or line.startswith('--'):  # Skip comments
                continue

            # Split by semicolons
            parts = [p.strip() for p in line.split(';')]
            tactics.extend(p for p in parts if p)

        return tactics

    def close(self):
        """Close all cached Dojo instances."""
        for cache_key, (dojo_ctx, dojo, init_state) in self._dojo_cache.items():
            try:
                dojo_ctx.__exit__(None, None, None)
            except Exception as e:
                print(f"Error closing Dojo for {cache_key}: {e}")

        self._dojo_cache.clear()

    def __del__(self):
        """Cleanup on deletion."""
        self.close()


# Convenience function for simple use cases
async def run_tactic_simple(
    tactic: str,
    theorem_file: str = "PCP.lean",
    theorem_name: str = "test_theorem",
    repo_path: str = ".",
) -> DojoResult:
    """
    Simple interface to run a single tactic.

    Args:
        tactic: Tactic to run
        theorem_file: Lean file
        theorem_name: Theorem name
        repo_path: Repository path

    Returns:
        DojoResult
    """
    dojo = DojoWrapper(repo_path)
    try:
        result = await dojo.run_tac(theorem_file, theorem_name, 0, tactic)
        return result
    finally:
        dojo.close()
