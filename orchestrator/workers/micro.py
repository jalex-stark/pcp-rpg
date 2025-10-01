"""
Micro-tactic worker: fast rewrites, simp, aesop.

Profile 0 baseline - deterministic, no ML dependencies.
"""

import asyncio
from typing import Optional
from ..scheduler import Goal, Result, StrategyType
from .dojo import DojoWrapper


# Global dojo instance cache
_dojo: Optional[DojoWrapper] = None


async def get_dojo() -> DojoWrapper:
    """Get or create the global DojoWrapper instance."""
    global _dojo
    if _dojo is None:
        _dojo = DojoWrapper()
    return _dojo


async def run_micro(goal: Goal, timeout: float = 8.0) -> Result:
    """
    Run quick tactic enumeration (simp, rw, aesop, ring, linarith).

    Tries deterministic tactics in sequence using LeanDojo:
    - rfl (reflexivity)
    - simp (simplifier)
    - simp [*] (with hypotheses)
    - aesop (automation)
    - ring (ring normalization)
    - omega (linear arithmetic)
    - linarith (linear arithmetic)
    - decide (decision procedures)

    Args:
        goal: Goal to solve
        timeout: Max seconds to try

    Returns:
        Result with success status and tactics used
    """
    start_time = asyncio.get_event_loop().time()

    # Tactics to try in order (fast → slower)
    tactics_to_try = [
        "rfl",
        "simp",
        "simp [*]",
        "aesop",
        "ring",
        "omega",
        "linarith",
        "decide",
        "simp_all; aesop",
    ]

    dojo = await get_dojo()
    per_tactic_timeout = timeout / len(tactics_to_try)

    for tactic in tactics_to_try:
        # Check global timeout
        elapsed = asyncio.get_event_loop().time() - start_time
        if elapsed >= timeout:
            break

        try:
            result = await asyncio.wait_for(
                dojo.run_tac(
                    theorem_file=goal.metadata.get("file_path", ""),
                    theorem_name=goal.id,
                    state=0,  # Initial state
                    tactic=tactic,
                    tactic_timeout=per_tactic_timeout,
                ),
                timeout=per_tactic_timeout,
            )

            if result.success:
                elapsed = asyncio.get_event_loop().time() - start_time
                return Result(
                    success=True,
                    strategy=StrategyType.MICRO,
                    tactics=[tactic],
                    time_seconds=elapsed,
                )

        except asyncio.TimeoutError:
            continue
        except Exception as e:
            # Log error but continue trying other tactics
            continue

    elapsed = asyncio.get_event_loop().time() - start_time
    return Result(
        success=False,
        strategy=StrategyType.MICRO,
        tactics=[],
        time_seconds=elapsed,
        error="No micro-tactic succeeded",
    )
