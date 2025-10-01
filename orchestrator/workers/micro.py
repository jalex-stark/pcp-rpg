"""
Micro-tactic worker: fast rewrites, simp, aesop.

Profile 0 baseline - deterministic, no ML dependencies.
"""

import asyncio
import random
from ..scheduler import Goal, Result, StrategyType


async def run_micro(goal: Goal, timeout: float = 8.0) -> Result:
    """
    Run quick tactic enumeration (simp, rw, aesop, ring, linarith).

    This is a stub implementation. In production, this would:
    1. Use LeanDojo to execute tactics
    2. Try common patterns: simp_all, aesop?, ring, omega, linarith
    3. Cache successful tactic templates
    4. Return normalized proof scripts

    Args:
        goal: Goal to solve
        timeout: Max seconds to try

    Returns:
        Result with success status and tactics used
    """
    start = asyncio.get_event_loop().time()

    # Simulate micro-tactic search
    await asyncio.sleep(min(0.1 + random.random() * 0.3, timeout))

    elapsed = asyncio.get_event_loop().time() - start

    # Stub: simulate success for easy goals
    difficulty = goal.estimated_difficulty
    success_prob = max(0.1, 0.8 - difficulty)

    success = random.random() < success_prob

    if success:
        # Simulate finding a short tactic sequence
        tactics = ["simp [*]", "aesop"]
        return Result(
            success=True,
            strategy=StrategyType.MICRO,
            tactics=tactics,
            time_seconds=elapsed,
        )
    else:
        return Result(
            success=False,
            strategy=StrategyType.MICRO,
            tactics=[],
            time_seconds=elapsed,
            error="No micro-tactic succeeded",
        )


# For integration: real implementation would look like:
# async def run_micro_real(goal: Goal, dojo, timeout: float = 8.0) -> Result:
#     """Real implementation using LeanDojo."""
#     tactics_to_try = [
#         "simp_all",
#         "aesop?",
#         "ring",
#         "omega",
#         "linarith",
#         "simp [*]; aesop",
#     ]
#
#     for tactic in tactics_to_try:
#         try:
#             result = await asyncio.wait_for(
#                 dojo.run_tac(goal.id, tactic),
#                 timeout=timeout / len(tactics_to_try)
#             )
#             if result.success:
#                 return Result(
#                     success=True,
#                     strategy=StrategyType.MICRO,
#                     tactics=[tactic],
#                     ...
#                 )
#         except asyncio.TimeoutError:
#             continue
#
#     return Result(success=False, ...)
