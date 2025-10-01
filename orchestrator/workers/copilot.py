"""
Lean Copilot worker: search_proof + select_premises.

Profile 1+ - requires Lean Copilot in lakefile.
"""

import asyncio
import random
from ..scheduler import Goal, Result, StrategyType


async def run_copilot(goal: Goal, timeout: float = 20.0) -> Result:
    """
    Run Lean Copilot search (select_premises + search_proof).

    This is a stub implementation. In production, this would:
    1. Use LeanDojo to invoke Copilot tactics inside Lean
    2. Call select_premises to get top-k relevant lemmas
    3. Call search_proof with Aesop + LLM suggestions
    4. Replay found proof script and verify
    5. Return normalized proof

    Configuration (to be wired):
    - beam: 4
    - temperature: 0.2
    - max_steps: 20
    - Aesop: bestFirst, maxRuleApplications=80

    Args:
        goal: Goal to solve
        timeout: Max seconds to search

    Returns:
        Result with proof script if found
    """
    start = asyncio.get_event_loop().time()

    # Simulate Copilot search
    await asyncio.sleep(min(1.0 + random.random() * 2.0, timeout))

    elapsed = asyncio.get_event_loop().time() - start

    # Stub: better on medium difficulty
    difficulty = goal.estimated_difficulty
    success_prob = max(0.05, 0.6 - abs(difficulty - 0.5))

    success = random.random() < success_prob

    if success:
        # Simulate Copilot finding a proof
        tactics = ["select_premises", "search_proof"]
        return Result(
            success=True,
            strategy=StrategyType.COPILOT,
            tactics=tactics,
            time_seconds=elapsed,
        )
    else:
        return Result(
            success=False,
            strategy=StrategyType.COPILOT,
            tactics=[],
            time_seconds=elapsed,
            error="Copilot search exhausted",
        )


# Real implementation outline:
# async def run_copilot_real(goal: Goal, dojo, timeout: float = 20.0) -> Result:
#     """Real Copilot integration via LeanDojo."""
#     try:
#         # Step 1: Select premises
#         premises_tactic = "select_premises (num := 12)"
#         premises_result = await dojo.run_tac(goal.id, premises_tactic)
#
#         # Step 2: Run search_proof with config
#         search_tactic = (
#             "search_proof "
#             "(beam := 4) "
#             "(temperature := 0.2) "
#             "(maxSteps := 20)"
#         )
#         search_result = await asyncio.wait_for(
#             dojo.run_tac(goal.id, search_tactic),
#             timeout=timeout
#         )
#
#         if search_result.success:
#             return Result(
#                 success=True,
#                 strategy=StrategyType.COPILOT,
#                 tactics=[premises_tactic, search_tactic],
#                 time_seconds=...,
#             )
#
#     except asyncio.TimeoutError:
#         return Result(success=False, error="timeout", ...)
#
#     return Result(success=False, ...)
