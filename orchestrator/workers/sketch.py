"""
Sketch validation worker: LLM-based proof plan validation.

Uses local/remote LLM to check if a proof approach is viable before
committing expensive compute to formal search.
"""

import asyncio
import random
from ..scheduler import Goal, Result, StrategyType


async def run_sketch(goal: Goal, timeout: float = 6.0) -> Result:
    """
    Validate proof sketch with LLM before deep search.

    This is a stub implementation. In production, this would:
    1. Send goal + context to Claude/local LLM
    2. Ask for proof outline and type-level feasibility check
    3. Parse sketch for missing lemmas or typeclass issues
    4. Return validation result (opens lemma requests if needed)
    5. Used as a cheap filter before expensive strategies

    Args:
        goal: Goal to validate
        timeout: Max seconds for LLM call

    Returns:
        Result indicating whether sketch looks viable
    """
    start = asyncio.get_event_loop().time()

    # Simulate sketch validation
    await asyncio.sleep(min(0.5 + random.random() * 1.0, timeout))

    elapsed = asyncio.get_event_loop().time() - start

    # Stub: reasonable validation for most goals
    success_prob = 0.7

    success = random.random() < success_prob

    if success:
        return Result(
            success=True,
            strategy=StrategyType.SKETCH,
            tactics=["-- Sketch looks viable"],
            time_seconds=elapsed,
            metadata={"validation": "passed", "concerns": []},
        )
    else:
        return Result(
            success=False,
            strategy=StrategyType.SKETCH,
            tactics=[],
            time_seconds=elapsed,
            error="Sketch validation failed: missing typeclass instances",
            metadata={"validation": "failed", "concerns": ["typeclass gap"]},
        )


# Real implementation outline:
# async def run_sketch_real(
#     goal: Goal,
#     llm_client,
#     timeout: float = 6.0
# ) -> Result:
#     """Real sketch validation with LLM."""
#     prompt = f"""
#     Lean 4 goal: {goal.text}
#     Context: {goal.context}
#
#     Provide a high-level proof outline. Check for:
#     1. Required typeclass instances
#     2. Available lemmas in context
#     3. Likely missing helper lemmas
#     4. Type coercions needed
#
#     Return: {{viable: bool, concerns: [str], suggested_lemmas: [str]}}
#     """
#
#     try:
#         response = await asyncio.wait_for(
#             llm_client.complete(prompt),
#             timeout=timeout
#         )
#
#         # Parse response
#         validation = parse_validation(response)
#
#         if validation.viable:
#             return Result(
#                 success=True,
#                 strategy=StrategyType.SKETCH,
#                 metadata={
#                     "validation": "passed",
#                     "concerns": validation.concerns,
#                     "suggested_lemmas": validation.suggested_lemmas,
#                 },
#             )
#         else:
#             # Open lemma requests for missing pieces
#             for lemma in validation.suggested_lemmas:
#                 marketplace.request_lemma(lemma, goal)
#
#             return Result(success=False, ...)
#
#     except asyncio.TimeoutError:
#         return Result(success=False, error="timeout", ...)
