"""
ReProver worker: retrieval-augmented tactic generation.

Profile 2+ - requires ReProver models and premise index.
"""

import asyncio
import random
from ..scheduler import Goal, Result, StrategyType


async def run_reprover(goal: Goal, timeout: float = 60.0) -> Result:
    """
    Run ReProver retrieval + generation.

    This is a stub implementation. In production, this would:
    1. Embed goal state with ByT5 encoder
    2. Retrieve top-k premises from FAISS index
    3. Generate tactics with ByT5 generator
    4. Use LeanDojo to replay and verify
    5. Update premise cache with success stats

    Configuration (to be wired):
    - retriever: kaiyuy/leandojo-lean4-retriever-byt5-small
    - generator: kaiyuy/leandojo-lean4-retriever-tacgen-byt5-small
    - top_k: 12
    - beam: 4
    - index: refreshed on module changes

    Args:
        goal: Goal to solve (typically high difficulty)
        timeout: Max seconds for retrieval + generation

    Returns:
        Result with generated tactics and premises used
    """
    start = asyncio.get_event_loop().time()

    # Simulate ReProver (retrieval + generation)
    await asyncio.sleep(min(2.0 + random.random() * 4.0, timeout))

    elapsed = asyncio.get_event_loop().time() - start

    # Stub: good on hard goals with high premise dependency
    difficulty = goal.estimated_difficulty
    success_prob = max(0.05, difficulty * 0.4)  # Better on harder goals

    success = random.random() < success_prob

    if success:
        # Simulate ReProver finding premises + tactics
        tactics = ["apply premise_1", "rw [premise_2]", "simp"]
        return Result(
            success=True,
            strategy=StrategyType.REPROVER,
            tactics=tactics,
            time_seconds=elapsed,
            metadata={"premises_retrieved": ["premise_1", "premise_2"]},
        )
    else:
        return Result(
            success=False,
            strategy=StrategyType.REPROVER,
            tactics=[],
            time_seconds=elapsed,
            error="ReProver generation failed",
        )


# Real implementation outline:
# async def run_reprover_real(
#     goal: Goal,
#     dojo,
#     retriever,
#     generator,
#     index,
#     timeout: float = 60.0
# ) -> Result:
#     """Real ReProver integration."""
#     try:
#         # Step 1: Retrieve premises
#         goal_embedding = await retriever.encode(goal.text)
#         premises = await index.search(goal_embedding, k=12)
#
#         # Step 2: Generate tactics with retrieved premises
#         tactics = await generator.generate(
#             goal=goal.text,
#             premises=premises,
#             beam=4,
#             max_len=128
#         )
#
#         # Step 3: Try each generated tactic
#         for tactic in tactics:
#             result = await asyncio.wait_for(
#                 dojo.run_tac(goal.id, tactic),
#                 timeout=timeout / len(tactics)
#             )
#             if result.success:
#                 return Result(
#                     success=True,
#                     strategy=StrategyType.REPROVER,
#                     tactics=[tactic],
#                     metadata={"premises": [p.name for p in premises]},
#                 )
#
#     except asyncio.TimeoutError:
#         return Result(success=False, error="timeout", ...)
#
#     return Result(success=False, ...)
