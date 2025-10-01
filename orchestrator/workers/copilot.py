"""
Lean Copilot worker: search_proof + select_premises.

Profile 1+ - requires Lean Copilot in lakefile.
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


async def run_copilot(goal: Goal, timeout: float = 20.0) -> Result:
    """
    Run Lean Copilot search (select_premises + search_proof).

    Uses LeanDojo to invoke Copilot tactics:
    1. Call select_premises to get top-k relevant lemmas
    2. Call search_proof with Aesop + LLM suggestions
    3. Return normalized proof script

    Configuration:
    - beam: 4
    - temperature: 0.2
    - max_steps: 20
    - premises: 12

    Args:
        goal: Goal to solve
        timeout: Max seconds to search

    Returns:
        Result with proof script if found
    """
    start_time = asyncio.get_event_loop().time()
    dojo = await get_dojo()

    # Try Copilot with select_premises first
    try:
        # Step 1: Select relevant premises
        premises_tactic = "select_premises (num := 12)"
        premises_result = await asyncio.wait_for(
            dojo.run_tac(
                theorem_file=goal.metadata.get("file_path", ""),
                theorem_name=goal.id,
                state=0,
                tactic=premises_tactic,
                tactic_timeout=timeout / 2,
            ),
            timeout=timeout / 2,
        )

        # Step 2: Run search_proof (only if premises succeeded or we have enough time)
        remaining_time = timeout - (asyncio.get_event_loop().time() - start_time)
        if remaining_time > 5.0:
            search_tactic = (
                "search_proof (beam := 4) (temperature := 0.2) (maxSteps := 20)"
            )
            search_result = await asyncio.wait_for(
                dojo.run_tac(
                    theorem_file=goal.metadata.get("file_path", ""),
                    theorem_name=goal.id,
                    state=premises_result.state if premises_result.success else 0,
                    tactic=search_tactic,
                    tactic_timeout=remaining_time,
                ),
                timeout=remaining_time,
            )

            if search_result.success:
                elapsed = asyncio.get_event_loop().time() - start_time
                tactics = (
                    [premises_tactic, search_tactic]
                    if premises_result.success
                    else [search_tactic]
                )
                return Result(
                    success=True,
                    strategy=StrategyType.COPILOT,
                    tactics=tactics,
                    time_seconds=elapsed,
                )

    except asyncio.TimeoutError:
        pass
    except Exception as e:
        pass

    # Fallback: try just search_proof without premise selection
    remaining_time = timeout - (asyncio.get_event_loop().time() - start_time)
    if remaining_time > 5.0:
        try:
            search_tactic = "search_proof (beam := 2) (maxSteps := 10)"
            search_result = await asyncio.wait_for(
                dojo.run_tac(
                    theorem_file=goal.metadata.get("file_path", ""),
                    theorem_name=goal.id,
                    state=0,
                    tactic=search_tactic,
                    tactic_timeout=remaining_time,
                ),
                timeout=remaining_time,
            )

            if search_result.success:
                elapsed = asyncio.get_event_loop().time() - start_time
                return Result(
                    success=True,
                    strategy=StrategyType.COPILOT,
                    tactics=[search_tactic],
                    time_seconds=elapsed,
                )
        except:
            pass

    elapsed = asyncio.get_event_loop().time() - start_time
    return Result(
        success=False,
        strategy=StrategyType.COPILOT,
        tactics=[],
        time_seconds=elapsed,
        error="Copilot search exhausted",
    )
