#!/usr/bin/env python3
"""
Test LeanCopilot integration with orchestrator.

Quick test to verify LeanCopilot tactics work through LeanDojo.
"""

import asyncio
import sys
from pathlib import Path

# Add orchestrator to path
sys.path.insert(0, str(Path(__file__).parent))

from orchestrator.scheduler import Goal, StrategyType
from orchestrator.workers.copilot import run_copilot


async def test_copilot_basic():
    """Test LeanCopilot on simple theorems from PCP.Basic."""

    test_cases = [
        {
            "id": "nat_add_zero",
            "goal": "n + 0 = n",
            "file": "PCP/Basic.lean",
            "context": ["n : ℕ"],
        },
        {
            "id": "nat_add_comm",
            "goal": "m + n = n + m",
            "file": "PCP/Basic.lean",
            "context": ["m n : ℕ"],
        },
    ]

    print("=" * 60)
    print("LEANCOPILOT INTEGRATION TEST")
    print("=" * 60)
    print()

    for i, tc in enumerate(test_cases, 1):
        print(f"Test {i}/{len(test_cases)}: {tc['id']}")
        print(f"  Goal: {tc['goal']}")

        goal = Goal(
            id=tc["id"],
            text=tc["goal"],
            context=tc["context"],
            estimated_difficulty=0.5,
            priority=1.0,
            metadata={
                "file_path": tc["file"],
                "theorem_name": tc["id"],
            }
        )

        try:
            result = await run_copilot(goal, timeout=30.0)

            if result.success:
                print(f"  ✓ SUCCESS (in {result.time_seconds:.2f}s)")
                print(f"    Strategy: {result.strategy}")
                print(f"    Tactics: {result.tactics}")
            else:
                print(f"  ✗ FAILED")
                print(f"    Error: {result.error}")

        except Exception as e:
            print(f"  ✗ EXCEPTION: {e}")

        print()

    print("=" * 60)


if __name__ == "__main__":
    asyncio.run(test_copilot_basic())
