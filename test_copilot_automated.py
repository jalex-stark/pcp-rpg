#!/usr/bin/env python3
"""
Test fully automated LeanCopilot proof search.

This uses the direct invocation method (no LeanDojo tracing required).
"""

import asyncio
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).parent))

from orchestrator.scheduler import Goal
from orchestrator.workers.copilot_direct import run_copilot_direct


async def test_automated_copilot():
    """Test fully automated LeanCopilot on simple goals."""

    test_cases = [
        {
            "id": "nat_add_zero_auto",
            "goal": "n + 0 = n",
            "context": ["(n : ℕ)"],
        },
        {
            "id": "nat_add_comm_auto",
            "goal": "m + n = n + m",
            "context": ["(m n : ℕ)"],
        },
        {
            "id": "list_append_nil_auto",
            "goal": "l ++ [] = l",
            "context": ["{α : Type*}", "(l : List α)"],
        },
    ]

    print("=" * 70)
    print("FULLY AUTOMATED LEANCOPILOT TEST (No Human Intervention)")
    print("=" * 70)
    print()
    print("This creates temp files with search_proof and compiles them.")
    print("No LeanDojo tracing, no existing theorem bodies needed.")
    print()

    successes = 0
    failures = 0

    for i, tc in enumerate(test_cases, 1):
        print(f"Test {i}/{len(test_cases)}: {tc['id']}")
        print(f"  Goal: {' '.join(tc['context'])} : {tc['goal']}")

        goal = Goal(
            id=tc["id"],
            text=tc["goal"],
            context=tc["context"],
            estimated_difficulty=0.5,
            priority=1.0,
            metadata={
                "theorem_name": tc["id"],
                "file_path": "TempTest.lean",
            }
        )

        try:
            result = await run_copilot_direct(goal, timeout=60.0)

            if result.success:
                print(f"  ✓ SUCCESS (in {result.time_seconds:.2f}s)")
                print(f"    Proof: {result.tactics[0] if result.tactics else 'N/A'}")
                successes += 1
            else:
                print(f"  ✗ FAILED ({result.time_seconds:.2f}s)")
                print(f"    Reason: {result.error}")
                failures += 1

        except Exception as e:
            print(f"  ✗ EXCEPTION: {e}")
            failures += 1

        print()

    print("=" * 70)
    print(f"Results: {successes} succeeded, {failures} failed")
    print("=" * 70)


if __name__ == "__main__":
    asyncio.run(test_automated_copilot())
