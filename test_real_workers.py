#!/usr/bin/env python3
"""Test real LeanDojo workers on PCP.Basic theorems."""

import asyncio
import os
from pathlib import Path

# Add orchestrator to path
import sys
sys.path.insert(0, str(Path(__file__).parent / "orchestrator"))

from orchestrator.scheduler import Goal, StrategyType
from orchestrator.workers.micro import run_micro


async def test_basic_theorems():
    """Test micro worker on PCP.Basic theorems."""

    # Path to the Lean file
    file_path = str(Path(__file__).parent / "PCP" / "Basic.lean")

    # Create goals for the sorry theorems in PCP.Basic
    goals = [
        Goal(
            id="PCP.Basic.nat_add_zero",
            text="∀ n : ℕ, n + 0 = n",
            estimated_difficulty=0.1,
            metadata={"file_path": file_path}
        ),
        Goal(
            id="PCP.Basic.nat_zero_add",
            text="∀ n : ℕ, 0 + n = n",
            estimated_difficulty=0.1,
            metadata={"file_path": file_path}
        ),
        Goal(
            id="PCP.Basic.nat_add_comm",
            text="∀ m n : ℕ, m + n = n + m",
            estimated_difficulty=0.2,
            metadata={"file_path": file_path}
        ),
        Goal(
            id="PCP.Basic.nat_mul_one",
            text="∀ n : ℕ, n * 1 = n",
            estimated_difficulty=0.1,
            metadata={"file_path": file_path}
        ),
        Goal(
            id="PCP.Basic.list_append_nil",
            text="∀ {α : Type*} (l : List α), l ++ [] = l",
            estimated_difficulty=0.2,
            metadata={"file_path": file_path}
        ),
        Goal(
            id="PCP.Basic.list_nil_append",
            text="∀ {α : Type*} (l : List α), [] ++ l = l",
            estimated_difficulty=0.2,
            metadata={"file_path": file_path}
        ),
    ]

    print(f"Testing micro worker on {len(goals)} theorems from PCP.Basic")
    print(f"File: {file_path}")
    print()

    results = []
    for goal in goals:
        print(f"Testing: {goal.id}...")
        try:
            result = await asyncio.wait_for(
                run_micro(goal, timeout=10.0),
                timeout=15.0
            )
            results.append((goal, result))

            if result.success:
                print(f"  ✓ SOLVED in {result.time_seconds:.2f}s")
                print(f"    Tactics: {result.tactics}")
            else:
                print(f"  ✗ FAILED in {result.time_seconds:.2f}s")
                if result.error:
                    print(f"    Error: {result.error}")
        except asyncio.TimeoutError:
            print(f"  ✗ TIMEOUT (>15s)")
        except Exception as e:
            print(f"  ✗ EXCEPTION: {e}")

        print()

    # Summary
    solved = sum(1 for _, r in results if r.success)
    total = len(results)
    print("=" * 60)
    print(f"RESULTS: {solved}/{total} solved ({100*solved/total:.1f}%)")
    print("=" * 60)

    return results


if __name__ == "__main__":
    asyncio.run(test_basic_theorems())
