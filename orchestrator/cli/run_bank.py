"""
Benchmark runner for toy lemma bank.

Loads goals from bench/bank.jsonl, runs them through the scheduler,
and reports results.
"""

import asyncio
import json
from pathlib import Path
from datetime import datetime
from typing import Optional

from orchestrator.scheduler import Scheduler, Goal, StrategyType
from orchestrator.workers import run_micro, run_copilot, run_reprover, run_sketch
from orchestrator.cache import Ledger


async def load_bank(bank_path: str = "bench/bank.jsonl") -> list[Goal]:
    """
    Load goals from benchmark bank.

    Args:
        bank_path: Path to bank file

    Returns:
        List of goals
    """
    path = Path(bank_path)
    if not path.exists():
        print(f"Warning: Bank file {bank_path} not found, using empty bank")
        return []

    goals = []
    with open(path) as f:
        for i, line in enumerate(f):
            if not line.strip():
                continue

            try:
                data = json.loads(line)
                goal = Goal(
                    id=data.get('id', f"bank_{i}"),
                    text=data['goal'],
                    context=data.get('context', []),
                    estimated_difficulty=data.get('difficulty', 0.5),
                    priority=data.get('priority', 0.5),
                    metadata=data.get('metadata', {}),
                )
                goals.append(goal)
            except (json.JSONDecodeError, KeyError) as e:
                print(f"Warning: Skipping invalid line {i}: {e}")

    return goals


async def run_benchmark(timeout: int = 120, output_dir: str = "bench/results"):
    """
    Run benchmark bank.

    Args:
        timeout: Max seconds to run
        output_dir: Directory for results
    """
    print("=" * 60)
    print("BENCHMARK BANK RUNNER")
    print("=" * 60)

    # Load goals
    goals = await load_bank()
    print(f"Loaded {len(goals)} goals from bank")

    if not goals:
        print("No goals to process")
        return

    # Create scheduler
    scheduler = Scheduler(
        max_heavy=2,
        max_light=8,
        cpu_target=0.5,
        profile=1,  # Use profile from env or default
    )

    scheduler.register_worker(StrategyType.MICRO, run_micro)
    scheduler.register_worker(StrategyType.COPILOT, run_copilot)
    scheduler.register_worker(StrategyType.REPROVER, run_reprover)
    scheduler.register_worker(StrategyType.SKETCH, run_sketch)

    # Create goal queue
    goal_queue = asyncio.Queue()
    for goal in goals:
        await goal_queue.put(goal)

    # Track results
    results = {}
    goal_ids = {g.id for g in goals}
    processed_count = 0

    # Start scheduler
    print(f"Running for up to {timeout} seconds...")
    scheduler_task = asyncio.create_task(scheduler.process_queue(goal_queue))

    start_time = asyncio.get_event_loop().time()

    try:
        # Monitor progress
        while True:
            await asyncio.sleep(1)

            stats = scheduler.get_stats()
            processed_count = stats['goals_processed']

            elapsed = asyncio.get_event_loop().time() - start_time

            # Progress indicator
            pct = processed_count / len(goals) * 100 if goals else 0
            print(f"\rProgress: {processed_count}/{len(goals)} ({pct:.0f}%) | "
                  f"Solved: {stats['goals_solved']} | "
                  f"Time: {elapsed:.0f}s", end='', flush=True)

            # Stop conditions
            if processed_count >= len(goals):
                print("\n✓ All goals processed")
                break

            if elapsed >= timeout:
                print(f"\n⏱ Timeout reached ({timeout}s)")
                break

    finally:
        scheduler.shutdown()
        await scheduler_task

    # Get final stats
    stats = scheduler.get_stats()

    print("\n" + "=" * 60)
    print("RESULTS")
    print("=" * 60)
    print(f"Goals: {stats['goals_processed']}/{len(goals)} processed")
    print(f"Solved: {stats['goals_solved']} ({stats['goals_solved']/stats['goals_processed']*100 if stats['goals_processed'] > 0 else 0:.1f}%)")
    print(f"\nBy strategy:")

    for strategy in StrategyType:
        used = stats['strategies_used'].get(strategy, 0)
        succeeded = stats['strategies_succeeded'].get(strategy, 0)
        if used > 0:
            print(f"  {strategy:10s}: {succeeded:3d}/{used:3d} ({succeeded/used*100:.1f}%)")

    # Save results
    output_path = Path(output_dir)
    output_path.mkdir(parents=True, exist_ok=True)

    timestamp = datetime.now().strftime('%Y%m%d-%H%M%S')
    results_file = output_path / f"bank-{timestamp}.json"

    with open(results_file, 'w') as f:
        json.dump({
            'timestamp': timestamp,
            'goals_total': len(goals),
            'goals_processed': stats['goals_processed'],
            'goals_solved': stats['goals_solved'],
            'strategies': {
                str(k): {
                    'used': stats['strategies_used'].get(k, 0),
                    'succeeded': stats['strategies_succeeded'].get(k, 0),
                }
                for k in StrategyType
            },
            'config': {
                'timeout': timeout,
                'max_heavy': scheduler.max_heavy,
                'max_light': scheduler.max_light,
                'cpu_target': scheduler.cpu_target,
                'profile': scheduler.profile,
            }
        }, f, indent=2)

    print(f"\n✓ Results saved to {results_file}")
