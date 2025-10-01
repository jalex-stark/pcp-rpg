"""
Main orchestrator CLI.

Provides commands to run background proof search, run benchmarks,
and launch the dashboard.
"""

import asyncio
import os
import sys
from pathlib import Path

try:
    import typer
    HAS_TYPER = True
except ImportError:
    HAS_TYPER = False
    print("Warning: typer not installed, CLI disabled")

from orchestrator.scheduler import Scheduler, Goal, StrategyType
from orchestrator.workers import run_micro, run_copilot, run_reprover, run_sketch
from orchestrator.cache import Ledger
from orchestrator.brokers import Marketplace


app = typer.Typer(help="PCP Formalization Orchestrator") if HAS_TYPER else None


def get_profile() -> int:
    """Get profile from environment."""
    return int(os.getenv('ORCH_PROFILE', '1'))


def get_cpu_target() -> float:
    """Get CPU target from environment."""
    return float(os.getenv('ORCH_CPU_TARGET', '0.5'))


def get_max_light() -> int:
    """Get max light workers from environment."""
    return int(os.getenv('ORCH_MAX_LIGHT', '8'))


def get_max_heavy() -> int:
    """Get max heavy workers from environment."""
    return int(os.getenv('ORCH_MAX_HEAVY', '2'))


def create_scheduler() -> Scheduler:
    """Create configured scheduler."""
    scheduler = Scheduler(
        max_heavy=get_max_heavy(),
        max_light=get_max_light(),
        cpu_target=get_cpu_target(),
        profile=get_profile(),
    )

    # Register workers
    scheduler.register_worker(StrategyType.MICRO, run_micro)
    scheduler.register_worker(StrategyType.COPILOT, run_copilot)
    scheduler.register_worker(StrategyType.REPROVER, run_reprover)
    scheduler.register_worker(StrategyType.SKETCH, run_sketch)

    return scheduler


async def run_background_search(duration: float = None):
    """
    Run background proof search.

    Args:
        duration: Max seconds to run (None = indefinite)
    """
    scheduler = create_scheduler()
    ledger = Ledger()
    marketplace = Marketplace()

    # Create goal queue (would be populated from Lean files)
    goal_queue = asyncio.Queue()

    # Example: add some test goals
    # In production, this would scan Lean files for sorry/admit
    test_goals = [
        Goal(
            id="test_1",
            text="∀ n : ℕ, n + 0 = n",
            estimated_difficulty=0.2,
            priority=0.5,
        ),
        Goal(
            id="test_2",
            text="∀ n m : ℕ, n + m = m + n",
            estimated_difficulty=0.3,
            priority=0.6,
        ),
    ]

    for goal in test_goals:
        await goal_queue.put(goal)

    print(f"Starting scheduler (profile={get_profile()}, cpu_target={get_cpu_target()})")
    print(f"Concurrency: light={get_max_light()}, heavy={get_max_heavy()}")

    # Start scheduler
    scheduler_task = asyncio.create_task(scheduler.process_queue(goal_queue))

    try:
        if duration:
            await asyncio.sleep(duration)
            scheduler.shutdown()
        await scheduler_task
    except KeyboardInterrupt:
        print("\nShutting down...")
        scheduler.shutdown()
        await scheduler_task

    # Print stats
    stats = scheduler.get_stats()
    print("\n" + "=" * 60)
    print("SCHEDULER STATISTICS")
    print("=" * 60)
    print(f"Goals processed: {stats['goals_processed']}")
    print(f"Goals solved: {stats['goals_solved']}")
    print(f"Success rate: {stats['goals_solved'] / stats['goals_processed'] * 100 if stats['goals_processed'] > 0 else 0:.1f}%")
    print(f"\nBy strategy:")
    for strategy in StrategyType:
        used = stats['strategies_used'].get(strategy, 0)
        succeeded = stats['strategies_succeeded'].get(strategy, 0)
        if used > 0:
            print(f"  {strategy:10s}: {succeeded:3d}/{used:3d} ({succeeded/used*100:.1f}%)")

    ledger.close()


if HAS_TYPER:
    @app.command()
    def bg(
        duration: float = typer.Option(None, help="Max seconds to run (None = indefinite)"),
    ):
        """Run background proof search."""
        asyncio.run(run_background_search(duration))


    @app.command()
    def bank(
        profile: int = typer.Option(None, help="Override ORCH_PROFILE"),
        timeout: int = typer.Option(120, help="Max seconds to run benchmark"),
        output: str = typer.Option("bench/results", help="Output directory"),
    ):
        """Run benchmark bank."""
        if profile is not None:
            os.environ['ORCH_PROFILE'] = str(profile)

        from orchestrator.cli.run_bank import run_benchmark
        asyncio.run(run_benchmark(timeout=timeout, output_dir=output))


    @app.command()
    def dashboard(
        port: int = typer.Option(8000, help="Port to serve on"),
        host: str = typer.Option("127.0.0.1", help="Host to bind to"),
    ):
        """Launch web dashboard."""
        from orchestrator.dashboards.serve import run_dashboard
        run_dashboard(host=host, port=port)


    @app.command()
    def stats():
        """Show current statistics."""
        ledger = Ledger()
        stats = ledger.get_statistics()

        print("=" * 60)
        print("LEDGER STATISTICS")
        print("=" * 60)
        print(f"Total attempts: {stats['total_attempts']}")
        print(f"Successful: {stats['successful']}")
        print(f"Success rate: {stats['success_rate'] * 100:.1f}%")
        print(f"\nBy strategy:")
        for strategy, data in stats['by_strategy'].items():
            print(f"  {strategy:10s}: {data['successes']:3d}/{data['attempts']:3d} "
                  f"({data['success_rate']*100:.1f}%) avg={data['avg_time']:.2f}s")
        print(f"\nCache:")
        print(f"  Cached goals: {stats['cached_goals']}")
        print(f"  Cache hits: {stats['cache_hits']}")

        ledger.close()


def main():
    """Main entry point."""
    if not HAS_TYPER:
        print("Error: typer not installed. Install with: pip install typer")
        sys.exit(1)

    app()


if __name__ == "__main__":
    main()
