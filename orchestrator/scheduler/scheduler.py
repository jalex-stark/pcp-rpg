"""
Resource-aware proof search scheduler with UCB strategy selection.

Maintains ~50% CPU target using EMA throttling and concurrency caps.
Supports multiple proof search strategies with bandit-based allocation.
"""

import asyncio
import time
import os
from collections import defaultdict
from dataclasses import dataclass, field
from typing import Optional, Callable, Any
from enum import Enum

try:
    import psutil
    HAS_PSUTIL = True
except ImportError:
    HAS_PSUTIL = False
    print("Warning: psutil not available, CPU throttling disabled")


class StrategyType(str, Enum):
    """Available proof search strategies."""
    MICRO = "micro"  # Quick rewrites, simp, aesop
    COPILOT = "copilot"  # Lean Copilot search_proof
    REPROVER = "reprover"  # ReProver RAG tactics
    SKETCH = "sketch"  # LLM sketch validation


@dataclass
class Goal:
    """A proof goal to solve."""
    id: str
    text: str
    context: list[str] = field(default_factory=list)
    estimated_difficulty: float = 0.5  # 0-1 scale
    priority: float = 0.5  # 0-1 scale
    metadata: dict = field(default_factory=dict)


@dataclass
class Result:
    """Result of a proof attempt."""
    success: bool
    strategy: StrategyType
    tactics: list[str] = field(default_factory=list)
    time_seconds: float = 0.0
    subgoals: list[Goal] = field(default_factory=list)
    error: Optional[str] = None


class Scheduler:
    """
    Difficulty-aware proof search scheduler with compute throttling.

    Uses UCB bandit for strategy selection and maintains target CPU utilization.
    """

    def __init__(
        self,
        max_heavy: int = 2,
        max_light: int = 8,
        cpu_target: float = 0.5,
        profile: int = 1,
    ):
        """
        Initialize scheduler.

        Args:
            max_heavy: Max concurrent heavy tasks (ReProver, deep search)
            max_light: Max concurrent light tasks (micro, quick Copilot)
            cpu_target: Target CPU utilization (0-1)
            profile: Strategy profile (0=micro only, 1=+copilot, 2=+reprover)
        """
        self.max_heavy = max_heavy
        self.max_light = max_light
        self.cpu_target = cpu_target
        self.profile = profile

        # Strategy stats for UCB
        self.success_rate = defaultdict(lambda: 0.05)
        self.trials = defaultdict(int)

        # Concurrency tracking
        self.heavy_count = 0
        self.light_count = 0

        # CPU monitoring
        self.cpu_ema = 0.0
        self.cpu_alpha = 0.1  # EMA smoothing

        # Worker registry
        self.workers: dict[StrategyType, Callable] = {}

        # Shutdown flag
        self.shutdown_requested = False

        # Statistics
        self.stats = {
            'goals_processed': 0,
            'goals_solved': 0,
            'strategies_used': defaultdict(int),
            'strategies_succeeded': defaultdict(int),
        }

    def register_worker(self, strategy: StrategyType, worker: Callable):
        """Register a worker function for a strategy."""
        self.workers[strategy] = worker

    def get_enabled_strategies(self) -> list[StrategyType]:
        """Get strategies enabled for current profile."""
        if self.profile == 0:
            return [StrategyType.MICRO]
        elif self.profile == 1:
            return [StrategyType.MICRO, StrategyType.COPILOT, StrategyType.SKETCH]
        else:  # profile >= 2
            return list(StrategyType)

    def ucb_score(self, strategy: StrategyType) -> float:
        """
        Calculate UCB1 score for a strategy.

        Balances exploitation (success rate) with exploration (uncertainty).
        """
        mean = self.success_rate[strategy]
        n = max(1, self.trials[strategy])
        N = sum(self.trials.values()) + 1

        # UCB1 formula with exploration bonus
        exploration = 1.5 * ((2 * (N).bit_length()) / n) ** 0.5
        return mean + exploration

    async def get_cpu_load(self) -> float:
        """Get current CPU load as fraction (0-1)."""
        if not HAS_PSUTIL:
            return 0.3  # Conservative default

        # Use load average normalized by CPU count
        load_avg = psutil.getloadavg()[0]
        cpu_count = psutil.cpu_count() or 1
        return load_avg / cpu_count

    async def throttle(self):
        """
        Throttle execution to maintain target CPU usage.

        Uses exponential moving average to smooth CPU measurements.
        """
        current_load = await self.get_cpu_load()
        self.cpu_ema = self.cpu_alpha * current_load + (1 - self.cpu_alpha) * self.cpu_ema

        if self.cpu_ema > self.cpu_target:
            # Exponential backoff based on overload
            overload = self.cpu_ema - self.cpu_target
            sleep_time = min(1.0, 4 * overload)
            await asyncio.sleep(sleep_time)
        else:
            # Small yield to other tasks
            await asyncio.sleep(0)

    def select_strategies(self, goal: Goal, n: int = 3) -> list[StrategyType]:
        """
        Select top-n strategies for a goal using UCB.

        Args:
            goal: The goal to solve
            n: Number of strategies to try in parallel

        Returns:
            List of strategy types, sorted by UCB score
        """
        enabled = self.get_enabled_strategies()
        available = [s for s in enabled if s in self.workers]

        # Sort by UCB score
        scored = [(s, self.ucb_score(s)) for s in available]
        scored.sort(key=lambda x: x[1], reverse=True)

        return [s for s, _ in scored[:n]]

    async def run_goal(self, goal: Goal) -> Optional[Result]:
        """
        Run proof search on a single goal.

        Selects strategies via UCB, runs them in parallel (speculative execution),
        and returns the first success (canceling others).

        Args:
            goal: Goal to solve

        Returns:
            Result if any strategy succeeded, None otherwise
        """
        self.stats['goals_processed'] += 1

        # Select strategies
        strategies = self.select_strategies(goal)
        if not strategies:
            return None

        # Create tasks for each strategy
        tasks = []
        for strategy in strategies:
            self.trials[strategy] += 1
            self.stats['strategies_used'][strategy] += 1

            worker = self.workers[strategy]
            task = asyncio.create_task(worker(goal))
            tasks.append((strategy, task))

        # Wait for first completion
        task_list = [t for _, t in tasks]
        done, pending = await asyncio.wait(task_list, return_when=asyncio.FIRST_COMPLETED)

        # Cancel pending tasks
        for task in pending:
            task.cancel()
            try:
                await task
            except asyncio.CancelledError:
                pass

        # Get result from first completed
        completed_task = next(iter(done))
        result = await completed_task

        # Find which strategy succeeded
        strategy_used = None
        for strategy, task in tasks:
            if task == completed_task:
                strategy_used = strategy
                break

        # Update stats
        if result and result.success and strategy_used:
            self.success_rate[strategy_used] = (
                0.9 * self.success_rate[strategy_used] + 0.1 * 1.0
            )
            self.stats['goals_solved'] += 1
            self.stats['strategies_succeeded'][strategy_used] += 1
        elif strategy_used:
            self.success_rate[strategy_used] = (
                0.9 * self.success_rate[strategy_used] + 0.1 * 0.0
            )

        return result

    async def process_queue(self, goal_queue: asyncio.Queue):
        """
        Main loop: process goals from queue with concurrency limits.

        Args:
            goal_queue: Queue of Goal objects to process
        """
        active_tasks = []

        while not self.shutdown_requested:
            await self.throttle()

            # Clean up completed tasks
            if active_tasks:
                done_tasks = [t for t in active_tasks if t.done()]
                for task in done_tasks:
                    active_tasks.remove(task)
                    try:
                        await task  # Collect result/exception
                    except Exception as e:
                        print(f"Task error: {e}")

            # Check if we can start new work
            if goal_queue.empty() and not active_tasks:
                await asyncio.sleep(0.1)
                continue

            # Get next goal if queue not empty
            if not goal_queue.empty():
                try:
                    goal = goal_queue.get_nowait()
                except asyncio.QueueEmpty:
                    continue

                # Determine if heavy or light
                is_heavy = goal.estimated_difficulty > 0.6

                # Check capacity
                if is_heavy and self.heavy_count >= self.max_heavy:
                    goal_queue.put_nowait(goal)
                    await asyncio.sleep(0.2)
                    continue

                if not is_heavy and self.light_count >= self.max_light:
                    goal_queue.put_nowait(goal)
                    await asyncio.sleep(0.2)
                    continue

                # Start task
                if is_heavy:
                    self.heavy_count += 1
                else:
                    self.light_count += 1

                async def run_and_track(g: Goal, heavy: bool):
                    try:
                        result = await self.run_goal(g)
                        return result
                    finally:
                        if heavy:
                            self.heavy_count -= 1
                        else:
                            self.light_count -= 1

                task = asyncio.create_task(run_and_track(goal, is_heavy))
                active_tasks.append(task)

            await asyncio.sleep(0.01)

        # Cleanup on shutdown
        for task in active_tasks:
            task.cancel()
            try:
                await task
            except asyncio.CancelledError:
                pass

    def shutdown(self):
        """Request scheduler shutdown."""
        self.shutdown_requested = True

    def get_stats(self) -> dict:
        """Get current statistics."""
        return {
            **self.stats,
            'success_rates': dict(self.success_rate),
            'trials': dict(self.trials),
            'cpu_ema': self.cpu_ema,
            'active_heavy': self.heavy_count,
            'active_light': self.light_count,
        }
