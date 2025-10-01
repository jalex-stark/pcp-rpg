"""
Ledger and cache system for proof search.

Tracks all attempts, caches successful tactics, and enables checkpointing.
"""

import sqlite3
import hashlib
import json
from datetime import datetime
from typing import Optional, Any
from pathlib import Path
from dataclasses import asdict


class Ledger:
    """
    SQLite-based ledger for proof search attempts.

    Records every strategy attempt with:
    - Goal hash (normalized)
    - Strategy used
    - Outcome (success/failure)
    - Time taken
    - Tactics applied
    - Next subgoals

    Enables:
    - Checkpointing and resume
    - Deduplication
    - Success rate tracking
    - Cache population
    """

    def __init__(self, db_path: str = "orchestrator/cache/ledger.db"):
        """
        Initialize ledger.

        Args:
            db_path: Path to SQLite database
        """
        self.db_path = Path(db_path)
        self.db_path.parent.mkdir(parents=True, exist_ok=True)
        self.conn: Optional[sqlite3.Connection] = None
        self._initialize_db()

    def _initialize_db(self):
        """Create tables if they don't exist."""
        self.conn = sqlite3.connect(str(self.db_path), check_same_thread=False)
        self.conn.row_factory = sqlite3.Row

        cursor = self.conn.cursor()

        # Attempts table
        cursor.execute("""
            CREATE TABLE IF NOT EXISTS attempts (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                goal_hash TEXT NOT NULL,
                goal_text TEXT NOT NULL,
                strategy TEXT NOT NULL,
                success BOOLEAN NOT NULL,
                time_seconds REAL NOT NULL,
                tactics TEXT,  -- JSON array
                subgoals TEXT,  -- JSON array
                error TEXT,
                metadata TEXT,  -- JSON
                timestamp DATETIME DEFAULT CURRENT_TIMESTAMP
            )
        """)

        # Create indexes separately
        cursor.execute("CREATE INDEX IF NOT EXISTS idx_goal_hash ON attempts(goal_hash)")
        cursor.execute("CREATE INDEX IF NOT EXISTS idx_strategy ON attempts(strategy)")
        cursor.execute("CREATE INDEX IF NOT EXISTS idx_success ON attempts(success)")

        # Tactic cache table
        cursor.execute("""
            CREATE TABLE IF NOT EXISTS tactic_cache (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                goal_hash TEXT NOT NULL UNIQUE,
                goal_text TEXT NOT NULL,
                best_tactics TEXT NOT NULL,  -- JSON array
                success_rate REAL NOT NULL,
                avg_time_seconds REAL NOT NULL,
                use_count INTEGER DEFAULT 1,
                last_used DATETIME DEFAULT CURRENT_TIMESTAMP
            )
        """)

        # Premise cache table (for ReProver)
        cursor.execute("""
            CREATE TABLE IF NOT EXISTS premise_cache (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                goal_hash TEXT NOT NULL,
                premises TEXT NOT NULL,  -- JSON array
                score REAL NOT NULL,
                timestamp DATETIME DEFAULT CURRENT_TIMESTAMP
            )
        """)

        cursor.execute("CREATE INDEX IF NOT EXISTS idx_goal_hash_premise ON premise_cache(goal_hash)")

        self.conn.commit()

    def normalize_goal(self, goal_text: str) -> str:
        """
        Normalize goal text for hashing.

        Removes binder names, sorts simp sets, etc. to detect duplicates.

        Args:
            goal_text: Raw goal text

        Returns:
            Normalized text
        """
        # Stub: basic normalization
        # Production would parse and normalize properly
        normalized = goal_text.strip().lower()
        normalized = ' '.join(normalized.split())  # Collapse whitespace
        return normalized

    def hash_goal(self, goal_text: str) -> str:
        """
        Compute stable hash of a goal.

        Args:
            goal_text: Goal text

        Returns:
            SHA256 hash (hex)
        """
        normalized = self.normalize_goal(goal_text)
        return hashlib.sha256(normalized.encode()).hexdigest()[:16]

    def record_attempt(
        self,
        goal_text: str,
        strategy: str,
        success: bool,
        time_seconds: float,
        tactics: list[str] = None,
        subgoals: list[str] = None,
        error: Optional[str] = None,
        metadata: Optional[dict] = None,
    ) -> int:
        """
        Record a proof attempt.

        Args:
            goal_text: Goal text
            strategy: Strategy used
            success: Whether attempt succeeded
            time_seconds: Time taken
            tactics: Tactics applied
            subgoals: New subgoals generated
            error: Error message if failed
            metadata: Additional metadata

        Returns:
            Attempt ID
        """
        goal_hash = self.hash_goal(goal_text)

        cursor = self.conn.cursor()
        cursor.execute("""
            INSERT INTO attempts
            (goal_hash, goal_text, strategy, success, time_seconds, tactics, subgoals, error, metadata)
            VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?)
        """, (
            goal_hash,
            goal_text,
            strategy,
            success,
            time_seconds,
            json.dumps(tactics or []),
            json.dumps(subgoals or []),
            error,
            json.dumps(metadata or {}),
        ))

        self.conn.commit()
        return cursor.lastrowid

    def check_duplicate(self, goal_text: str, strategy: str) -> bool:
        """
        Check if goal+strategy has been tried before.

        Args:
            goal_text: Goal text
            strategy: Strategy to check

        Returns:
            True if already attempted
        """
        goal_hash = self.hash_goal(goal_text)

        cursor = self.conn.cursor()
        cursor.execute("""
            SELECT COUNT(*) FROM attempts
            WHERE goal_hash = ? AND strategy = ?
        """, (goal_hash, strategy))

        count = cursor.fetchone()[0]
        return count > 0

    def get_cached_tactics(self, goal_text: str) -> Optional[dict]:
        """
        Get cached tactics for a goal.

        Args:
            goal_text: Goal text

        Returns:
            Dict with tactics, success_rate, avg_time if cached, None otherwise
        """
        goal_hash = self.hash_goal(goal_text)

        cursor = self.conn.cursor()
        cursor.execute("""
            SELECT best_tactics, success_rate, avg_time_seconds, use_count
            FROM tactic_cache
            WHERE goal_hash = ?
        """, (goal_hash,))

        row = cursor.fetchone()
        if not row:
            return None

        # Update use count
        cursor.execute("""
            UPDATE tactic_cache
            SET use_count = use_count + 1, last_used = CURRENT_TIMESTAMP
            WHERE goal_hash = ?
        """, (goal_hash,))
        self.conn.commit()

        return {
            'tactics': json.loads(row['best_tactics']),
            'success_rate': row['success_rate'],
            'avg_time': row['avg_time_seconds'],
            'use_count': row['use_count'],
        }

    def update_tactic_cache(
        self,
        goal_text: str,
        tactics: list[str],
        success_rate: float,
        avg_time: float,
    ):
        """
        Update tactic cache for a goal.

        Args:
            goal_text: Goal text
            tactics: Successful tactics
            success_rate: Success rate (0-1)
            avg_time: Average time in seconds
        """
        goal_hash = self.hash_goal(goal_text)

        cursor = self.conn.cursor()
        cursor.execute("""
            INSERT INTO tactic_cache
            (goal_hash, goal_text, best_tactics, success_rate, avg_time_seconds)
            VALUES (?, ?, ?, ?, ?)
            ON CONFLICT(goal_hash) DO UPDATE SET
                best_tactics = excluded.best_tactics,
                success_rate = excluded.success_rate,
                avg_time_seconds = excluded.avg_time_seconds,
                use_count = use_count + 1,
                last_used = CURRENT_TIMESTAMP
        """, (
            goal_hash,
            goal_text,
            json.dumps(tactics),
            success_rate,
            avg_time,
        ))

        self.conn.commit()

    def get_statistics(self) -> dict:
        """Get ledger statistics."""
        cursor = self.conn.cursor()

        # Total attempts
        cursor.execute("SELECT COUNT(*) FROM attempts")
        total_attempts = cursor.fetchone()[0]

        # Success rate
        cursor.execute("SELECT COUNT(*) FROM attempts WHERE success = 1")
        successful = cursor.fetchone()[0]

        # By strategy
        cursor.execute("""
            SELECT strategy, COUNT(*) as count,
                   SUM(CASE WHEN success = 1 THEN 1 ELSE 0 END) as successes,
                   AVG(time_seconds) as avg_time
            FROM attempts
            GROUP BY strategy
        """)
        by_strategy = {}
        for row in cursor.fetchall():
            by_strategy[row['strategy']] = {
                'attempts': row['count'],
                'successes': row['successes'],
                'success_rate': row['successes'] / row['count'] if row['count'] > 0 else 0,
                'avg_time': row['avg_time'] or 0,
            }

        # Cache stats
        cursor.execute("SELECT COUNT(*) FROM tactic_cache")
        cached_goals = cursor.fetchone()[0]

        cursor.execute("SELECT SUM(use_count) FROM tactic_cache")
        cache_hits = cursor.fetchone()[0] or 0

        return {
            'total_attempts': total_attempts,
            'successful': successful,
            'success_rate': successful / total_attempts if total_attempts > 0 else 0,
            'by_strategy': by_strategy,
            'cached_goals': cached_goals,
            'cache_hits': cache_hits,
        }

    def close(self):
        """Close database connection."""
        if self.conn:
            self.conn.close()

    def __del__(self):
        """Cleanup on deletion."""
        self.close()
