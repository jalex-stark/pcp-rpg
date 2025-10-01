"""
Lemma marketplace: request/provide helper lemmas.

Enables subagents to request missing lemmas and suppliers to fulfill them.
Tracks dependencies and prevents duplicate work.
"""

import asyncio
from dataclasses import dataclass, field
from typing import Optional
from datetime import datetime
from enum import Enum


class TicketStatus(str, Enum):
    """Status of a lemma request ticket."""
    OPEN = "open"
    CLAIMED = "claimed"
    COMPLETED = "completed"
    CANCELLED = "cancelled"


@dataclass
class LemmaRequest:
    """A request for a helper lemma."""
    ticket_id: str
    goal: str
    context: list[str] = field(default_factory=list)
    suggested_name: Optional[str] = None
    constraints: list[str] = field(default_factory=list)  # e.g., ["noncomputable", "[simp]"]
    priority: float = 0.5  # 0-1 scale
    requester: Optional[str] = None
    created_at: datetime = field(default_factory=datetime.now)
    status: TicketStatus = TicketStatus.OPEN
    claimed_by: Optional[str] = None
    completed_proof: Optional[str] = None


class Marketplace:
    """
    Lemma marketplace for coordinating helper lemma requests.

    Workers can:
    - Request lemmas when blocked
    - Claim open requests
    - Submit completed proofs
    - Query related lemmas
    """

    def __init__(self):
        """Initialize marketplace."""
        self.tickets: dict[str, LemmaRequest] = {}
        self.ticket_counter = 0
        self.lock = asyncio.Lock()

        # Statistics
        self.stats = {
            'total_requests': 0,
            'completed': 0,
            'cancelled': 0,
            'avg_completion_time': 0.0,
        }

    async def request_lemma(
        self,
        goal: str,
        context: list[str],
        suggested_name: Optional[str] = None,
        constraints: list[str] = None,
        priority: float = 0.5,
        requester: Optional[str] = None,
    ) -> str:
        """
        Submit a lemma request.

        Args:
            goal: Goal statement for the lemma
            context: Contextual information and types
            suggested_name: Suggested name for the lemma
            constraints: Constraints (e.g., ["noncomputable"])
            priority: Priority (0-1, higher = more urgent)
            requester: Identifier of requesting worker

        Returns:
            Ticket ID
        """
        async with self.lock:
            self.ticket_counter += 1
            ticket_id = f"lem-{datetime.now().strftime('%Y%m%d')}-{self.ticket_counter:04d}"

            request = LemmaRequest(
                ticket_id=ticket_id,
                goal=goal,
                context=context or [],
                suggested_name=suggested_name,
                constraints=constraints or [],
                priority=priority,
                requester=requester,
            )

            self.tickets[ticket_id] = request
            self.stats['total_requests'] += 1

            return ticket_id

    async def get_open_tickets(self, limit: int = 10) -> list[LemmaRequest]:
        """
        Get open lemma requests, sorted by priority.

        Args:
            limit: Max number of tickets to return

        Returns:
            List of open tickets
        """
        async with self.lock:
            open_tickets = [
                t for t in self.tickets.values()
                if t.status == TicketStatus.OPEN
            ]

            # Sort by priority (high to low)
            open_tickets.sort(key=lambda t: t.priority, reverse=True)

            return open_tickets[:limit]

    async def claim_ticket(self, ticket_id: str, claimer: str) -> bool:
        """
        Claim a ticket for work.

        Args:
            ticket_id: Ticket to claim
            claimer: Identifier of claiming worker

        Returns:
            True if claim succeeded
        """
        async with self.lock:
            if ticket_id not in self.tickets:
                return False

            ticket = self.tickets[ticket_id]

            if ticket.status != TicketStatus.OPEN:
                return False

            ticket.status = TicketStatus.CLAIMED
            ticket.claimed_by = claimer

            return True

    async def complete_ticket(
        self,
        ticket_id: str,
        proof: str,
        completer: str,
    ) -> bool:
        """
        Mark a ticket as completed with proof.

        Args:
            ticket_id: Ticket to complete
            proof: Completed Lean proof
            completer: Identifier of completing worker

        Returns:
            True if completion succeeded
        """
        async with self.lock:
            if ticket_id not in self.tickets:
                return False

            ticket = self.tickets[ticket_id]

            if ticket.status != TicketStatus.CLAIMED:
                return False

            if ticket.claimed_by != completer:
                return False

            ticket.status = TicketStatus.COMPLETED
            ticket.completed_proof = proof

            # Update stats
            self.stats['completed'] += 1
            completion_time = (datetime.now() - ticket.created_at).total_seconds()

            # Update running average
            prev_avg = self.stats['avg_completion_time']
            n = self.stats['completed']
            self.stats['avg_completion_time'] = (
                (prev_avg * (n - 1) + completion_time) / n
            )

            return True

    async def cancel_ticket(self, ticket_id: str, reason: Optional[str] = None) -> bool:
        """
        Cancel a ticket.

        Args:
            ticket_id: Ticket to cancel
            reason: Optional cancellation reason

        Returns:
            True if cancellation succeeded
        """
        async with self.lock:
            if ticket_id not in self.tickets:
                return False

            ticket = self.tickets[ticket_id]

            if ticket.status == TicketStatus.COMPLETED:
                return False

            ticket.status = TicketStatus.CANCELLED
            self.stats['cancelled'] += 1

            return True

    async def get_ticket(self, ticket_id: str) -> Optional[LemmaRequest]:
        """
        Get a specific ticket.

        Args:
            ticket_id: Ticket ID

        Returns:
            LemmaRequest if found, None otherwise
        """
        async with self.lock:
            return self.tickets.get(ticket_id)

    async def search_similar(self, goal: str, limit: int = 5) -> list[LemmaRequest]:
        """
        Search for similar lemma requests.

        Args:
            goal: Goal to search for
            limit: Max results

        Returns:
            List of similar requests
        """
        # Stub: simple text matching
        # Production would use embeddings + FAISS
        async with self.lock:
            results = []
            for ticket in self.tickets.values():
                if ticket.status == TicketStatus.COMPLETED:
                    # Simple heuristic: word overlap
                    goal_words = set(goal.lower().split())
                    ticket_words = set(ticket.goal.lower().split())
                    overlap = len(goal_words & ticket_words)

                    if overlap > 0:
                        results.append((overlap, ticket))

            # Sort by overlap
            results.sort(key=lambda x: x[0], reverse=True)

            return [ticket for _, ticket in results[:limit]]

    def get_stats(self) -> dict:
        """Get marketplace statistics."""
        return {
            **self.stats,
            'open_tickets': sum(
                1 for t in self.tickets.values()
                if t.status == TicketStatus.OPEN
            ),
            'claimed_tickets': sum(
                1 for t in self.tickets.values()
                if t.status == TicketStatus.CLAIMED
            ),
        }
