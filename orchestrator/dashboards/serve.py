"""
Dashboard web server using FastAPI.

Provides real-time monitoring of:
- Scheduler statistics
- Ledger history
- Lemma marketplace
- Cache hit rates
"""

import os
from pathlib import Path

try:
    from fastapi import FastAPI
    from fastapi.responses import HTMLResponse, JSONResponse
    import uvicorn
    HAS_FASTAPI = True
except ImportError:
    HAS_FASTAPI = False
    print("Warning: fastapi not installed, dashboard disabled")

from orchestrator.cache import Ledger
from orchestrator.brokers import Marketplace


if HAS_FASTAPI:
    app = FastAPI(title="PCP Orchestrator Dashboard")

    # Global instances (would be managed better in production)
    ledger = Ledger()
    marketplace = Marketplace()


    @app.get("/", response_class=HTMLResponse)
    async def root():
        """Serve dashboard HTML."""
        return """
<!DOCTYPE html>
<html>
<head>
    <title>PCP Orchestrator Dashboard</title>
    <style>
        body {
            font-family: -apple-system, BlinkMacSystemFont, "Segoe UI", Roboto, sans-serif;
            max-width: 1200px;
            margin: 0 auto;
            padding: 20px;
            background: #f5f5f5;
        }
        h1 { color: #333; }
        h2 { color: #666; margin-top: 30px; }
        .card {
            background: white;
            border-radius: 8px;
            padding: 20px;
            margin: 10px 0;
            box-shadow: 0 2px 4px rgba(0,0,0,0.1);
        }
        .metric {
            display: inline-block;
            margin: 10px 20px 10px 0;
        }
        .metric-value {
            font-size: 2em;
            font-weight: bold;
            color: #007bff;
        }
        .metric-label {
            color: #666;
            font-size: 0.9em;
        }
        table {
            width: 100%;
            border-collapse: collapse;
        }
        th, td {
            padding: 10px;
            text-align: left;
            border-bottom: 1px solid #ddd;
        }
        th {
            background: #f8f9fa;
            font-weight: 600;
        }
        .success { color: #28a745; }
        .error { color: #dc3545; }
        .warning { color: #ffc107; }
        .refresh {
            float: right;
            padding: 5px 15px;
            background: #007bff;
            color: white;
            border: none;
            border-radius: 4px;
            cursor: pointer;
        }
    </style>
    <script>
        async function refreshData() {
            const statsResp = await fetch('/api/stats');
            const stats = await statsResp.json();

            const marketplaceResp = await fetch('/api/marketplace');
            const marketplace = await marketplaceResp.json();

            updateDisplay(stats, marketplace);
        }

        function updateDisplay(stats, marketplace) {
            document.getElementById('total-attempts').textContent = stats.total_attempts;
            document.getElementById('successful').textContent = stats.successful;
            document.getElementById('success-rate').textContent =
                (stats.success_rate * 100).toFixed(1) + '%';
            document.getElementById('cached-goals').textContent = stats.cached_goals;
            document.getElementById('cache-hits').textContent = stats.cache_hits;
            document.getElementById('open-tickets').textContent = marketplace.open_tickets;
            document.getElementById('completed-tickets').textContent = marketplace.completed;

            // Update strategy table
            const tbody = document.getElementById('strategy-tbody');
            tbody.innerHTML = '';
            for (const [strategy, data] of Object.entries(stats.by_strategy)) {
                const row = tbody.insertRow();
                row.innerHTML = `
                    <td>${strategy}</td>
                    <td>${data.attempts}</td>
                    <td>${data.successes}</td>
                    <td>${(data.success_rate * 100).toFixed(1)}%</td>
                    <td>${data.avg_time.toFixed(2)}s</td>
                `;
            }
        }

        setInterval(refreshData, 5000);
        refreshData();
    </script>
</head>
<body>
    <h1>PCP Orchestrator Dashboard</h1>
    <button class="refresh" onclick="refreshData()">Refresh</button>

    <div class="card">
        <h2>Overall Statistics</h2>
        <div class="metric">
            <div class="metric-value" id="total-attempts">0</div>
            <div class="metric-label">Total Attempts</div>
        </div>
        <div class="metric">
            <div class="metric-value success" id="successful">0</div>
            <div class="metric-label">Successful</div>
        </div>
        <div class="metric">
            <div class="metric-value" id="success-rate">0%</div>
            <div class="metric-label">Success Rate</div>
        </div>
    </div>

    <div class="card">
        <h2>Cache Performance</h2>
        <div class="metric">
            <div class="metric-value" id="cached-goals">0</div>
            <div class="metric-label">Cached Goals</div>
        </div>
        <div class="metric">
            <div class="metric-value" id="cache-hits">0</div>
            <div class="metric-label">Cache Hits</div>
        </div>
    </div>

    <div class="card">
        <h2>Lemma Marketplace</h2>
        <div class="metric">
            <div class="metric-value warning" id="open-tickets">0</div>
            <div class="metric-label">Open Requests</div>
        </div>
        <div class="metric">
            <div class="metric-value success" id="completed-tickets">0</div>
            <div class="metric-label">Completed</div>
        </div>
    </div>

    <div class="card">
        <h2>Strategy Performance</h2>
        <table>
            <thead>
                <tr>
                    <th>Strategy</th>
                    <th>Attempts</th>
                    <th>Successes</th>
                    <th>Success Rate</th>
                    <th>Avg Time</th>
                </tr>
            </thead>
            <tbody id="strategy-tbody">
            </tbody>
        </table>
    </div>
</body>
</html>
        """


    @app.get("/api/stats")
    async def get_stats():
        """Get ledger statistics."""
        stats = ledger.get_statistics()
        return JSONResponse(stats)


    @app.get("/api/marketplace")
    async def get_marketplace():
        """Get marketplace statistics."""
        stats = marketplace.get_stats()
        return JSONResponse(stats)


    @app.get("/api/health")
    async def health():
        """Health check."""
        return {"status": "ok"}


def run_dashboard(host: str = "127.0.0.1", port: int = 8000):
    """
    Run the dashboard server.

    Args:
        host: Host to bind to
        port: Port to serve on
    """
    if not HAS_FASTAPI:
        print("Error: fastapi not installed. Install with: pip install fastapi uvicorn")
        return

    print(f"Starting dashboard at http://{host}:{port}")
    uvicorn.run(app, host=host, port=port)
