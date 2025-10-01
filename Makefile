.PHONY: all build update graph blueprint lean clean help orch-init orch-lean-init orch-bg orch-bank orch-dashboard orch-stats orch-test

help:
	@echo "PCP RPG Project Commands:"
	@echo ""
	@echo "Planning & Generation:"
	@echo "  make graph        - View interactive dependency graph (http://localhost:8000)"
	@echo "  make blueprint    - Regenerate blueprint LaTeX from JSON"
	@echo "  make lean         - Regenerate Lean scaffolding from JSON"
	@echo "  make all-gen      - Regenerate both blueprint and Lean files"
	@echo ""
	@echo "Lean Development:"
	@echo "  make build        - Build Lean project with Lake"
	@echo "  make update       - Update mathlib and get cache"
	@echo "  make clean        - Clean build artifacts"
	@echo ""
	@echo "Orchestrator (Proof Search Automation):"
	@echo "  make orch-init       - Install orchestrator deps (Python 3.13, no LeanDojo)"
	@echo "  make orch-lean-init  - Install LeanDojo deps (Python 3.12, full features)"
	@echo "  make orch-bg         - Run background proof search"
	@echo "  make orch-bank       - Run benchmark bank (Profile 0 by default)"
	@echo "  make orch-dashboard  - Launch web dashboard (http://127.0.0.1:8000)"
	@echo "  make orch-stats      - Show orchestrator statistics"
	@echo "  make orch-test       - Test LeanDojo integration"
	@echo ""
	@echo "Wrapper Scripts (use these for daily work):"
	@echo "  bin/orch         - General orchestrator (Python 3.13)"
	@echo "  bin/orch-lean    - With LeanDojo support (Python 3.12)"
	@echo ""
	@echo "Documentation:"
	@echo "  make pdf          - Build blueprint PDF (requires LaTeX)"

# Generation commands
graph:
	@echo "Starting web server for dependency graph..."
	@echo "Open http://localhost:8000 in your browser"
	@cd website/static && python3 -m http.server 8000

blueprint:
	@echo "Regenerating blueprint from JSON..."
	@cd website && python3 lib/generate_blueprint.py

lean:
	@echo "Regenerating Lean scaffolding from JSON..."
	@cd website && python3 lib/generate_lean.py
	@echo "Updating root PCP.lean imports..."
	@# Note: Current version manually maintains PCP.lean

all-gen: blueprint lean
	@echo "✓ All generated files updated"

# Lean build commands
build:
	lake build

update:
	lake update
	lake exe cache get

clean:
	lake clean

# Blueprint PDF
pdf:
	@cd blueprint && make pdf

# Orchestrator commands
orch-init:
	@echo "Installing orchestrator dependencies (Python 3.13, no LeanDojo)..."
	@python3 -m venv .venv || true
	@.venv/bin/pip install -r orchestrator/requirements.txt
	@echo "✓ Orchestrator dependencies installed"
	@echo ""
	@echo "Usage: bin/orch <command>"
	@echo "  or: source .venv/bin/activate && python -m orchestrator.main <command>"

orch-lean-init:
	@echo "Installing LeanDojo dependencies (Python 3.12)..."
	@command -v python3.12 >/dev/null 2>&1 || (echo "Error: Python 3.12 not found. Install with: brew install python@3.12" && exit 1)
	@python3.12 -m venv .venv-lean || true
	@.venv-lean/bin/pip install --upgrade pip
	@.venv-lean/bin/pip install lean-dojo psutil typer fastapi uvicorn
	@echo "✓ LeanDojo environment installed"
	@echo ""
	@echo "Usage: bin/orch-lean <command>"
	@echo "  or: source .venv-lean/bin/activate && python -m orchestrator.main <command>"

orch-bg:
	@echo "Starting background proof search..."
	@bin/orch bg

orch-bank:
	@echo "Running benchmark bank..."
	@bin/orch bank --timeout 120

orch-dashboard:
	@echo "Starting dashboard at http://127.0.0.1:8000"
	@bin/orch dashboard

orch-stats:
	@bin/orch stats

orch-test:
	@echo "Testing LeanDojo integration..."
	@bin/orch-test-dojo
