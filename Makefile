.PHONY: all build update graph blueprint lean clean help orch-init orch-bg orch-bank orch-dashboard orch-stats

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
	@echo "  make orch-init    - Install orchestrator dependencies"
	@echo "  make orch-bg      - Run background proof search"
	@echo "  make orch-bank    - Run benchmark bank (Profile 0 by default)"
	@echo "  make orch-dashboard - Launch web dashboard (http://127.0.0.1:8000)"
	@echo "  make orch-stats   - Show orchestrator statistics"
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
	@echo "Installing orchestrator dependencies..."
	@python3 -m venv .venv || true
	@.venv/bin/pip install -r orchestrator/requirements.txt
	@echo "✓ Orchestrator dependencies installed"
	@echo "To activate: source .venv/bin/activate"

orch-bg:
	@echo "Starting background proof search..."
	@python3 -m orchestrator.main bg

orch-bank:
	@echo "Running benchmark bank..."
	@python3 -m orchestrator.main bank --timeout 120

orch-dashboard:
	@echo "Starting dashboard at http://127.0.0.1:8000"
	@python3 -m orchestrator.main dashboard

orch-stats:
	@python3 -m orchestrator.main stats
