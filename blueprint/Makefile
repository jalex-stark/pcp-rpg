.PHONY: all generate web pdf clean help

help:
	@echo "PCP Blueprint Build Commands:"
	@echo "  make generate    - Regenerate content.tex from JSON"
	@echo "  make pdf         - Build PDF with pdflatex"
	@echo "  make web         - Build web version (requires leanblueprint)"
	@echo "  make clean       - Remove build artifacts"
	@echo "  make all         - generate + pdf"

all: generate pdf

generate:
	@echo "Regenerating content.tex from JSON..."
	cd .. && python3 website/lib/generate_blueprint.py

pdf: generate
	@echo "Building PDF..."
	cd src && pdflatex -interaction=nonstopmode print.tex
	cd src && pdflatex -interaction=nonstopmode print.tex
	@echo "✓ PDF generated: src/print.pdf"

web: generate
	@echo "Building web blueprint..."
	leanblueprint web
	@echo "✓ Web blueprint generated"

clean:
	cd src && rm -f *.aux *.log *.out *.toc *.pdf *.fls *.fdb_latexmk