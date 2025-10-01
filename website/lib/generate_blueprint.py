#!/usr/bin/env python3
"""
Generate blueprint LaTeX from RPG JSON graph.

Reads website/data/pcp-graph.json and generates blueprint/src/content.tex
following the leanblueprint conventions.
"""

import json
import sys
from pathlib import Path
from collections import defaultdict

def escape_latex(text):
    """Escape special LaTeX characters."""
    if not text:
        return ""
    replacements = {
        '&': r'\&',
        '%': r'\%',
        '$': r'\$',
        '#': r'\#',
        '_': r'\_',
        '{': r'\{',
        '}': r'\}',
        '~': r'\textasciitilde{}',
        '^': r'\^{}',
        '\\': r'\textbackslash{}',
    }
    for char, replacement in replacements.items():
        text = text.replace(char, replacement)
    return text

def lean_id_to_label(node_id):
    """Convert node ID to LaTeX label."""
    return node_id.replace('.', '-')

def format_difficulty(difficulty):
    """Format difficulty as stars."""
    if not difficulty:
        return ""
    stars = '★' * difficulty + '☆' * (5 - difficulty)
    return f"\\textbf{{{stars}}}"

def get_dependencies(node_id, edges):
    """Get list of nodes this node depends on."""
    deps = []
    for edge in edges:
        if edge['to'] == node_id and edge['type'] in ['depends', 'uses']:
            deps.append(edge['from'])
    return deps

def generate_node_latex(node, edges, work_packages):
    """Generate LaTeX for a single node."""
    lines = []

    # Determine environment type
    if node['kind'] == 'module':
        env = 'definition'  # Modules as definitions
        env_name = escape_latex(node['name'])
    elif node['kind'] == 'theorem':
        env = 'theorem'
        env_name = escape_latex(node['name'])
    elif node['kind'] == 'lemma':
        env = 'lemma'
        env_name = escape_latex(node['name'])
    elif node['kind'] == 'definition':
        env = 'definition'
        env_name = escape_latex(node['name'])
    else:
        env = 'lemma'
        env_name = escape_latex(node['name'])

    # Start environment
    lines.append(f"\\begin{{{env}}}[{env_name}]")
    lines.append(f"\\label{{{lean_id_to_label(node['id'])}}}")

    # Add lean file marker
    if node.get('path'):
        lean_path = node['path'].replace('.lean', '').replace('/', '.')
        lines.append(f"\\lean{{{lean_path}}}")

    # Add leanok marker if proved/tested
    if node.get('status') in ['proved', 'tested']:
        lines.append("\\leanok")

    # Add uses (dependencies)
    deps = get_dependencies(node['id'], edges)
    if deps:
        uses_labels = ', '.join(lean_id_to_label(d) for d in deps)
        lines.append(f"\\uses{{{uses_labels}}}")

    # Description
    if node.get('description'):
        lines.append(f"{escape_latex(node['description'])}")
        lines.append("")

    # Signature in code block
    if node.get('signature'):
        lines.append("\\begin{lstlisting}[language=Lean]")
        lines.append(node['signature'])
        lines.append("\\end{lstlisting}")
        lines.append("")

    # Metadata paragraph
    meta_parts = []
    if node.get('difficulty'):
        meta_parts.append(f"Difficulty: {format_difficulty(node['difficulty'])}")
    if node.get('estimatedLOC'):
        meta_parts.append(f"Est. {node['estimatedLOC']} LOC")
    if node.get('workPackage'):
        wp = next((w for w in work_packages if w['id'] == node['workPackage']), None)
        if wp:
            meta_parts.append(f"Work Package: {wp['name']}")

    if meta_parts:
        lines.append("\\noindent " + " $\\bullet$ ".join(meta_parts))
        lines.append("")

    # Notes
    if node.get('notes'):
        lines.append(f"\\textbf{{Notes:}} {escape_latex(node['notes'])}")
        lines.append("")

    # References
    if node.get('references'):
        lines.append("\\textbf{References:}")
        lines.append("\\begin{itemize}")
        for ref in node['references']:
            ref_text = escape_latex(ref.get('paper', ''))
            if ref.get('section'):
                ref_text += f", §{escape_latex(ref['section'])}"
            if ref.get('pages'):
                ref_text += f" ({escape_latex(ref['pages'])})"
            lines.append(f"  \\item {ref_text}")
        lines.append("\\end{itemize}")
        lines.append("")

    lines.append(f"\\end{{{env}}}")
    lines.append("")

    return '\n'.join(lines)

def generate_content(data):
    """Generate the full content.tex file."""
    lines = []

    # Header
    lines.append("% This file is auto-generated from website/data/pcp-graph.json")
    lines.append("% by website/lib/generate_blueprint.py")
    lines.append("% DO NOT EDIT DIRECTLY - edit the JSON and regenerate")
    lines.append("")
    lines.append("\\chapter{Introduction}")
    lines.append("")
    lines.append(escape_latex(data['metadata']['description']))
    lines.append("")
    lines.append("This blueprint presents a formalization plan for the classical PCP theorem")
    lines.append("following Dinur's gap amplification proof via constraint graphs.")
    lines.append("")

    # Organize nodes by work package
    wp_nodes = defaultdict(list)
    for node in data['nodes']:
        wp = node.get('workPackage', 'other')
        wp_nodes[wp].append(node)

    # Generate chapters for each work package
    for wp in data['workPackages']:
        wp_id = wp['id']
        if wp_id not in wp_nodes:
            continue

        lines.append(f"\\chapter{{{escape_latex(wp['name'])}}}")
        lines.append("")

        if wp.get('description'):
            lines.append(escape_latex(wp['description']))
            lines.append("")

        if wp.get('difficulty'):
            lines.append(f"\\textbf{{Difficulty:}} {escape_latex(wp['difficulty'])}")
            lines.append("")

        # Add each node in this work package
        for node in wp_nodes[wp_id]:
            lines.append(generate_node_latex(node, data['edges'], data['workPackages']))

    # Handle orphan nodes (no work package)
    if 'other' in wp_nodes:
        lines.append("\\chapter{Other Components}")
        lines.append("")
        for node in wp_nodes['other']:
            lines.append(generate_node_latex(node, data['edges'], data['workPackages']))

    return '\n'.join(lines)

def main():
    # Load JSON
    json_path = Path(__file__).parent.parent / 'data' / 'pcp-graph.json'
    with open(json_path) as f:
        data = json.load(f)

    # Generate content.tex
    content = generate_content(data)

    # Write output
    output_path = Path(__file__).parent.parent.parent / 'blueprint' / 'src' / 'content.tex'
    output_path.parent.mkdir(parents=True, exist_ok=True)

    with open(output_path, 'w') as f:
        f.write(content)

    print(f"✓ Generated {output_path}")
    print(f"  {len(data['nodes'])} nodes across {len(data['workPackages'])} work packages")

if __name__ == '__main__':
    main()