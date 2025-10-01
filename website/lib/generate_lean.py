#!/usr/bin/env python3
"""
Generate Lean 4 scaffolding from RPG JSON graph.

Reads website/data/pcp-graph.json and generates Lean files with stubs.
"""

import json
import sys
from pathlib import Path
from collections import defaultdict

def path_to_module_name(path):
    """Convert file path to module name: 'PCP/Defs.lean' -> 'PCP.Defs'"""
    if not path:
        return None
    return path.replace('.lean', '').replace('/', '.')

def module_to_file_path(module_name):
    """Convert module name to file path: 'PCP.Defs' -> 'PCP/Defs.lean'"""
    return module_name.replace('.', '/') + '.lean'

def get_imports_for_node(node, edges, all_nodes):
    """Determine which modules this node needs to import."""
    imports = set()
    node_id = node['id']

    # Find all dependencies
    for edge in edges:
        if edge['to'] == node_id and edge['type'] in ['depends', 'uses', 'imports']:
            dep_node = next((n for n in all_nodes if n['id'] == edge['from']), None)
            if dep_node and dep_node.get('path') and dep_node['path'] != node.get('path'):
                imports.add(path_to_module_name(dep_node['path']))

    return sorted(imports)

def format_difficulty_stars(difficulty):
    """Format difficulty as star comment."""
    if not difficulty:
        return ""
    stars = '★' * difficulty + '☆' * (5 - difficulty)
    return stars

def generate_file_header(node, imports):
    """Generate file header with imports and metadata."""
    lines = []
    lines.append("/-")
    lines.append(f"  {node.get('name', 'Module')}")
    lines.append(f"  ")
    if node.get('description'):
        lines.append(f"  {node['description']}")
        lines.append(f"  ")

    # Add metadata
    if node.get('difficulty'):
        stars = format_difficulty_stars(node['difficulty'])
        lines.append(f"  Difficulty: {stars} ({node['difficulty']}/5)")
    if node.get('estimatedLOC'):
        lines.append(f"  Estimated LOC: {node['estimatedLOC']}")
    if node.get('workPackage'):
        lines.append(f"  Work Package: {node['workPackage']}")

    # Add references
    if node.get('references'):
        lines.append(f"  ")
        lines.append(f"  References:")
        for ref in node['references']:
            ref_line = f"    - {ref.get('paper', '')}"
            if ref.get('section'):
                ref_line += f", §{ref['section']}"
            if ref.get('pages'):
                ref_line += f" ({ref['pages']})"
            lines.append(ref_line)

    # Add notes
    if node.get('notes'):
        lines.append(f"  ")
        lines.append(f"  Notes: {node['notes']}")

    lines.append("-/")
    lines.append("")

    # Standard imports
    if imports or node['kind'] in ['theorem', 'lemma', 'definition']:
        lines.append("import Mathlib")

    # Specific imports from dependencies
    for imp in imports:
        lines.append(f"import {imp}")

    if imports or node['kind'] in ['theorem', 'lemma', 'definition']:
        lines.append("")

    return '\n'.join(lines)

def generate_node_code(node):
    """Generate Lean code for a node."""
    lines = []

    kind = node['kind']

    if kind == 'module':
        # Module files are just collections, no specific declaration
        if node.get('description'):
            lines.append("/-!")
            lines.append(f"# {node['name']}")
            lines.append("")
            lines.append(node['description'])
            lines.append("-/")
            lines.append("")

    elif kind == 'theorem':
        if node.get('signature'):
            lines.append(node['signature'] + " := by")
            lines.append("  sorry")
        else:
            # Generic placeholder
            lines.append(f"theorem {node['id'].split('.')[-1]} : True := by")
            lines.append("  sorry")

    elif kind == 'lemma':
        if node.get('signature'):
            lines.append(node['signature'] + " := by")
            lines.append("  sorry")
        else:
            lines.append(f"lemma {node['id'].split('.')[-1]} : True := by")
            lines.append("  sorry")

    elif kind == 'definition':
        if node.get('signature'):
            lines.append(node['signature'] + " := by")
            lines.append("  sorry")
        else:
            # Generic structure
            name = node['id'].split('.')[-1]
            lines.append(f"def {name} : Type := by")
            lines.append("  sorry")

    elif kind == 'axiom':
        if node.get('signature'):
            lines.append(node['signature'])
        else:
            lines.append(f"axiom {node['id'].split('.')[-1]} : True")

    return '\n'.join(lines) if lines else ""

def group_nodes_by_file(nodes):
    """Group nodes by their file path."""
    files = defaultdict(list)
    for node in nodes:
        path = node.get('path')
        if path:
            files[path].append(node)
    return files

def generate_file(file_path, nodes, edges, all_nodes, root_dir):
    """Generate a complete Lean file."""
    lines = []

    # Use the first node (usually a module node) for the file header
    header_node = nodes[0] if nodes else {'name': file_path, 'kind': 'module'}

    # Get imports needed by any node in this file
    all_imports = set()
    for node in nodes:
        all_imports.update(get_imports_for_node(node, edges, all_nodes))

    # Generate header
    lines.append(generate_file_header(header_node, sorted(all_imports)))

    # Generate code for each node
    for i, node in enumerate(nodes):
        if i > 0:
            lines.append("")
            lines.append("")

        # Add node-specific comment if it's not a module
        if node['kind'] != 'module':
            lines.append("/-!")
            lines.append(f"## {node['name']}")
            if node.get('description'):
                lines.append("")
                lines.append(node['description'])
            lines.append("-/")
            lines.append("")

        code = generate_node_code(node)
        if code:
            lines.append(code)

    # Write file
    output_path = root_dir / file_path
    output_path.parent.mkdir(parents=True, exist_ok=True)

    with open(output_path, 'w') as f:
        f.write('\n'.join(lines))
        f.write('\n')  # Trailing newline

    return output_path

def generate_root_module(all_files, root_dir):
    """Generate PCP.lean that imports all submodules."""
    lines = []
    lines.append("/-")
    lines.append("  PCP Theorem Formalization")
    lines.append("  ")
    lines.append("  Root module - imports all submodules")
    lines.append("-/")
    lines.append("")

    # Import all submodules
    modules = []
    for file_path in sorted(all_files):
        module = path_to_module_name(file_path)
        if module:
            modules.append(module)

    for module in modules:
        lines.append(f"import {module}")

    output_path = root_dir / "PCP.lean"
    with open(output_path, 'w') as f:
        f.write('\n'.join(lines))
        f.write('\n')

    return output_path

def main():
    # Load JSON
    json_path = Path(__file__).parent.parent / 'data' / 'pcp-graph.json'
    with open(json_path) as f:
        data = json.load(f)

    # Determine output directory
    root_dir = Path(__file__).parent.parent.parent / 'PCP'

    # Group nodes by file
    files = group_nodes_by_file(data['nodes'])

    print(f"Generating Lean scaffolding in {root_dir}/")

    generated_files = []
    for file_path, nodes in sorted(files.items()):
        output_path = generate_file(
            file_path,
            nodes,
            data['edges'],
            data['nodes'],
            root_dir
        )
        generated_files.append(file_path)
        print(f"  ✓ {file_path} ({len(nodes)} nodes)")

    # Generate root module
    root_module = generate_root_module(generated_files, root_dir)
    print(f"  ✓ PCP.lean (root module)")

    print(f"\nGenerated {len(generated_files)} files with {len(data['nodes'])} nodes")
    print(f"All theorems/lemmas have 'sorry' placeholders - ready for formalization!")

if __name__ == '__main__':
    main()