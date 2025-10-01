// Load and visualize the PCP graph
(async function() {
    // Load the graph data
    const data = await d3.json('pcp-graph.json');

    // Update stats
    updateStats(data);

    // Set up SVG
    const container = d3.select('#graph-container');
    const svg = d3.select('#graph');
    const width = container.node().getBoundingClientRect().width;
    const height = container.node().getBoundingClientRect().height;

    svg.attr('width', width).attr('height', height);

    const g = svg.append('g');

    // Add zoom behavior
    const zoom = d3.zoom()
        .scaleExtent([0.1, 4])
        .on('zoom', (event) => {
            g.attr('transform', event.transform);
        });

    svg.call(zoom);

    // Status color mapping
    const statusColors = {
        'planned': '#1f6feb',
        'stated': '#a371f7',
        'proved': '#3fb950',
        'tested': '#bf8700',
        'blocked': '#f85149'
    };

    // Edge type colors
    const edgeColors = {
        'depends': '#58a6ff',
        'imports': '#8b949e',
        'uses': '#a371f7',
        'refines': '#3fb950',
        'implements': '#f0883e'
    };

    // Create node/edge data for D3
    const nodes = data.nodes.map(n => ({
        ...n,
        id: n.id,
        x: Math.random() * width,
        y: Math.random() * height
    }));

    const links = data.edges.map(e => ({
        source: e.from,
        target: e.to,
        type: e.type,
        label: e.label
    }));

    // Create force simulation
    const simulation = d3.forceSimulation(nodes)
        .force('link', d3.forceLink(links)
            .id(d => d.id)
            .distance(150))
        .force('charge', d3.forceManyBody()
            .strength(-800))
        .force('center', d3.forceCenter(width / 2, height / 2))
        .force('collision', d3.forceCollide().radius(50));

    // Draw links
    const link = g.append('g')
        .selectAll('line')
        .data(links)
        .join('line')
        .attr('class', 'link')
        .attr('stroke', d => edgeColors[d.type] || '#58a6ff')
        .attr('stroke-width', 2)
        .attr('marker-end', 'url(#arrowhead)');

    // Add arrowhead marker
    svg.append('defs').append('marker')
        .attr('id', 'arrowhead')
        .attr('viewBox', '0 -5 10 10')
        .attr('refX', 25)
        .attr('refY', 0)
        .attr('markerWidth', 6)
        .attr('markerHeight', 6)
        .attr('orient', 'auto')
        .append('path')
        .attr('d', 'M0,-5L10,0L0,5')
        .attr('fill', '#58a6ff')
        .attr('opacity', 0.6);

    // Draw nodes
    const node = g.append('g')
        .selectAll('circle')
        .data(nodes)
        .join('circle')
        .attr('class', 'node')
        .attr('r', d => {
            if (d.kind === 'module') return 18;
            if (d.kind === 'theorem') return 14;
            return 12;
        })
        .attr('fill', d => statusColors[d.status] || '#8b949e')
        .attr('stroke', d => {
            if (d.kind === 'theorem' || d.kind === 'lemma') return '#58a6ff';
            return '#30363d';
        })
        .attr('stroke-dasharray', d => {
            if (d.kind === 'theorem' || d.kind === 'lemma') return '4,2';
            return '0';
        })
        .on('click', (event, d) => {
            // Deselect all
            node.classed('selected', false);
            // Select this one
            d3.select(event.currentTarget).classed('selected', true);
            showNodeDetails(d);
        })
        .call(d3.drag()
            .on('start', dragstarted)
            .on('drag', dragged)
            .on('end', dragended));

    // Add node labels
    const labels = g.append('g')
        .selectAll('text')
        .data(nodes)
        .join('text')
        .attr('class', 'node-label')
        .attr('dy', d => {
            if (d.kind === 'module') return 28;
            if (d.kind === 'theorem') return 24;
            return 22;
        })
        .text(d => {
            // Truncate long names
            const name = d.name;
            if (name.length > 25) return name.substring(0, 22) + '...';
            return name;
        });

    // Update positions on simulation tick
    simulation.on('tick', () => {
        link
            .attr('x1', d => d.source.x)
            .attr('y1', d => d.source.y)
            .attr('x2', d => d.target.x)
            .attr('y2', d => d.target.y);

        node
            .attr('cx', d => d.x)
            .attr('cy', d => d.y);

        labels
            .attr('x', d => d.x)
            .attr('y', d => d.y);
    });

    // Drag functions
    function dragstarted(event, d) {
        if (!event.active) simulation.alphaTarget(0.3).restart();
        d.fx = d.x;
        d.fy = d.y;
    }

    function dragged(event, d) {
        d.fx = event.x;
        d.fy = event.y;
    }

    function dragended(event, d) {
        if (!event.active) simulation.alphaTarget(0);
        d.fx = null;
        d.fy = null;
    }

    // Show node details in sidebar
    function showNodeDetails(node) {
        const sidebar = d3.select('#sidebar');
        sidebar.classed('empty', false);

        const difficulty = '★'.repeat(node.difficulty || 0) + '☆'.repeat(5 - (node.difficulty || 0));

        let html = `
            <h2>${node.name}</h2>
            <div class="node-details">
                <div class="label">Status</div>
                <div class="value">
                    <span class="status-badge status-${node.status}">${node.status}</span>
                </div>

                <div class="label">Type</div>
                <div class="value">${node.kind}</div>

                ${node.path ? `
                    <div class="label">File Path</div>
                    <div class="value"><code>${node.path}</code></div>
                ` : ''}

                ${node.workPackage ? `
                    <div class="label">Work Package</div>
                    <div class="value">${node.workPackage} - ${getWorkPackageName(node.workPackage, data)}</div>
                ` : ''}

                ${node.difficulty ? `
                    <div class="label">Difficulty</div>
                    <div class="value difficulty">${difficulty} (${node.difficulty}/5)</div>
                ` : ''}

                ${node.estimatedLOC ? `
                    <div class="label">Estimated LOC</div>
                    <div class="value">${node.estimatedLOC} lines</div>
                ` : ''}

                ${node.description ? `
                    <div class="label">Description</div>
                    <div class="value">${node.description}</div>
                ` : ''}

                ${node.signature ? `
                    <div class="label">Lean Signature</div>
                    <div class="signature">${escapeHtml(node.signature)}</div>
                ` : ''}

                ${node.notes ? `
                    <div class="label">Notes</div>
                    <div class="value">${node.notes}</div>
                ` : ''}

                ${node.references && node.references.length > 0 ? `
                    <div class="label">References</div>
                    ${node.references.map(ref => `
                        <div class="reference">
                            <strong>${ref.paper}</strong>
                            ${ref.section ? `<br>§${ref.section}` : ''}
                            ${ref.pages ? ` (${ref.pages})` : ''}
                        </div>
                    `).join('')}
                ` : ''}
            </div>
        `;

        sidebar.html(html);
    }

    function getWorkPackageName(id, data) {
        const wp = data.workPackages.find(w => w.id === id);
        return wp ? wp.name : '';
    }

    function escapeHtml(text) {
        const div = document.createElement('div');
        div.textContent = text;
        return div.innerHTML;
    }

    function updateStats(data) {
        const total = data.nodes.length;
        const theorems = data.nodes.filter(n => n.kind === 'theorem' || n.kind === 'lemma').length;
        const modules = data.nodes.filter(n => n.kind === 'module').length;
        const proved = data.nodes.filter(n => n.status === 'proved' || n.status === 'tested').length;
        const totalLOC = data.nodes.reduce((sum, n) => sum + (n.estimatedLOC || 0), 0);

        d3.select('#stat-total').text(total);
        d3.select('#stat-theorems').text(theorems);
        d3.select('#stat-modules').text(modules);
        d3.select('#stat-loc').text(totalLOC.toLocaleString());
        d3.select('#stat-proved').text(total > 0 ? Math.round((proved / total) * 100) + '%' : '0%');
    }

})();