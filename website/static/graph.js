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
            showNodeDetails(d, data);
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
    function showNodeDetails(selectedNode, graphData) {
        const sidebar = d3.select('#sidebar');
        sidebar.classed('empty', false);

        const difficulty = '★'.repeat(selectedNode.difficulty || 0) + '☆'.repeat(5 - (selectedNode.difficulty || 0));

        // Find dependencies (what this node depends on)
        const dependencies = graphData.edges
            .filter(e => e.from === selectedNode.id)
            .map(e => {
                const targetNode = graphData.nodes.find(n => n.id === e.to);
                return { edge: e, node: targetNode };
            })
            .filter(d => d.node);

        // Find backlinks (what depends on this node)
        const backlinks = graphData.edges
            .filter(e => e.to === selectedNode.id)
            .map(e => {
                const sourceNode = graphData.nodes.find(n => n.id === e.from);
                return { edge: e, node: sourceNode };
            })
            .filter(d => d.node);

        let html = `
            <h2>${selectedNode.name}</h2>
            <div class="node-details">
                <div class="label">Status</div>
                <div class="value">
                    <span class="status-badge status-${selectedNode.status}">${selectedNode.status}</span>
                </div>

                <div class="label">Type</div>
                <div class="value">${selectedNode.kind}</div>

                ${selectedNode.path ? `
                    <div class="label">File Path</div>
                    <div class="value"><code>${selectedNode.path}</code></div>
                ` : ''}

                ${selectedNode.workPackage ? `
                    <div class="label">Work Package</div>
                    <div class="value">${selectedNode.workPackage} - ${getWorkPackageName(selectedNode.workPackage, graphData)}</div>
                ` : ''}

                ${selectedNode.difficulty ? `
                    <div class="label">Difficulty</div>
                    <div class="value difficulty">${difficulty} (${selectedNode.difficulty}/5)</div>
                ` : ''}

                ${selectedNode.estimatedLOC ? `
                    <div class="label">Estimated LOC</div>
                    <div class="value">${selectedNode.estimatedLOC} lines</div>
                ` : ''}

                ${selectedNode.description ? `
                    <div class="label">Description</div>
                    <div class="value">${selectedNode.description}</div>
                ` : ''}

                ${selectedNode.signature ? `
                    <div class="label">Lean Signature</div>
                    <div class="signature">${escapeHtml(selectedNode.signature)}</div>
                ` : ''}

                ${dependencies.length > 0 ? `
                    <div class="label">Dependencies (${dependencies.length})</div>
                    <div class="value">
                        ${dependencies.map(d => `
                            <div class="reference" style="cursor: pointer;" data-node-id="${d.node.id}">
                                <strong>${d.node.name}</strong>
                                ${d.edge.type ? `<br><span style="color: #8b949e; font-size: 0.75rem;">${d.edge.type}${d.edge.label ? ': ' + d.edge.label : ''}</span>` : ''}
                            </div>
                        `).join('')}
                    </div>
                ` : ''}

                ${backlinks.length > 0 ? `
                    <div class="label">Required By (${backlinks.length})</div>
                    <div class="value">
                        ${backlinks.map(d => `
                            <div class="reference" style="cursor: pointer;" data-node-id="${d.node.id}">
                                <strong>${d.node.name}</strong>
                                ${d.edge.type ? `<br><span style="color: #8b949e; font-size: 0.75rem;">${d.edge.type}${d.edge.label ? ': ' + d.edge.label : ''}</span>` : ''}
                            </div>
                        `).join('')}
                    </div>
                ` : ''}

                ${selectedNode.notes ? `
                    <div class="label">Notes</div>
                    <div class="value">${selectedNode.notes}</div>
                ` : ''}

                ${selectedNode.references && selectedNode.references.length > 0 ? `
                    <div class="label">References</div>
                    ${selectedNode.references.map(ref => `
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

        // Add click handlers for dependency/backlink navigation
        sidebar.selectAll('[data-node-id]').on('click', function() {
            const nodeId = d3.select(this).attr('data-node-id');
            const targetNode = nodes.find(n => n.id === nodeId);
            if (targetNode) {
                // Deselect all and select the target
                node.classed('selected', false);
                node.filter(d => d.id === nodeId).classed('selected', true);
                showNodeDetails(targetNode, graphData);

                // Center the view on the target node
                const scale = d3.zoomTransform(svg.node()).k;
                svg.transition().duration(750).call(
                    zoom.transform,
                    d3.zoomIdentity.translate(width / 2, height / 2).scale(scale).translate(-targetNode.x, -targetNode.y)
                );
            }
        });
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

    // Sidebar toggle functionality
    const sidebarToggle = document.getElementById('sidebar-toggle');
    const sidebar = document.getElementById('sidebar');
    let sidebarOpen = true;

    sidebarToggle.addEventListener('click', () => {
        sidebarOpen = !sidebarOpen;
        if (sidebarOpen) {
            sidebar.classList.remove('collapsed');
            sidebarToggle.classList.add('sidebar-open');
            sidebarToggle.textContent = '◀';
        } else {
            sidebar.classList.add('collapsed');
            sidebarToggle.classList.remove('sidebar-open');
            sidebarToggle.textContent = '▶';
        }
    });

    // Zoom controls
    const zoomIn = document.getElementById('zoom-in');
    const zoomOut = document.getElementById('zoom-out');
    const zoomReset = document.getElementById('zoom-reset');

    zoomIn.addEventListener('click', () => {
        svg.transition().call(zoom.scaleBy, 1.3);
    });

    zoomOut.addEventListener('click', () => {
        svg.transition().call(zoom.scaleBy, 0.7);
    });

    zoomReset.addEventListener('click', () => {
        svg.transition().call(zoom.transform, d3.zoomIdentity);
    });

    // Panel minimize functionality
    const legendMinimize = document.getElementById('legend-minimize');
    const statsMinimize = document.getElementById('stats-minimize');
    const legend = document.querySelector('.legend');
    const stats = document.querySelector('.stats');

    legendMinimize.addEventListener('click', (e) => {
        e.stopPropagation();
        legend.classList.toggle('minimized');
        legendMinimize.textContent = legend.classList.contains('minimized') ? '+' : '−';
        legendMinimize.title = legend.classList.contains('minimized') ? 'Expand' : 'Minimize';
    });

    statsMinimize.addEventListener('click', (e) => {
        e.stopPropagation();
        stats.classList.toggle('minimized');
        statsMinimize.textContent = stats.classList.contains('minimized') ? '+' : '−';
        statsMinimize.title = stats.classList.contains('minimized') ? 'Expand' : 'Minimize';
    });

    // Make panels draggable
    function makeDraggable(element) {
        let pos1 = 0, pos2 = 0, pos3 = 0, pos4 = 0;

        element.onmousedown = dragMouseDown;

        function dragMouseDown(e) {
            // Don't drag if clicking on buttons
            if (e.target.tagName === 'BUTTON') return;

            e.preventDefault();
            pos3 = e.clientX;
            pos4 = e.clientY;
            document.onmouseup = closeDragElement;
            document.onmousemove = elementDrag;
        }

        function elementDrag(e) {
            e.preventDefault();
            pos1 = pos3 - e.clientX;
            pos2 = pos4 - e.clientY;
            pos3 = e.clientX;
            pos4 = e.clientY;

            const newTop = element.offsetTop - pos2;
            const newLeft = element.offsetLeft - pos1;

            element.style.top = newTop + "px";
            element.style.left = newLeft + "px";
            element.style.right = "auto";
            element.style.bottom = "auto";
        }

        function closeDragElement() {
            document.onmouseup = null;
            document.onmousemove = null;
        }
    }

    makeDraggable(legend);
    makeDraggable(stats);

    // Search functionality
    const searchInput = document.getElementById('search-input');
    let searchActive = false;

    searchInput.addEventListener('input', (e) => {
        const searchTerm = e.target.value.toLowerCase().trim();

        if (searchTerm === '') {
            // Reset all nodes
            searchActive = false;
            node.attr('opacity', 1)
                .attr('stroke-width', 2)
                .attr('r', d => {
                    if (d.kind === 'module') return 18;
                    if (d.kind === 'theorem') return 14;
                    return 12;
                });
            labels.attr('opacity', 1)
                .attr('font-weight', 'normal');
            link.attr('stroke-opacity', 0.4);
            return;
        }

        searchActive = true;

        // Find matching nodes
        const matches = nodes.filter(n =>
            n.name.toLowerCase().includes(searchTerm) ||
            (n.description && n.description.toLowerCase().includes(searchTerm)) ||
            (n.signature && n.signature.toLowerCase().includes(searchTerm)) ||
            (n.id && n.id.toLowerCase().includes(searchTerm))
        );

        const matchIds = new Set(matches.map(m => m.id));

        // Highlight matches, dim others
        node.attr('opacity', d => matchIds.has(d.id) ? 1 : 0.15)
            .attr('stroke-width', d => matchIds.has(d.id) ? 4 : 2)
            .attr('r', d => {
                const baseSize = d.kind === 'module' ? 18 : (d.kind === 'theorem' ? 14 : 12);
                return matchIds.has(d.id) ? baseSize + 4 : baseSize;
            });

        labels.attr('opacity', d => matchIds.has(d.id) ? 1 : 0.15)
            .attr('font-weight', d => matchIds.has(d.id) ? 'bold' : 'normal');

        // Dim edges unless they connect matched nodes
        link.attr('stroke-opacity', d => {
            const sourceId = typeof d.source === 'object' ? d.source.id : d.source;
            const targetId = typeof d.target === 'object' ? d.target.id : d.target;
            const sourceMatch = matchIds.has(sourceId);
            const targetMatch = matchIds.has(targetId);
            return (sourceMatch || targetMatch) ? 0.6 : 0.05;
        });

        // If exactly one match, select it
        if (matches.length === 1) {
            node.classed('selected', false);
            node.filter(d => d.id === matches[0].id).classed('selected', true);
            showNodeDetails(matches[0], data);
        }
    });

    // Clear search on Escape
    searchInput.addEventListener('keydown', (e) => {
        if (e.key === 'Escape') {
            searchInput.value = '';
            searchInput.dispatchEvent(new Event('input'));
            searchInput.blur();
        }
    });

})();