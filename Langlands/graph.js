(function () {
  function cssEscape(value) {
    if (window.CSS && typeof window.CSS.escape === "function") {
      return window.CSS.escape(value);
    }
    return value.replace(/[^a-zA-Z0-9_-]/g, "\\$&");
  }

  function closeGraphModals() {
    document.querySelectorAll(".dep-modal-container").forEach((modal) => {
      modal.hidden = true;
    });
  }

  function showGraphModalElement(modal) {
    closeGraphModals();
    if (modal) {
      modal.hidden = false;
      modal.querySelector(".dep-closebtn")?.focus();
    }
  }

  function graphNodeVisibleLabel(node) {
    const labels = Array.from(node.querySelectorAll("text"))
      .map((text) => text.textContent.trim())
      .filter(Boolean);
    return labels.join(" ").trim();
  }

  function dotQuote(value) {
    return `"${String(value).replace(/\\/g, "\\\\").replace(/"/g, '\\"').replace(/\n/g, "\\n")}"`;
  }

  function topicGraphId(topicId) {
    return `topic:${topicId}`;
  }

  const GRAPH_DEFAULT_CONFIG = {
    maxVisibleNodes: 120,
    maxExpandNodes: 80,
    proofPlans: "selected-only",
  };
  const GRAPH_PROOF_PLAN_POLICIES = new Set(["hidden", "selected-only", "all"]);

  const graphState = {
    config: null,
    topicOverview: null,
    topicCache: new Map(),
    nodePayloadUrls: new Map(),
    nodePayloadCache: new Map(),
    expandedTopic: null,
    currentTopicSubgraph: null,
    proofPlanMode: null,
  };
  let graphRenderer = null;
  let graphZoomBehavior = null;
  let graphZoomSelection = null;

  // Per-status fill and border RGB values — the only colors that encode meaning.
  // Topic boxes blend these proportionally to show overall maturity at a glance.
  const STATUS_RGB = {
    formalized: { fill: [200, 230, 201], border: [46, 125, 50] },
    proved:     { fill: [200, 230, 201], border: [46, 125, 50] },
    admitted:   { fill: [187, 222, 251], border: [21, 101, 192] },
  };
  const STATUS_RGB_FALLBACK = { fill: [236, 236, 236], border: [130, 130, 130] };

  function _toHex(v) {
    return Math.round(Math.max(0, Math.min(255, v))).toString(16).padStart(2, "0");
  }

  // Returns {fillcolor, color} for a topic box based on the mix of node statuses.
  // Colors are a weighted RGB blend of the status fill/border colors.
  function topicMaturityColor(statusCounts) {
    const sc = statusCounts || {};
    const total = Object.values(sc).reduce((a, b) => a + b, 0);
    if (!total) return { fillcolor: "#ececec", color: "#828282" };
    let fr = 0, fg = 0, fb = 0, br = 0, bg = 0, bb = 0;
    for (const [status, count] of Object.entries(sc)) {
      const col = STATUS_RGB[status] || STATUS_RGB_FALLBACK;
      const w = count / total;
      fr += col.fill[0] * w;   fg += col.fill[1] * w;   fb += col.fill[2] * w;
      br += col.border[0] * w; bg += col.border[1] * w; bb += col.border[2] * w;
    }
    return {
      fillcolor: `#${_toHex(fr)}${_toHex(fg)}${_toHex(fb)}`,
      color:     `#${_toHex(br)}${_toHex(bg)}${_toHex(bb)}`,
    };
  }

  // Boundary topic nodes (other topics shown at the edge of a subgraph) — neutral style.
  const BOUNDARY_TOPIC_STYLE = {
    fillcolor: "#f0f4f8",
    color: "#8aaac8",
    fontcolor: "#6688aa",
  };

  function topicOverviewToDot(data) {
    const lines = [
      'strict digraph "" {',
      "\tgraph [bgcolor=transparent, rankdir=TB, ranksep=1.4, nodesep=0.8, splines=curved, pad=0.5];",
      '\tnode [label="\\N", penwidth=1.8, shape=box, fontname="Helvetica Neue,Helvetica,Arial,sans-serif", fontsize=13, margin="0.38,0.22", style=filled];',
      "\tedge [arrowhead=normal, arrowsize=0.7];",
    ];
    (data.topics || []).forEach((topic) => {
      const mc = topicMaturityColor(topic.status_counts);
      lines.push(`\t${dotQuote(topicGraphId(topic.id))} [label=${dotQuote(topic.title)}, fillcolor=${dotQuote(mc.fillcolor)}, color=${dotQuote(mc.color)}, penwidth=2.0, URL=${dotQuote(`#${topicGraphId(topic.id)}`)}];`);
    });
    (data.edges || []).forEach((edge) => {
      const count = edge.count || 1;
      // Skip very rare cross-topic edges to reduce visual noise in the overview
      if (count < 2) return;
      const weight = Math.min(count, 10);
      let penwidth, color;
      if (count >= 15) {
        penwidth = "2.4"; color = "#334455";
      } else if (count >= 8) {
        penwidth = "1.8"; color = "#556677";
      } else if (count >= 4) {
        penwidth = "1.2"; color = "#778899";
      } else {
        penwidth = "0.8"; color = "#aabbcc";
      }
      lines.push(`\t${dotQuote(topicGraphId(edge.from))} -> ${dotQuote(topicGraphId(edge.to))} [weight=${weight}, penwidth=${penwidth}, color=${dotQuote(color)}];`);
    });
    lines.push("}");
    return lines.join("\n");
  }

  function shapeForKind(kind) {
    if (kind === "topic" || kind === "definition" || kind === "concept") return "box";
    if (["lemma", "proposition", "theorem", "external-theorem"].includes(kind)) return "ellipse";
    if (kind === "example" || kind === "proof-plan") return "note";
    if (kind === "task") return "component";
    return "box";
  }

  function statusDisplay(status) {
    if (status === "formalized" || status === "proved") {
      return { color: "#2e7d32", fillcolor: "#c8e6c9", filled: true };
    }
    if (status === "admitted") {
      return { color: "#1565c0", fillcolor: "#bbdefb", filled: true };
    }
    // stub / needs_review / etc — light gray so it's visible but clearly incomplete
    return { color: "#666666", fillcolor: "#f0f0f0", filled: true };
  }

  function nodeStyleAttr(node, statusFilled) {
    const tokens = [];
    if (statusFilled) tokens.push("filled");
    if (node.kind === "proof-plan") tokens.push("dashed");
    return tokens.length ? tokens.join(",") : null;
  }

  function dotAttributes(attrs) {
    return Object.entries(attrs)
      .filter(([, value]) => value !== null && value !== undefined && value !== "")
      .sort(([left], [right]) => left.localeCompare(right))
      .map(([key, value]) => `${key}=${dotQuote(value)}`)
      .join(", ");
  }

  function currentProofPlanMode() {
    return GRAPH_PROOF_PLAN_POLICIES.has(graphState.proofPlanMode)
      ? graphState.proofPlanMode
      : GRAPH_DEFAULT_CONFIG.proofPlans;
  }

  function isVisibleProofPlan(node, mode) {
    if (node.kind !== "proof-plan") return true;
    if (mode === "all") return true;
    if (mode === "selected-only") return node.plan_status === "selected";
    return false;
  }

  function visibleSubgraphNodes(data) {
    const mode = currentProofPlanMode();
    return (data.nodes || []).filter((node) => isVisibleProofPlan(node, mode));
  }

  function edgeDisplayAttributes(edge) {
    if (edge.kind === "proof_plan_uses") {
      return {
        color: "#7a4aa0",
        label: "proof route",
        style: "dotted",
      };
    }
    return { color: "#444444", style: "solid" };
  }

  function boundaryEdgeDisplayAttributes(edge) {
    const isProofPlanRoute = edge.kind === "boundary_proof_plan_dependency"
      || edge.kind === "boundary_proof_plan_dependent";
    return {
      color: isProofPlanRoute ? "#7a4aa0" : "#999999",
      label: isProofPlanRoute ? "proof route" : "",
      style: isProofPlanRoute ? "dotted" : "dashed",
    };
  }

  function topicSubgraphToDot(data) {
    const visibleNodes = visibleSubgraphNodes(data);
    const visibleNodeIds = new Set(visibleNodes.map((node) => node.id));
    const endpointVisible = (nodeId) => nodeId.startsWith("topic:") || visibleNodeIds.has(nodeId);
    const lines = [
      'strict digraph "" {',
      "\tgraph [bgcolor=transparent, rankdir=TB, ranksep=1.0, nodesep=0.5, splines=spline, pad=0.3, fontname=\"Helvetica Neue,Helvetica,Arial,sans-serif\"];",
      '\tnode [label="\\N", penwidth=1.6, fontname="Helvetica Neue,Helvetica,Arial,sans-serif", fontsize=11, margin="0.25,0.14"];',
      "\tedge [arrowhead=normal, arrowsize=0.7, color=\"#444444\"];",
    ];
    if (data.topic) {
      const mc = topicMaturityColor(data.topic.status_counts);
      lines.push(`\t${dotQuote(topicGraphId(data.topic.id))} [${dotAttributes({
        color: mc.color,
        fillcolor: mc.fillcolor,
        fontsize: "13",
        label: data.topic.title,
        penwidth: "2.6",
        shape: "box",
        style: "filled,bold",
        URL: `#${topicGraphId(data.topic.id)}`,
      })}];`);
    }
    (data.child_topic_nodes || []).forEach((topic) => {
      const mc = topicMaturityColor(topic.status_counts);
      lines.push(`\t${dotQuote(topicGraphId(topic.id))} [${dotAttributes({
        color: mc.color,
        fillcolor: mc.fillcolor,
        label: topic.title,
        shape: "box",
        style: "filled",
        URL: `#${topicGraphId(topic.id)}`,
      })}];`);
    });
    (data.boundary_topics || []).forEach((topic) => {
      lines.push(`\t${dotQuote(topicGraphId(topic.id))} [${dotAttributes({
        color: BOUNDARY_TOPIC_STYLE.color,
        fillcolor: BOUNDARY_TOPIC_STYLE.fillcolor,
        fontcolor: BOUNDARY_TOPIC_STYLE.fontcolor,
        label: topic.title,
        penwidth: "1.2",
        shape: "box",
        style: "filled,dashed",
        URL: `#${topicGraphId(topic.id)}`,
      })}];`);
    });
    visibleNodes.forEach((node) => {
      const display = statusDisplay(node.status);
      lines.push(`\t${dotQuote(node.id)} [${dotAttributes({
        color: display.color,
        fillcolor: display.fillcolor,
        label: node.title,
        shape: shapeForKind(node.kind),
        style: nodeStyleAttr(node, display.filled),
        URL: `#${node.id}`,
      })}];`);
    });
    (data.edges || []).filter((edge) => endpointVisible(edge.from) && endpointVisible(edge.to)).forEach((edge) => {
      lines.push(`\t${dotQuote(edge.from)} -> ${dotQuote(edge.to)} [${dotAttributes(edgeDisplayAttributes(edge))}];`);
    });
    (data.boundary_edges || []).filter((edge) => endpointVisible(edge.from) && endpointVisible(edge.to)).forEach((edge) => {
      lines.push(`\t${dotQuote(edge.from)} -> ${dotQuote(edge.to)} [${dotAttributes(boundaryEdgeDisplayAttributes(edge))}];`);
    });
    (data.proof_plan_attachments || []).filter((edge) => endpointVisible(edge.from) && endpointVisible(edge.to)).forEach((edge) => {
      lines.push(`\t${dotQuote(edge.from)} -> ${dotQuote(edge.to)} [${dotAttributes({
        label: "has plan",
        style: "dotted",
      })}];`);
    });
    lines.push("}");
    return lines.join("\n");
  }

  function bindGraphInteractions() {
    document.querySelectorAll("#graph .node").forEach((node) => {
      const graphNodeId = node.querySelector("title")?.textContent?.trim();
      const visibleLabel = graphNodeVisibleLabel(node) || graphNodeId || "Node";
      const titleElement = node.querySelector("title");
      if (graphNodeId) node.dataset.graphNodeId = graphNodeId;
      if (titleElement) titleElement.textContent = visibleLabel;
      node.setAttribute("aria-label", visibleLabel);
      node.setAttribute("tabindex", "0");
      node.setAttribute("role", "button");
      node.addEventListener("click", () => {
        const nodeId = node.dataset.graphNodeId;
        if (nodeId?.startsWith("topic:")) {
          handleTopicActivation(nodeId.slice("topic:".length));
          return;
        }
        if (nodeId) {
          showNodeDetail(nodeId);
          return;
        }
        const mapped = nodeId ? document.querySelector(`[data-graph-node="${cssEscape(nodeId)}"]`) : null;
        if (mapped) showGraphModalElement(mapped);
      });
      node.addEventListener("keydown", (event) => {
        if (event.key === "Enter" || event.key === " ") {
          event.preventDefault();
          node.dispatchEvent(new MouseEvent("click", { bubbles: true }));
        }
      });
    });
  }

  function openNodeModal(target) {
    if (target) document.getElementById(target)?.removeAttribute("hidden");
  }

  function closeNodeModal(button) {
    button.closest(".modal-container")?.setAttribute("hidden", "");
  }

  function escapeHtml(value) {
    return String(value)
      .replace(/&/g, "&amp;")
      .replace(/</g, "&lt;")
      .replace(/>/g, "&gt;")
      .replace(/"/g, "&quot;");
  }

  function renderLinkList(title, items) {
    if (!items || !items.length) return "";
    return `<h2>${escapeHtml(title)}</h2><ul class="uses">${items.map((item) => (
      `<li><a href="${escapeHtml(item.href)}">${escapeHtml(item.title)}</a></li>`
    )).join("")}</ul>`;
  }

  function renderLeanRefs(refs) {
    if (!refs || !refs.length) return "";
    const items = refs.map((ref) => {
      const declaration = ref.source_url
        ? `<a href="${escapeHtml(ref.source_url)}"><code>${escapeHtml(ref.display_name)}</code></a>`
        : `<code>${escapeHtml(ref.display_name)}</code>`;
      const unresolved = ref.status === "unresolved"
        ? ` <span class="badge status-staged">Unresolved</span>${ref.reason ? ` <span class="lean-source-meta">${escapeHtml(ref.reason)}</span>` : ""}`
        : "";
      const metadata = ref.status !== "unresolved" && ref.repository_title
        ? ` <span class="lean-source-meta">${escapeHtml(ref.repository_title)}${ref.short_revision ? ` @ ${escapeHtml(ref.short_revision)}` : ""}${ref.module ? `, ${escapeHtml(ref.module)}` : ""}</span>`
        : "";
      const sorry = ref.has_sorry ? ' <span class="badge status-needs_proof_review">sorry/admit</span>' : "";
      return `<li>${declaration}${unresolved}${metadata}${sorry}</li>`;
    }).join("");
    return `<h2>Lean declarations</h2><ul class="uses">${items}</ul>`;
  }

  function graphLimit(name) {
    const value = graphState.config?.[name];
    return Number.isInteger(value) && value > 0 ? value : GRAPH_DEFAULT_CONFIG[name];
  }

  function visibleSubgraphNodeCount(data) {
    return 1 + (data.boundary_topics || []).length + visibleSubgraphNodes(data).length;
  }

  function exceedsTopicExpansionLimits(data) {
    // Count what the renderer will actually draw: flat page nodes plus
    // child-topic boxes. `counts.internal_nodes` is the pre-fold tally
    // (every node tagged into this topic, including those hidden behind
    // a folded child box) — using it here causes pages Python has
    // already folded under the cap to be wrongly rejected by the gate.
    const renderedNodes =
      (data.nodes || []).length +
      (data.child_topic_nodes || []).length;
    return renderedNodes > graphLimit("maxExpandNodes")
      || visibleSubgraphNodeCount(data) > graphLimit("maxVisibleNodes");
  }

  function hideGraphFallback() {
    const fallback = document.getElementById("graph-fallback");
    const graphElement = document.getElementById("graph");
    if (fallback) {
      fallback.hidden = true;
      fallback.replaceChildren();
    }
    if (graphElement) graphElement.hidden = false;
  }

  function updateGraphNavigationControls(mode) {
    const overviewButton = document.getElementById("graph-overview-button");
    const parentButton = document.getElementById("graph-parent-button");
    const resetButton = document.getElementById("graph-reset-view-button");
    const isOverview = mode === "topic-overview";
    const isFallback = mode === "topic-fallback";
    if (overviewButton) overviewButton.hidden = isOverview;
    if (parentButton) {
      const topic = graphState.currentTopicSubgraph?.topic || null;
      parentButton.hidden = isOverview || !topic?.parent;
    }
    if (resetButton) resetButton.hidden = isFallback;
  }

  function topicPathIds(topicId) {
    if (!topicId) return [];
    const parts = topicId.split(".");
    return parts.map((_, index) => parts.slice(0, index + 1).join("."));
  }

  function updateGraphBreadcrumbs(topic) {
    const nav = document.getElementById("graph-breadcrumbs");
    if (!nav) return;
    nav.replaceChildren();
    if (!topic) {
      nav.hidden = true;
      return;
    }
    const rootButton = document.createElement("button");
    rootButton.type = "button";
    rootButton.textContent = "Topic overview";
    rootButton.addEventListener("click", () => {
      goToTopicOverview().catch((error) => {
        const graphElement = document.getElementById("graph");
        if (graphElement) graphElement.textContent = error.message;
      });
    });
    nav.append(rootButton);
    topicPathIds(topic.id).forEach((topicId) => {
      const separator = document.createElement("span");
      separator.textContent = "/";
      separator.setAttribute("aria-hidden", "true");
      nav.append(separator);
      const button = document.createElement("button");
      button.type = "button";
      button.textContent = topicId.split(".").at(-1).replace(/[_-]/g, " ");
      button.disabled = topicId === topic.id;
      button.addEventListener("click", () => {
        handleTopicActivation(topicId);
      });
      nav.append(button);
    });
    nav.hidden = false;
  }

  function showOversizedTopicFallback(data) {
    const graphElement = document.getElementById("graph");
    const fallback = document.getElementById("graph-fallback");
    if (!graphElement || !fallback) return;

    graphElement.hidden = true;
    graphElement.replaceChildren();
    graphRenderer = null;

    const topic = data.topic || {};
    const title = topic.title || topic.id || "Topic";
    const nodeCount = data.counts?.internal_nodes ?? (data.nodes || []).length;
    const keywordPages = (data.keywords || []).map((keyword) => (
      `<li><a href="${escapeHtml(keyword.href)}">${escapeHtml(keyword.title)}</a> <span class="graph-fallback-count">${escapeHtml(keyword.count)}</span></li>`
    )).join("");
    const keywordSection = keywordPages
      ? `<h3>Keyword pages</h3><ul class="graph-fallback-links">${keywordPages}</ul>`
      : "";

    fallback.innerHTML = `
      <h2>${escapeHtml(title)}</h2>
      <p>This topic has ${escapeHtml(nodeCount)} nodes. Direct graph expansion is capped at ${escapeHtml(graphLimit("maxExpandNodes"))} topic nodes and ${escapeHtml(graphLimit("maxVisibleNodes"))} visible nodes.</p>
      <p><a href="${escapeHtml(topic.href || "#")}">Open topic page</a></p>
      ${keywordSection}
    `;
    fallback.hidden = false;
  }

  function updateProofPlanControls(visible) {
    const controls = document.getElementById("proof-plan-controls");
    if (!controls) return;
    controls.hidden = !visible;
    controls.querySelectorAll('input[name="proof-plan-mode"]').forEach((input) => {
      input.checked = input.value === currentProofPlanMode();
    });
  }

  function renderExpandedTopic(subgraph) {
    const graphElement = document.getElementById("graph");
    if (!graphElement || !subgraph?.topic) return;
    graphState.currentTopicSubgraph = subgraph;
    graphState.expandedTopic = subgraph.topic.id;
    graphElement.dataset.expandedTopic = subgraph.topic.id;
    if (exceedsTopicExpansionLimits(subgraph)) {
      graphElement.dataset.graphMode = "topic-fallback";
      updateGraphNavigationControls("topic-fallback");
      updateGraphBreadcrumbs(subgraph.topic);
      updateProofPlanControls(false);
      showOversizedTopicFallback(subgraph);
      return;
    }
    graphElement.dataset.graphMode = "topic-expanded";
    updateGraphNavigationControls("topic-expanded");
    updateGraphBreadcrumbs(subgraph.topic);
    updateProofPlanControls(true);
    renderDot(topicSubgraphToDot(subgraph));
  }

  function setProofPlanMode(mode) {
    if (!GRAPH_PROOF_PLAN_POLICIES.has(mode)) return;
    graphState.proofPlanMode = mode;
    updateProofPlanControls(Boolean(graphState.currentTopicSubgraph));
    if (graphState.currentTopicSubgraph) renderExpandedTopic(graphState.currentTopicSubgraph);
  }

  function renderNodePayload(payload) {
    const proof = payload.proof_html
      ? `<details class="proof-details"><summary>Proof</summary><div class="proof-body">${payload.proof_html}</div></details>`
      : "";
    return `
      <article class="thm ${escapeHtml(payload.kind)}_thmwrapper theorem-style-${escapeHtml(payload.kind)}">
        <header class="${escapeHtml(payload.kind)}_thmheading thm-heading">
          <span class="${escapeHtml(payload.kind)}_thmcaption thm-caption">${escapeHtml(payload.kind.replace(/-/g, " "))}</span>
          <span class="${escapeHtml(payload.kind)}_thmtitle thm-title">${escapeHtml(payload.title)}</span>
          <span class="thm-status thm-status-${escapeHtml(payload.status)}">${escapeHtml(payload.status)}</span>
        </header>
        <div class="${escapeHtml(payload.kind)}_thmcontent thm-content">
          <div class="body graph-modal-body">${payload.body_html}${proof}</div>
          <p><a href="${escapeHtml(payload.href)}">Open node page</a></p>
          ${renderLinkList("Uses", payload.deps)}
          ${renderLinkList("Used by", payload.dependents)}
          ${renderLeanRefs(payload.lean_refs)}
        </div>
      </article>
    `;
  }

  function rerenderMath(element) {
    if (typeof window.renderMathInElement === "function") {
      window.renderMathInElement(element, window.MDBLUEPRINT_MATH_OPTIONS || {});
    }
  }

  function nodePayloadUrl(nodeId) {
    return graphState.nodePayloadUrls.get(nodeId) || `node_payloads/${nodeId.replace(/\./g, "_")}.json`;
  }

  async function fetchNodePayload(nodeId) {
    if (graphState.nodePayloadCache.has(nodeId)) {
      return graphState.nodePayloadCache.get(nodeId);
    }
    const response = await fetch(nodePayloadUrl(nodeId));
    if (!response.ok) throw new Error(`Unable to load node details for ${nodeId}`);
    const payload = await response.json();
    graphState.nodePayloadCache.set(nodeId, payload);
    return payload;
  }

  async function showNodeDetail(nodeId) {
    const modal = document.getElementById("node-detail-modal");
    const content = document.getElementById("node-detail-content");
    if (!modal || !content) return;
    content.textContent = "Loading...";
    showGraphModalElement(modal);
    try {
      const payload = await fetchNodePayload(nodeId);
      content.innerHTML = renderNodePayload(payload);
      rerenderMath(content);
    } catch (error) {
      content.innerHTML = `<p class="graph-error">${escapeHtml(error.message)}</p>`;
    }
  }

  function graphvizRenderer(graphElement) {
    if (graphRenderer) return graphRenderer;
    const width = graphElement.clientWidth || 960;
    const height = graphElement.clientHeight || 720;
    graphRenderer = window.d3.select("#graph")
      .graphviz({ useWorker: true })
      .width(width)
      .height(height)
      .fit(true);
    return graphRenderer;
  }

  function installGraphPanZoom() {
    const svg = document.querySelector("#graph svg");
    if (!svg || !window.d3) return;
    if (!svg.querySelector(".graph-pan-zoom-layer")) {
      const layer = document.createElementNS("http://www.w3.org/2000/svg", "g");
      layer.setAttribute("class", "graph-pan-zoom-layer");
      while (svg.firstChild) layer.appendChild(svg.firstChild);
      svg.appendChild(layer);
    }
    const layer = svg.querySelector(".graph-pan-zoom-layer");
    graphZoomBehavior = window.d3.zoom()
      .scaleExtent([0.25, 5])
      .on("zoom", (event) => {
        window.d3.select(layer).attr("transform", event.transform);
      });
    graphZoomSelection = window.d3.select(svg);
    graphZoomSelection.call(graphZoomBehavior);
  }

  function resetGraphView() {
    if (!graphZoomSelection || !graphZoomBehavior) return;
    graphZoomSelection.transition()
      .duration(180)
      .call(graphZoomBehavior.transform, window.d3.zoomIdentity);
  }

  function renderDot(dot) {
    const graphElement = document.getElementById("graph");
    if (!graphElement || !window.d3) return;
    hideGraphFallback();
    graphElement.replaceChildren();
    graphRenderer = null;
    graphvizRenderer(graphElement)
      .on("end", () => {
        installGraphPanZoom();
        bindGraphInteractions();
        updateGraphNavigationControls(graphElement.dataset.graphMode);
      })
      .renderDot(dot);
  }

  function normalizeGraphConfig(config) {
    const raw = config || {};
    const proofPlans = GRAPH_PROOF_PLAN_POLICIES.has(raw.proofPlans)
      ? raw.proofPlans
      : GRAPH_DEFAULT_CONFIG.proofPlans;
    const positiveInteger = (value, fallback) => (
      Number.isInteger(value) && value > 0 ? value : fallback
    );
    return {
      ...raw,
      maxVisibleNodes: positiveInteger(raw.maxVisibleNodes, GRAPH_DEFAULT_CONFIG.maxVisibleNodes),
      maxExpandNodes: positiveInteger(raw.maxExpandNodes, GRAPH_DEFAULT_CONFIG.maxExpandNodes),
      proofPlans,
    };
  }

  function readGraphConfig() {
    const configElement = document.getElementById("graph-config");
    if (!configElement) return null;
    try {
      return normalizeGraphConfig(JSON.parse(configElement.textContent || "{}"));
    } catch (error) {
      return null;
    }
  }

  async function renderTopicOverview(config) {
    const graphElement = document.getElementById("graph");
    if (!graphElement || !config?.topicOverviewUrl) return;
    const response = await fetch(config.topicOverviewUrl);
    if (!response.ok) throw new Error(`Unable to load ${config.topicOverviewUrl}`);
    const data = await response.json();
    graphState.config = config;
    if (!GRAPH_PROOF_PLAN_POLICIES.has(graphState.proofPlanMode)) {
      graphState.proofPlanMode = config.proofPlans;
    }
    graphState.topicOverview = data;
    graphState.expandedTopic = null;
    graphState.currentTopicSubgraph = null;
    graphElement.dataset.graphMode = "topic-overview";
    delete graphElement.dataset.expandedTopic;
    updateGraphNavigationControls("topic-overview");
    updateProofPlanControls(false);
    renderDot(topicOverviewToDot(data));
  }

  async function fetchTopicSubgraph(topicId) {
    if (graphState.topicCache.has(topicId)) {
      return graphState.topicCache.get(topicId);
    }
    const baseUrl = graphState.config?.topicSubgraphBaseUrl || "subgraphs/topics";
    const response = await fetch(`${baseUrl}/${encodeURIComponent(topicId)}.json`);
    if (!response.ok) throw new Error(`Unable to load topic ${topicId}`);
    const data = await response.json();
    (data.nodes || []).forEach((node) => {
      if (node.payload) graphState.nodePayloadUrls.set(node.id, node.payload);
    });
    graphState.topicCache.set(topicId, data);
    return data;
  }

  async function handleTopicActivation(topicId) {
    const graphElement = document.getElementById("graph");
    if (!graphElement) return;
    try {
      if (graphState.expandedTopic === topicId) {
        goToTopicOverview().catch((error) => {
          graphElement.textContent = error.message;
        });
        return;
      }
      const subgraph = await fetchTopicSubgraph(topicId);
      renderExpandedTopic(subgraph);
    } catch (error) {
      hideGraphFallback();
      graphElement.textContent = error.message;
    }
  }

  async function goToTopicOverview() {
    const graphElement = document.getElementById("graph");
    if (!graphElement || !graphState.topicOverview) return;
    graphState.expandedTopic = null;
    graphState.currentTopicSubgraph = null;
    graphElement.dataset.graphMode = "topic-overview";
    delete graphElement.dataset.expandedTopic;
    updateGraphNavigationControls("topic-overview");
    updateGraphBreadcrumbs(null);
    updateProofPlanControls(false);
    renderDot(topicOverviewToDot(graphState.topicOverview));
  }

  async function goToParentTopic() {
    const topic = graphState.currentTopicSubgraph?.topic || null;
    if (!topic?.parent) {
      await goToTopicOverview();
      return;
    }
    await handleTopicActivation(topic.parent);
  }

  window.addEventListener("DOMContentLoaded", () => {
    document.querySelector("#legend-title")?.addEventListener("click", () => {
      document.querySelector("#legend-list")?.toggleAttribute("hidden");
    });
    document.querySelectorAll(".dep-closebtn").forEach((button) => {
      button.addEventListener("click", closeGraphModals);
    });
    document.querySelectorAll(".modal-trigger").forEach((button) => {
      button.addEventListener("click", () => openNodeModal(button.getAttribute("data-modal-target")));
    });
    document.querySelectorAll(".closebtn").forEach((button) => {
      button.addEventListener("click", () => closeNodeModal(button));
    });
    document.getElementById("proof-plan-controls")?.addEventListener("change", (event) => {
      const target = event.target;
      if (target?.matches?.('input[name="proof-plan-mode"]')) {
        setProofPlanMode(target.value);
      }
    });
    document.getElementById("graph-overview-button")?.addEventListener("click", () => {
      goToTopicOverview().catch((error) => {
        const graphElement = document.getElementById("graph");
        if (graphElement) graphElement.textContent = error.message;
      });
    });
    document.getElementById("graph-parent-button")?.addEventListener("click", () => {
      goToParentTopic().catch((error) => {
        const graphElement = document.getElementById("graph");
        if (graphElement) graphElement.textContent = error.message;
      });
    });
    document.getElementById("graph-reset-view-button")?.addEventListener("click", resetGraphView);
    document.addEventListener("keydown", (event) => {
      if (event.key === "Escape") {
        closeGraphModals();
        document.querySelectorAll(".modal-container").forEach((modal) => {
          modal.hidden = true;
        });
      }
    });

    const graphElement = document.getElementById("graph");
    const config = readGraphConfig();
    if (!graphElement || !config || !window.d3) return;
    renderTopicOverview(config).catch((error) => {
      graphElement.textContent = error.message;
    });
  });
})();
