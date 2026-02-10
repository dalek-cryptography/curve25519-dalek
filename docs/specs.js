// ============================================================
// Specs Browser — Dual-List Layout
// Left panel:  verified function contracts (accordion cards)
// Right panel: spec function definitions   (accordion cards)
// Sidebar:     module filter
// ============================================================

// ── Firebase Configuration ───────────────────────────────────
// Fill in your Firebase project config to enable commenting.
// Firestore security rules should allow anonymous read/create with:
//
//   rules_version = '2';
//   service cloud.firestore {
//     match /databases/{database}/documents {
//       match /comments/{commentId} {
//         allow read: if true;
//         allow create: if request.resource.data.keys().hasAll(
//                            ['functionId', 'name', 'message', 'timestamp'])
//                       && request.resource.data.name is string
//                       && request.resource.data.message is string
//                       && request.resource.data.message.size() > 0;
//         allow delete: if true;
//         allow update: if false;
//       }
//     }
//   }
//
// The optional 'contentHash' field is stored automatically for version tracking.
const FIREBASE_CONFIG = {
    apiKey: "AIzaSyADcvcLYzwjeOUfjy9nWYv364gjjkJ07rA",
    authDomain: "dalek-lite-specs.firebaseapp.com",
    projectId: "dalek-lite-specs",
    storageBucket: "dalek-lite-specs.firebasestorage.app",
    messagingSenderId: "533633298026",
    appId: "1:533633298026:web:ace23bd6c0b26d20e2a413"
};

const FIREBASE_ENABLED = FIREBASE_CONFIG.apiKey !== "";

// ── State ────────────────────────────────────────────────────
let verifiedFunctions = [];
let specFunctions = [];
let specLookup = {};              // specName -> spec object

let activeModules = new Set();    // module filter — empty = show all
let filterPublic = false;         // toggle: show only public functions
let filterLibsignal = false;      // toggle: show only libsignal-used functions
let searchLeft = "";              // search in left panel
let searchRight = "";             // search in right panel
let specFilterRefs = null;        // null = show all, or Set of spec names to filter right panel
let specFilterSource = "";        // display name of the function that set the filter

let db = null;
let commentsCache = {};
let contentHashes = {};           // functionId -> hash of body/contract

// ── Initialization ───────────────────────────────────────────
document.addEventListener("DOMContentLoaded", async () => {
    // Firebase
    if (FIREBASE_ENABLED && typeof firebase !== "undefined") {
        try {
            firebase.initializeApp(FIREBASE_CONFIG);
            db = firebase.firestore();
        } catch (e) {
            console.warn("Firebase init failed:", e);
        }
    }

    // Load data
    try {
        const response = await fetch("specs_data.json");
        const data = await response.json();
        verifiedFunctions = data.verified_functions || [];
        specFunctions = data.spec_functions || [];
    } catch (err) {
        const errorHtml = '<div class="no-results"><h3>Failed to load data</h3><p>Could not load specs_data.json</p></div>';
        document.getElementById("listLeft").innerHTML = errorHtml;
        document.getElementById("listRight").innerHTML = errorHtml;
        console.error("Failed to load specs:", err);
        return;
    }

    // Build lookup
    for (const s of specFunctions) {
        specLookup[s.name] = s;
    }

    // Build content hashes for comment version tracking
    buildContentHashes();

    // Stats
    const modules = [...new Set(verifiedFunctions.map(v => v.module))];
    const axiomCount = specFunctions.filter(s => s.category === "axiom").length;
    const specOnlyCount = specFunctions.filter(s => s.category !== "axiom").length;
    const withSpecsCount = verifiedFunctions.filter(v => v.has_spec).length;
    const publicCount = verifiedFunctions.filter(v => v.is_public).length;
    const libsignalCount = verifiedFunctions.filter(v => v.is_libsignal).length;
    document.getElementById("totalFunctions").textContent = verifiedFunctions.length;
    document.getElementById("totalSpecs").textContent = specOnlyCount;
    document.getElementById("totalAxioms").textContent = axiomCount;

    // Build module pills and attribute filter pills
    buildModuleTree(modules);
    buildAttributeFilters(publicCount, libsignalCount);

    // Initial render of both panels
    renderLeftPanel();
    renderRightPanel();

    // Event listeners
    document.getElementById("searchLeft").addEventListener("input", e => {
        searchLeft = e.target.value.toLowerCase().trim();
        renderLeftPanel();
    });
    document.getElementById("searchRight").addEventListener("input", e => {
        searchRight = e.target.value.toLowerCase().trim();
        renderRightPanel();
    });
    document.getElementById("specFilterClear").addEventListener("click", () => {
        if (autoFilterBypassed) {
            autoFilterBypassed = false;
            renderRightPanel();
        } else {
            clearSpecFilter();
        }
    });


    // Event delegation for inline ref cards in right panel (registered once)
    document.getElementById("listRight").addEventListener("click", e => {
        const refHeader = e.target.closest(".inline-ref-header");
        if (refHeader) {
            e.stopPropagation();
            const card = refHeader.parentElement;
            if (card && card.classList.contains("inline-ref-card") && !card.classList.contains("inline-ref-cycle")) {
                card.classList.toggle("open");
                if (card.classList.contains("open")) {
                    const body = card.querySelector(":scope > .inline-ref-body");
                    if (body) {
                        body.querySelectorAll(":scope > pre code:not(.prism-highlighted)").forEach(block => {
                            Prism.highlightElement(block);
                            block.classList.add("prism-highlighted");
                        });
                    }
                }
            }
        }
    });
});

// ── Module filter (horizontal pills) ─────────────────────────
// Keep references to all pill elements so we can update counts dynamically.
let modulePills = [];   // { el, moduleId, countEl }
let attrPillPublic = null;   // { el, countEl }
let attrPillLibsignal = null;

function buildModuleTree(modules) {
    const container = document.getElementById("moduleTree");

    // Sort modules alphabetically, but push "backend" to the end
    const sorted = [...modules].sort((a, b) => {
        if (a === "backend") return 1;
        if (b === "backend") return -1;
        return a.localeCompare(b);
    });
    for (const mod of sorted) {
        const count = verifiedFunctions.filter(v => v.module === mod).length;
        const pill = createModulePill(mod, count, mod);
        container.appendChild(pill.el);
        modulePills.push(pill);
    }
}

function createModulePill(displayName, count, moduleId) {
    const el = document.createElement("span");
    el.className = "module-pill";
    el.innerHTML = `
        ${displayName}
        <span class="pill-count">${count}</span>
    `;
    const countEl = el.querySelector(".pill-count");
    el.addEventListener("click", () => {
        if (activeModules.has(moduleId)) {
            activeModules.delete(moduleId);
            el.classList.remove("active");
        } else {
            activeModules.add(moduleId);
            el.classList.add("active");
        }
        autoFilterBypassed = false;
        renderLeftPanel();
        renderRightPanel();
    });
    return { el, moduleId, countEl };
}

// ── Attribute filters (Public / Libsignal pills) ────────────
function buildAttributeFilters(publicCount, libsignalCount) {
    const container = document.getElementById("attrFilters");
    if (!container) return;

    const publicEl = document.createElement("span");
    publicEl.className = "attr-pill attr-public";
    publicEl.innerHTML = `Public <span class="pill-count">${publicCount}</span>`;
    publicEl.addEventListener("click", () => {
        filterPublic = !filterPublic;
        publicEl.classList.toggle("active", filterPublic);
        autoFilterBypassed = false;
        renderLeftPanel();
        renderRightPanel();
    });
    container.appendChild(publicEl);
    attrPillPublic = { el: publicEl, countEl: publicEl.querySelector(".pill-count") };

    const libsignalEl = document.createElement("span");
    libsignalEl.className = "attr-pill attr-libsignal";
    libsignalEl.innerHTML = `Libsignal <span class="pill-count">${libsignalCount}</span>`;
    libsignalEl.addEventListener("click", () => {
        filterLibsignal = !filterLibsignal;
        libsignalEl.classList.toggle("active", filterLibsignal);
        autoFilterBypassed = false;
        renderLeftPanel();
        renderRightPanel();
    });
    container.appendChild(libsignalEl);
    attrPillLibsignal = { el: libsignalEl, countEl: libsignalEl.querySelector(".pill-count") };
}

/**
 * Recompute and update all filter pill counts based on current active filters.
 *
 * Module pill counts reflect the attribute filters (Public / Libsignal).
 * Attribute pill counts reflect the active module filter.
 * This way, every count shows "how many would I see if I clicked this pill?".
 */
function updateFilterCounts() {
    // Base list filtered by attribute toggles (for module pills)
    let attrFiltered = verifiedFunctions;
    if (filterPublic) attrFiltered = attrFiltered.filter(v => v.is_public);
    if (filterLibsignal) attrFiltered = attrFiltered.filter(v => v.is_libsignal);

    for (const pill of modulePills) {
        const cnt = attrFiltered.filter(v => v.module === pill.moduleId).length;
        pill.countEl.textContent = cnt;
        // Hide module pills with 0 matches
        pill.el.style.display = cnt === 0 ? "none" : "";
    }

    // Base list filtered by active modules (for attribute pills)
    let modFiltered = verifiedFunctions;
    if (activeModules.size > 0) modFiltered = modFiltered.filter(v => activeModules.has(v.module));

    if (attrPillPublic) {
        let base = modFiltered;
        if (filterLibsignal) base = base.filter(v => v.is_libsignal);
        attrPillPublic.countEl.textContent = base.filter(v => v.is_public).length;
    }
    if (attrPillLibsignal) {
        let base = modFiltered;
        if (filterPublic) base = base.filter(v => v.is_public);
        attrPillLibsignal.countEl.textContent = base.filter(v => v.is_libsignal).length;
    }
}

// ── Left panel: tracked functions ────────────────────────────
function getFilteredVerified() {
    let list = verifiedFunctions;
    if (activeModules.size > 0) {
        list = list.filter(v => activeModules.has(v.module));
    }
    if (filterPublic) {
        list = list.filter(v => v.is_public);
    }
    if (filterLibsignal) {
        list = list.filter(v => v.is_libsignal);
    }
    if (searchLeft) {
        list = list.filter(v => {
            // Search top-level fields only (name, module, docs,
            // interpretations) — exclude contract body and referenced
            // spec names to avoid false matches.
            const h = (
                v.name + " " + v.display_name + " " + v.module + " " +
                (v.doc_comment || "") + " " +
                (v.math_interpretation || "") + " " + (v.informal_interpretation || "")
            ).toLowerCase();
            return h.includes(searchLeft);
        });
    }
    // Sort by module (backend last), then by display name
    list.sort((a, b) => {
        const ma = a.module === "backend" ? 1 : 0;
        const mb = b.module === "backend" ? 1 : 0;
        if (ma !== mb) return ma - mb;
        return a.module.localeCompare(b.module) || a.display_name.localeCompare(b.display_name);
    });
    return list;
}

function renderLeftPanel() {
    const container = document.getElementById("listLeft");
    const countEl = document.getElementById("countLeft");
    const filtered = getFilteredVerified();

    // Update all filter pill counts to reflect current state
    updateFilterCounts();

    if (filtered.length === 0) {
        container.innerHTML = '<div class="no-results"><h3>No matching functions</h3><p>Try a different search or module.</p></div>';
        countEl.textContent = "0";
        return;
    }

    countEl.textContent = filtered.length;

    let html = "";
    let currentMod = null;
    for (const fn of filtered) {
        if (fn.module !== currentMod) {
            currentMod = fn.module;
            html += `<div class="module-group-header">${escapeHtml(currentMod)}</div>`;
        }
        html += renderVerifiedCard(fn);
    }

    container.innerHTML = html;

    // Card toggle — inflate body lazily on first open
    container.querySelectorAll(".spec-header").forEach(h => {
        h.addEventListener("click", () => {
            const card = h.closest(".spec-card");
            inflateVerifiedBody(card);
            card.classList.toggle("open");
        });
    });
}

function renderVerifiedCard(fn) {
    const hasProof = fn.has_proof;
    const hasSpec = fn.has_spec;
    const hasMath = fn.math_interpretation && fn.math_interpretation.trim();

    // Status badges
    const badges = [];
    if (hasProof) badges.push(`<span class="fn-badge fn-badge-proof">proved</span>`);
    else if (hasSpec) badges.push(`<span class="fn-badge fn-badge-spec">spec</span>`);
    else badges.push(`<span class="fn-badge fn-badge-nospec">no spec</span>`);
    if (fn.is_libsignal) badges.push(`<span class="fn-badge fn-badge-libsignal">libsignal</span>`);

    // Render only the header; body is injected lazily on first open
    return `
    <div class="spec-card${hasProof ? " card-proved" : hasSpec ? " card-spec" : " card-nospec"}" data-id="${escapeAttr(fn.id)}" data-module="${escapeAttr(fn.module)}">
        <div class="spec-header">
            <div class="spec-toggle">&#9654;</div>
            <div class="spec-info">
                <div class="spec-name">${escapeHtml(fn.display_name)} ${badges.join("")}</div>
                <div class="spec-meta">
                    <span class="spec-module">${escapeHtml(fn.module)}</span>
                    ${hasMath ? `<span class="spec-math">${escapeHtml(fn.math_interpretation)}</span>` : ""}
                </div>
            </div>
            <a class="spec-github" href="${escapeAttr(fn.github_link)}" target="_blank" rel="noopener"
               title="View source on GitHub" onclick="event.stopPropagation()">
                Source &nearr;
            </a>
        </div>
        <div class="spec-body"></div>
    </div>`;
}

/** Populate a verified-function card body on first open. */
function inflateVerifiedBody(card) {
    if (card.dataset.inflated) return;
    card.dataset.inflated = "1";

    const fnId = card.dataset.id;
    const fn = verifiedFunctions.find(f => f.id === fnId);
    if (!fn) return;

    const hasDoc = fn.doc_comment && fn.doc_comment.trim();
    const hasMath = fn.math_interpretation && fn.math_interpretation.trim();
    const hasInformal = fn.informal_interpretation && fn.informal_interpretation.trim();
    const hasInterpretations = hasMath || hasInformal;
    const hasRefs = fn.referenced_specs && fn.referenced_specs.length > 0;
    const contractHtml = highlightSpecNames(fn.contract, fn.referenced_specs || []);

    const docHtml = hasDoc
        ? fn.doc_comment.split("\n").filter(Boolean).map(p => `<p>${escapeHtml(p)}</p>`).join("")
        : "";

    const refsHtml = hasRefs ? `
        <div class="contract-refs">
            <div class="contract-refs-label">Referenced Spec Functions</div>
            <div class="contract-refs-list">
                ${fn.referenced_specs.map(s => `<span class="contract-ref-tag" data-spec="${escapeAttr(s)}" title="Click to scroll to definition">${escapeHtml(s)}</span>`).join("")}
            </div>
        </div>` : "";

    const showRefsBtn = hasRefs ? `
        <button class="show-refs-btn" data-fn-id="${escapeAttr(fn.id)}" title="Filter right panel to show only referenced specs">
            Focus referenced specs <span class="refs-count">${fn.referenced_specs.length}</span>
        </button>` : "";

    const body = card.querySelector(".spec-body");
    body.innerHTML = `
        ${hasDoc ? `<div class="spec-doc">${docHtml}</div>` : ""}
        ${hasInterpretations ? `
        <div class="spec-interpretations">
            ${hasMath ? `<div class="spec-interp"><span class="spec-interp-label">Math:</span> <span class="spec-interp-value">${escapeHtml(fn.math_interpretation)}</span></div>` : ""}
            ${hasInformal ? `<div class="spec-interp"><span class="spec-interp-label">Meaning:</span> <span class="spec-interp-value">${escapeHtml(fn.informal_interpretation)}</span></div>` : ""}
        </div>` : ""}
        ${refsHtml}
        ${showRefsBtn}
        <div class="spec-code-wrapper">
            <button class="copy-btn">Copy</button>
            <pre><code class="language-rust">${contractHtml}</code></pre>
        </div>
        <div class="spec-comments">
            <button class="comments-toggle" data-fn-id="${escapeAttr(fn.id)}">
                <span>Comments</span>
                <span class="comment-count" id="count-${escapeAttr(fn.id)}">...</span>
            </button>
            <div class="comments-content" id="comments-${fn.id}"></div>
        </div>`;

    // Syntax highlight
    body.querySelectorAll("pre code.language-rust").forEach(b => {
        Prism.highlightElement(b);
        b.classList.add("prism-highlighted");
    });

    // Wire up copy button
    body.querySelectorAll(".copy-btn").forEach(btn => {
        btn.addEventListener("click", e => {
            e.stopPropagation();
            const code = btn.closest(".spec-code-wrapper").querySelector("code").textContent;
            navigator.clipboard.writeText(code).then(() => {
                btn.textContent = "Copied!";
                setTimeout(() => { btn.textContent = "Copy"; }, 1500);
            });
        });
    });

    // Wire up "Show referenced specs" button
    body.querySelectorAll(".show-refs-btn").forEach(btn => {
        btn.addEventListener("click", e => {
            e.stopPropagation();
            const refs = fn.referenced_specs || [];
            if (refs.length) setSpecFilter(refs, fn.display_name || fn.name);
        });
    });

    // Wire up comment toggle
    body.querySelectorAll(".comments-toggle").forEach(btn => {
        btn.addEventListener("click", () => {
            const content = btn.nextElementSibling;
            if (!content) return;
            content.classList.toggle("open");
            if (content.classList.contains("open")) {
                loadComments(btn.dataset.fnId, content);
            }
        });
    });

    // Wire up ref tag clicks
    body.querySelectorAll(".contract-ref-tag").forEach(tag => {
        tag.addEventListener("click", e => {
            e.stopPropagation();
            scrollToSpecCard(tag.dataset.spec);
        });
    });

    // Wire up spec-link clicks (highlighted spec names in contract code)
    body.querySelectorAll(".spec-link").forEach(link => {
        link.addEventListener("click", e => {
            e.stopPropagation();
            scrollToSpecCard(link.dataset.spec);
        });
    });
}

// ── Right panel: spec functions ──────────────────────────────
/**
 * Compute the transitive closure of spec names reachable from a set of
 * verified functions.  Each verified function's `referenced_specs` are the
 * seeds; we then recursively follow each spec's own `referenced_specs`.
 */
function getReachableSpecs(verifiedList) {
    const reachable = new Set();
    const queue = [];
    for (const fn of verifiedList) {
        for (const s of (fn.referenced_specs || [])) {
            if (!reachable.has(s)) { reachable.add(s); queue.push(s); }
        }
    }
    while (queue.length) {
        const name = queue.pop();
        const spec = specLookup[name];
        if (!spec) continue;
        for (const dep of (spec.referenced_specs || [])) {
            if (!reachable.has(dep)) { reachable.add(dep); queue.push(dep); }
        }
    }
    return reachable;
}

/** True when any left-panel filter (module, public, libsignal) is active. */
function hasLeftFilter() {
    return activeModules.size > 0 || filterPublic || filterLibsignal;
}

function getFilteredSpecs() {
    let list = specFunctions;

    // Filter by referenced specs (from "Show referenced specs" button)
    if (specFilterRefs) {
        list = list.filter(s => specFilterRefs.has(s.name));
    }

    // Auto-filter: when a left-panel filter is active, show only specs
    // reachable (transitively) from the visible verified functions.
    // Skip when autoFilterBypassed (user navigated to an out-of-scope spec).
    if (!specFilterRefs && !autoFilterBypassed && hasLeftFilter()) {
        const reachable = getReachableSpecs(getFilteredVerified());
        list = list.filter(s => reachable.has(s.name));
    }

    if (searchRight) {
        list = list.filter(s => {
            // Search top-level fields only (name, module, signature, docs,
            // interpretations) — exclude body to avoid matching on referenced
            // spec names that appear inside the function definition.
            const h = (
                s.name + " " + s.module + " " + s.signature + " " +
                (s.doc_comment || "") + " " + (s.math_interpretation || "") +
                " " + (s.informal_interpretation || "")
            ).toLowerCase();
            return h.includes(searchRight);
        });
    }

    // Sort: specs first (by module, then name), axioms last (by name only)
    list.sort((a, b) => {
        const aIsAxiom = a.category === "axiom" ? 1 : 0;
        const bIsAxiom = b.category === "axiom" ? 1 : 0;
        if (aIsAxiom !== bIsAxiom) return aIsAxiom - bIsAxiom;
        if (!aIsAxiom) {
            // Both are specs — sort by module then name
            return a.module.localeCompare(b.module) || a.name.localeCompare(b.name);
        }
        // Both are axioms — sort by name only (no module grouping)
        return a.name.localeCompare(b.name);
    });
    return list;
}

function renderRightPanel() {
    const container = document.getElementById("listRight");
    const countEl = document.getElementById("countRight");
    const banner = document.getElementById("specFilterBanner");
    const bannerText = document.getElementById("specFilterText");

    // Show/hide filter banner
    const filtered = getFilteredSpecs();
    const clearBtn = document.getElementById("specFilterClear");
    if (specFilterRefs) {
        banner.style.display = "flex";
        bannerText.textContent = `Showing ${specFilterRefs.size} specs related to ${specFilterSource}`;
        clearBtn.textContent = "Show All";
        clearBtn.style.display = "";
    } else if (autoFilterBypassed && hasLeftFilter()) {
        banner.style.display = "flex";
        bannerText.textContent = `Showing all specs (navigated outside filtered scope)`;
        clearBtn.textContent = "Re-apply filter";
        clearBtn.style.display = "";
    } else if (hasLeftFilter()) {
        banner.style.display = "flex";
        const labels = [];
        if (activeModules.size > 0) labels.push([...activeModules].join(", "));
        if (filterPublic) labels.push("Public");
        if (filterLibsignal) labels.push("Libsignal");
        bannerText.textContent = `Showing ${filtered.length} specs referenced by ${labels.join(" + ")} functions`;
        clearBtn.style.display = "none";
    } else {
        banner.style.display = "none";
    }

    if (filtered.length === 0) {
        container.innerHTML = '<div class="no-results"><h3>No matching specs</h3><p>Try a different search or clear the filter.</p></div>';
        countEl.textContent = "0";
        return;
    }

    // Show only spec count (axioms are counted separately in the hero bar)
    countEl.textContent = filtered.filter(s => s.category !== "axiom").length;

    let html = "";
    let currentMod = null;
    let axiomHeaderShown = false;
    for (const spec of filtered) {
        if (spec.category === "axiom") {
            // Single header for all axioms
            if (!axiomHeaderShown) {
                axiomHeaderShown = true;
                const axiomCount = filtered.filter(s => s.category === "axiom").length;
                html += `<div class="module-group-header axiom-group-header">Axioms <span class="axiom-group-count">${axiomCount}</span></div>`;
            }
        } else {
            if (spec.module !== currentMod) {
                currentMod = spec.module;
                html += `<div class="module-group-header">${escapeHtml(currentMod)}</div>`;
            }
        }
        html += renderSpecCard(spec);
    }

    container.innerHTML = html;

    // Card toggle — inflate body lazily on first open
    container.querySelectorAll(".spec-header").forEach(h => {
        h.addEventListener("click", () => {
            const card = h.closest(".spec-card");
            inflateSpecBody(card);
            card.classList.toggle("open");
        });
    });
}

function renderInlineRefCard(spec, visited) {
    // visited tracks already-rendered specs to prevent infinite recursion
    if (!visited) visited = new Set();
    if (visited.has(spec.name)) {
        return `<div class="inline-ref-card inline-ref-cycle">
            <div class="inline-ref-header">
                <span class="inline-ref-name">${escapeHtml(spec.name)}</span>
                <span class="inline-ref-cycle-label">(already shown above)</span>
            </div>
        </div>`;
    }
    visited = new Set(visited);
    visited.add(spec.name);

    const escapedBody = escapeHtml(spec.body);
    const hasMath = spec.math_interpretation && spec.math_interpretation.trim();
    const hasNestedRefs = spec.referenced_specs && spec.referenced_specs.length > 0;

    // Recursively render nested referenced specs (same layout as top level)
    const nestedRefsHtml = hasNestedRefs ? `
        <div class="inline-refs-container inline-refs-nested">
            <div class="inline-refs-label">Referenced specs <span class="refs-count">${spec.referenced_specs.length}</span></div>
            ${spec.referenced_specs.map(refName => {
                const refSpec = specLookup[refName];
                if (!refSpec) return `<div class="inline-ref-card"><div class="inline-ref-header"><span class="inline-ref-name">${escapeHtml(refName)}</span><span class="inline-ref-missing">not found</span></div></div>`;
                return renderInlineRefCard(refSpec, visited);
            }).join("")}
        </div>` : "";

    return `
    <div class="inline-ref-card">
        <div class="inline-ref-header">
            <span class="inline-ref-toggle">&#9654;</span>
            <span class="inline-ref-name">${escapeHtml(spec.name)}</span>
            <span class="inline-ref-module">${escapeHtml(spec.module)}</span>
            ${hasMath ? `<span class="inline-ref-math">${escapeHtml(spec.math_interpretation)}</span>` : ""}
        </div>
        <div class="inline-ref-body">
            <pre><code class="language-rust">${escapedBody}</code></pre>
            ${nestedRefsHtml}
        </div>
    </div>`;
}

function renderSpecCard(spec) {
    const isAxiom = spec.category === "axiom";
    const hasMath = spec.math_interpretation && spec.math_interpretation.trim();
    const axiomBadge = isAxiom ? `<span class="axiom-badge">AXIOM</span>` : "";

    // Render only the header; body is injected lazily on first open
    return `
    <div class="spec-card${isAxiom ? " axiom-card" : ""}" data-id="${escapeAttr(spec.id)}" data-spec-name="${escapeAttr(spec.name)}" data-module="${escapeAttr(spec.module)}" data-category="${escapeAttr(spec.category || "spec")}">
        <div class="spec-header">
            <div class="spec-toggle">&#9654;</div>
            <div class="spec-info">
                <div class="spec-name">${escapeHtml(spec.name)} ${axiomBadge}</div>
                <div class="spec-meta">
                    <span class="spec-module">${escapeHtml(spec.module)}</span>
                    ${spec.visibility && !isAxiom ? `<span class="spec-visibility">${escapeHtml(spec.visibility)}</span>` : ""}
                    ${hasMath ? `<span class="spec-math">${escapeHtml(spec.math_interpretation)}</span>` : ""}
                </div>
            </div>
            <a class="spec-github" href="${escapeAttr(spec.github_link)}" target="_blank" rel="noopener"
               title="View source on GitHub" onclick="event.stopPropagation()">
                Source &nearr;
            </a>
        </div>
        <div class="spec-body"></div>
    </div>`;
}

/** Populate a spec-function card body on first open. */
function inflateSpecBody(card) {
    if (card.dataset.inflated) return;
    card.dataset.inflated = "1";

    const specName = card.dataset.specName;
    const spec = specLookup[specName];
    if (!spec) return;

    const isAxiom = spec.category === "axiom";
    const hasDoc = spec.doc_comment && spec.doc_comment.trim();
    const hasMath = spec.math_interpretation && spec.math_interpretation.trim();
    const hasInformal = spec.informal_interpretation && spec.informal_interpretation.trim();
    const hasInterpretations = hasMath || hasInformal;
    const hasRefs = spec.referenced_specs && spec.referenced_specs.length > 0;

    const docHtml = hasDoc
        ? spec.doc_comment.split("\n").filter(Boolean).map(p => `<p>${escapeHtml(p)}</p>`).join("")
        : "";

    const visited = new Set([spec.name]);
    const inlineRefsHtml = hasRefs ? `
        <div class="inline-refs-container">
            <div class="inline-refs-label">Referenced specs <span class="refs-count">${spec.referenced_specs.length}</span></div>
            ${spec.referenced_specs.map(refName => {
                const refSpec = specLookup[refName];
                if (!refSpec) return `<div class="inline-ref-card"><div class="inline-ref-header"><span class="inline-ref-name">${escapeHtml(refName)}</span><span class="inline-ref-missing">not found</span></div></div>`;
                return renderInlineRefCard(refSpec, visited);
            }).join("")}
        </div>` : "";

    const body = card.querySelector(".spec-body");
    body.innerHTML = `
        ${hasDoc ? `<div class="spec-doc">${docHtml}</div>` : ""}
        ${(() => {
            if (isAxiom) {
                return hasMath ? `
                <div class="spec-interpretations">
                    <div class="spec-interp"><span class="spec-interp-label">Math:</span> <span class="spec-interp-value">${escapeHtml(spec.math_interpretation)}</span></div>
                </div>` : "";
            }
            return hasInterpretations ? `
            <div class="spec-interpretations">
                ${hasMath ? `<div class="spec-interp"><span class="spec-interp-label">Math:</span> <span class="spec-interp-value">${escapeHtml(spec.math_interpretation)}</span></div>` : ""}
                ${hasInformal ? `<div class="spec-interp"><span class="spec-interp-label">Meaning:</span> <span class="spec-interp-value">${escapeHtml(spec.informal_interpretation)}</span></div>` : ""}
            </div>` : "";
        })()}
        <div class="spec-code-wrapper">
            <button class="copy-btn">Copy</button>
            <pre><code class="language-rust">${escapeHtml(spec.body)}</code></pre>
        </div>
        ${inlineRefsHtml}
        <div class="spec-comments">
            <button class="comments-toggle" data-fn-id="${escapeAttr(spec.id)}">
                <span>Comments</span>
                <span class="comment-count" id="count-${escapeAttr(spec.id)}">...</span>
            </button>
            <div class="comments-content" id="comments-${spec.id}"></div>
        </div>`;

    // Syntax highlight
    body.querySelectorAll("pre code.language-rust").forEach(b => {
        Prism.highlightElement(b);
        b.classList.add("prism-highlighted");
    });

    // Wire up copy button
    body.querySelectorAll(".copy-btn").forEach(btn => {
        btn.addEventListener("click", e => {
            e.stopPropagation();
            const code = btn.closest(".spec-code-wrapper").querySelector("code").textContent;
            navigator.clipboard.writeText(code).then(() => {
                btn.textContent = "Copied!";
                setTimeout(() => { btn.textContent = "Copy"; }, 1500);
            });
        });
    });

    // Wire up comment toggle
    body.querySelectorAll(".comments-toggle").forEach(btn => {
        btn.addEventListener("click", () => {
            const content = btn.nextElementSibling;
            if (!content) return;
            content.classList.toggle("open");
            if (content.classList.contains("open")) {
                loadComments(btn.dataset.fnId, content);
            }
        });
    });

    // Wire up inline ref toggles
    body.querySelectorAll(".inline-ref-header").forEach(h => {
        h.addEventListener("click", e => {
            e.stopPropagation();
            const refCard = h.closest(".inline-ref-card");
            refCard.classList.toggle("open");
            if (refCard.classList.contains("open")) {
                refCard.querySelectorAll("pre code.language-rust:not(.prism-highlighted)").forEach(b => {
                    Prism.highlightElement(b);
                    b.classList.add("prism-highlighted");
                });
            }
        });
    });
}

// ── Spec filter (from "Show referenced specs" button) ────────
function setSpecFilter(refNames, sourceName) {
    specFilterRefs = new Set(refNames);
    specFilterSource = sourceName;
    renderRightPanel();
    // Scroll the right panel's own scroll container to top (not the page)
    const rightScroll = document.querySelector(".panel-right .panel-scroll");
    if (rightScroll) rightScroll.scrollTop = 0;
}

function clearSpecFilter() {
    specFilterRefs = null;
    specFilterSource = "";
    renderRightPanel();
}

// ── Scroll to and highlight a spec card on the right ─────────
let autoFilterBypassed = false;  // true when we showed all specs to reach a target

function scrollToSpecCard(specName) {
    // If the right panel is filtered by "Focus referenced specs" and the
    // target isn't in that set, clear the per-function filter first.
    if (specFilterRefs && !specFilterRefs.has(specName)) {
        clearSpecFilter();
    }

    // Find the card
    let card = document.querySelector(`.panel-right .spec-card[data-spec-name="${cssSelectorEscape(specName)}"]`);

    // If the card isn't in the DOM it may be hidden by the auto-filter
    // (left-panel module/public/libsignal filters).  Bypass the auto-filter
    // so the full spec list renders, then scroll to the target.
    if (!card && hasLeftFilter()) {
        autoFilterBypassed = true;
        renderRightPanel();
        card = document.querySelector(`.panel-right .spec-card[data-spec-name="${cssSelectorEscape(specName)}"]`);
    }

    if (!card) return;

    // Inflate & open it
    inflateSpecBody(card);
    card.classList.add("open");

    // Highlight briefly
    card.classList.add("highlight-card");
    setTimeout(() => card.classList.remove("highlight-card"), 2500);

    // Scroll within the right panel's own scroll container (not the page)
    const rightScroll = document.querySelector(".panel-right .panel-scroll");
    if (rightScroll) {
        const cardTop = card.offsetTop - rightScroll.offsetTop;
        rightScroll.scrollTo({ top: cardTop - 20, behavior: "smooth" });
    }
}

// ── Highlight spec names in contract text ────────────────────
function highlightSpecNames(contractText, referencedSpecs) {
    if (!referencedSpecs || referencedSpecs.length === 0) {
        return escapeHtml(contractText);
    }

    const sortedSpecs = [...referencedSpecs].sort((a, b) => b.length - a.length);
    const pattern = new RegExp(
        `\\b(${sortedSpecs.map(s => s.replace(/[.*+?^${}()|[\]\\]/g, '\\$&')).join("|")})\\b`,
        "g"
    );

    const segments = [];
    let lastIndex = 0;
    let match;

    while ((match = pattern.exec(contractText)) !== null) {
        if (match.index > lastIndex) {
            segments.push({ type: "text", value: contractText.slice(lastIndex, match.index) });
        }
        segments.push({ type: "spec", value: match[1] });
        lastIndex = pattern.lastIndex;
    }
    if (lastIndex < contractText.length) {
        segments.push({ type: "text", value: contractText.slice(lastIndex) });
    }

    return segments.map(seg => {
        if (seg.type === "spec") {
            return `<span class="spec-link" data-spec="${escapeAttr(seg.value)}" title="Click to view definition">${escapeHtml(seg.value)}</span>`;
        }
        return escapeHtml(seg.value);
    }).join("");
}

// ── Expand / Collapse All ────────────────────────────────────
// ── Comments (Firebase) ──────────────────────────────────────
async function loadComments(functionId, container) {
    if (!FIREBASE_ENABLED || !db) {
        container.innerHTML = `
            <div class="firebase-notice">
                Commenting is not yet configured.<br>
                See <code>specs.js</code> FIREBASE_CONFIG to enable.
            </div>`;
        return;
    }

    container.innerHTML = `
        <div class="comment-list" id="list-${functionId}">
            <div class="comment-empty">Loading comments...</div>
        </div>
        <div class="comment-form">
            <input type="text" placeholder="Your name (optional)" maxlength="100" id="name-${functionId}">
            <textarea placeholder="Your comment..." maxlength="2000" id="msg-${functionId}"></textarea>
            <button onclick="submitComment('${functionId}')">Post Comment</button>
        </div>`;

    try {
        const snapshot = await db.collection("comments")
            .where("functionId", "==", functionId)
            .orderBy("timestamp", "asc")
            .get();
        const comments = [];
        snapshot.forEach(doc => comments.push({ id: doc.id, ...doc.data() }));
        commentsCache[functionId] = comments;
        renderComments(functionId, comments);
        const countEl = document.getElementById(`count-${functionId}`);
        if (countEl) countEl.textContent = comments.length;
    } catch (err) {
        console.error("Error loading comments:", err);
        const listEl = document.getElementById(`list-${functionId}`);
        if (listEl) listEl.innerHTML = `<div class="comment-empty">Could not load comments.</div>`;
    }
}

function renderComments(functionId, comments) {
    const listEl = document.getElementById(`list-${functionId}`);
    if (!listEl) return;
    if (comments.length === 0) {
        listEl.innerHTML = `<div class="comment-empty">No comments yet. Be the first!</div>`;
        return;
    }
    const currentHash = contentHashes[functionId] || "";
    let html = comments.map(c => {
        // A comment is outdated if it has a contentHash that differs from current
        const isOutdated = c.contentHash && currentHash && c.contentHash !== currentHash;
        const outdatedClass = isOutdated ? " outdated" : "";
        const outdatedBadge = isOutdated
            ? `<span class="comment-outdated-badge">earlier version</span>`
            : "";
        const displayName = c.name || "anonymous";
        return `
            <div class="comment-item${outdatedClass}">
                <span class="comment-author">${escapeHtml(displayName)}</span>
                ${outdatedBadge}
                <div class="comment-text">${escapeHtml(c.message)}</div>
                <button class="comment-delete-btn" onclick="deleteComment('${functionId}','${c.id}')" title="Delete">Delete</button>
            </div>`;
    }).join("");
    listEl.innerHTML = html;
}

window.submitComment = async function(functionId) {
    if (!db) return;
    const nameInput = document.getElementById(`name-${functionId}`);
    const msgInput = document.getElementById(`msg-${functionId}`);
    const name = nameInput.value.trim() || "anonymous";
    const message = msgInput.value.trim();
    if (!message) {
        alert("Please enter a comment.");
        return;
    }
    const btn = msgInput.closest(".comment-form").querySelector("button");
    btn.disabled = true;
    btn.textContent = "Posting...";
    try {
        await db.collection("comments").add({
            functionId, name, message,
            contentHash: contentHashes[functionId] || "",
            timestamp: firebase.firestore.FieldValue.serverTimestamp()
        });
        nameInput.value = "";
        msgInput.value = "";
        const container = document.getElementById(`comments-${functionId}`);
        if (container) await loadComments(functionId, container);
    } catch (err) {
        console.error("Error posting comment:", err);
        alert("Failed to post comment. Please try again.");
    } finally {
        btn.disabled = false;
        btn.textContent = "Post Comment";
    }
};

window.deleteComment = async function(functionId, docId) {
    if (!db) return;
    try {
        await db.collection("comments").doc(docId).delete();
        const container = document.getElementById(`comments-${functionId}`);
        if (container) await loadComments(functionId, container);
    } catch (err) {
        console.error("Error deleting comment:", err);
        alert("Failed to delete comment.");
    }
};

// ── Content hashing (for comment version tracking) ──────────
// Fast synchronous djb2 hash — produces a short hex string fingerprint
function computeContentHash(text) {
    if (!text) return "";
    let hash = 5381;
    for (let i = 0; i < text.length; i++) {
        hash = ((hash << 5) + hash + text.charCodeAt(i)) & 0xffffffff;
    }
    return (hash >>> 0).toString(16).padStart(8, "0");
}

function buildContentHashes() {
    for (const spec of specFunctions) {
        contentHashes[spec.id] = computeContentHash(spec.body || "");
    }
    for (const fn of verifiedFunctions) {
        contentHashes[fn.id] = computeContentHash(fn.contract || "");
    }
}

// ── Download helpers ─────────────────────────────────────────
function triggerDownload(content, filename, mime) {
    const blob = new Blob([content], { type: mime });
    const a = document.createElement("a");
    a.href = URL.createObjectURL(blob);
    a.download = filename;
    a.click();
    URL.revokeObjectURL(a.href);
}

/**
 * Build a filename suffix that reflects the active filters.
 * E.g. "verus-specs-edwards-public-libsignal.md"
 */
function downloadFilenameSuffix() {
    const parts = ["verus-specs"];
    if (activeModules.size > 0) {
        parts.push([...activeModules].sort().map(m => m.replace(/::/g, "-")).join("+"));
    }
    if (filterPublic) parts.push("public");
    if (filterLibsignal) parts.push("libsignal");
    return parts.join("-");
}

window.downloadMarkdown = function() {
    try {
        const filteredLeft = getFilteredVerified();
        const filteredRight = getFilteredSpecs();

        let md = "# Verified Function Specifications\n\n";

        md += `## Function Contracts (${filteredLeft.length})\n\n`;
        for (const fn of filteredLeft) {
            md += `### ${fn.display_name || fn.name}\n\n`;
            md += `**Module:** ${fn.module}  \n`;
            if (fn.informal_interpretation) md += `**Meaning:** ${fn.informal_interpretation}  \n`;
            md += `\n\`\`\`rust\n${fn.contract || ""}\n\`\`\`\n\n`;
            if (fn.referenced_specs && fn.referenced_specs.length) {
                md += `**Uses spec functions:** ${fn.referenced_specs.join(", ")}  \n\n`;
            }
            md += "---\n\n";
        }

        const specs = filteredRight.filter(s => s.category !== "axiom");
        if (specs.length) {
            md += `## Spec Functions (${specs.length})\n\n`;
            for (const s of specs) {
                md += `### ${s.name}\n\n`;
                md += `**Module:** ${s.module}  \n`;
                if (s.math_interpretation) md += `**Math:** ${s.math_interpretation}  \n`;
                if (s.informal_interpretation) md += `**Meaning:** ${s.informal_interpretation}  \n`;
                md += `\n\`\`\`rust\n${s.body || ""}\n\`\`\`\n\n---\n\n`;
            }
        }

        const axioms = filteredRight.filter(s => s.category === "axiom");
        if (axioms.length) {
            md += `## Axioms (${axioms.length})\n\n`;
            for (const a of axioms) {
                md += `### ${a.name}\n\n`;
                if (a.math_interpretation) md += `**Math:** ${a.math_interpretation}  \n`;
                if (a.informal_interpretation) md += `**Meaning:** ${a.informal_interpretation}  \n`;
                md += `\n\`\`\`rust\n${a.body || ""}\n\`\`\`\n\n---\n\n`;
            }
        }

        triggerDownload(md, `${downloadFilenameSuffix()}.md`, "text/markdown;charset=utf-8");
    } catch (e) {
        console.error("Download MD failed:", e);
        alert("Download failed — see console for details.");
    }
};

window.downloadCSV = function() {
    try {
        const filteredLeft = getFilteredVerified();
        const filteredRight = getFilteredSpecs();

        const esc = v => {
            if (v == null) return "";
            const s = String(v).replace(/"/g, '""');
            return (s.includes(",") || s.includes('"') || s.includes("\n")) ? `"${s}"` : s;
        };

        let csv = "category,name,module,math_interpretation,informal_interpretation,code\n";

        for (const fn of filteredLeft) {
            csv += [
                esc("contract"), esc(fn.display_name || fn.name), esc(fn.module),
                esc(""), esc(fn.informal_interpretation), esc(fn.contract)
            ].join(",") + "\n";
        }
        for (const s of filteredRight) {
            csv += [
                esc(s.category || "spec"), esc(s.name), esc(s.module),
                esc(s.math_interpretation), esc(s.informal_interpretation), esc(s.body)
            ].join(",") + "\n";
        }

        triggerDownload(csv, `${downloadFilenameSuffix()}.csv`, "text/csv;charset=utf-8");
    } catch (e) {
        console.error("Download CSV failed:", e);
        alert("Download failed — see console for details.");
    }
};

// ── Utilities ────────────────────────────────────────────────
function escapeHtml(str) {
    if (!str) return "";
    const div = document.createElement("div");
    div.textContent = str;
    return div.innerHTML;
}

// Escape a string for safe use inside an HTML attribute value (double-quoted).
function escapeAttr(str) {
    if (!str) return "";
    return String(str).replace(/&/g, "&amp;").replace(/"/g, "&quot;").replace(/</g, "&lt;").replace(/>/g, "&gt;");
}

// Escape a string for safe use inside a CSS attribute selector value.
function cssSelectorEscape(str) {
    if (!str) return "";
    if (typeof CSS !== "undefined" && typeof CSS.escape === "function") return CSS.escape(str);
    // Fallback: escape special chars
    return String(str).replace(/([!"#$%&'()*+,.\/:;<=>?@[\\\]^`{|}~])/g, "\\$1");
}
