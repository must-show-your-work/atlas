/*
 * card.js — shared card rendering for the atlas viewer.
 *
 * Ported (verbatim where possible) from `graph.html`'s inline helpers
 * so the TOC viewer and graph viewer can use the same renderers. The
 * Lean → LaTeX → KaTeX pipeline, the side-by-side commentary view,
 * the source highlighter, and the per-marker rendering all live here.
 *
 * Everything is attached to `window.AtlasCard`. KaTeX must already be
 * loaded on the page (the renderTypeHtmlFromTex call uses it).
 *
 * `window.markersByDecl` and `window.commentaryByDecl` are consulted
 * for the side-by-side source rendering and commentary section. The
 * loader pages (toc.html, graph.html) populate those before calling
 * any render function that needs them.
 */
(function () {
'use strict';

// ---------- HTML escapes ----------

function escapeHtml(s) {
  return String(s ?? '').replace(/[&<>"']/g, c => ({
    '&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;',"'":'&#39;'
  }[c]));
}

function escapeMath(s) {
  // KaTeX has special meanings for `#`, `%`, `&`, `~`, `^`, `$`, `\`.
  // Of these, Lean type signatures typically only emit `_` (rarely
  // `^`). Replace `_` so it isn't interpreted as a subscript.
  return s.replace(/_/g, '\\_');
}

// ---------- Lean source highlighter ----------

const LEAN_KEYWORDS = new Set([
  'theorem','lemma','axiom','def','example','instance','class','structure','inductive',
  'namespace','end','section','open','import','attribute','alias','noncomputable',
  'private','protected','public','meta','partial','mutual','where','with','do',
  'if','then','else','match','let','fun','have','show','suffices','from',
  'by','at','in','as','of','intro','intros','exact','apply','refine','rcases',
  'obtain','rw','rewrite','simp','simp_all','tauto','trivial','contradiction',
  'use','constructor','left','right','split','exfalso','by_contra','push_neg',
  'unfold','separate','distinguish','obvious','clearly','calc',
  'forall','exists','True','False',
  'atlas','ref','proposition','corollary','exercise','remark','postulate',
  'alternate','definition',
]);

function highlightLean(src) {
  const out = [];
  let i = 0, n = src.length;
  const push = (kind, text) =>
    out.push(kind ? `<span class="lean-${kind}">${escapeHtml(text)}</span>` : escapeHtml(text));
  while (i < n) {
    const c = src[i];
    if (c === '-' && src[i+1] === '-') {
      let j = src.indexOf('\n', i);
      if (j < 0) j = n;
      push('cmt', src.slice(i, j));
      i = j; continue;
    }
    if (c === '/' && src[i+1] === '-') {
      let j = src.indexOf('-/', i + 2);
      j = j < 0 ? n : j + 2;
      push('cmt', src.slice(i, j));
      i = j; continue;
    }
    if (c === '"') {
      let j = i + 1;
      while (j < n && src[j] !== '"') {
        if (src[j] === '\\' && j + 1 < n) j += 2; else j++;
      }
      j = Math.min(j + 1, n);
      push('str', src.slice(i, j));
      i = j; continue;
    }
    if (c === '«') {
      let j = src.indexOf('»', i + 1);
      j = j < 0 ? n : j + 1;
      push('const', src.slice(i, j));
      i = j; continue;
    }
    if (/[A-Za-z_]/.test(c)) {
      let j = i + 1;
      while (j < n && /[A-Za-z0-9_'.]/.test(src[j])) j++;
      const word = src.slice(i, j);
      if (!word.includes('.') && LEAN_KEYWORDS.has(word)) {
        push('kw', word);
      } else if (/^[A-Z]/.test(word)) {
        push('const', word);
      } else {
        push('var', word);
      }
      i = j; continue;
    }
    if (/[0-9]/.test(c)) {
      let j = i + 1;
      while (j < n && /[0-9.]/.test(src[j])) j++;
      push('num', src.slice(i, j));
      i = j; continue;
    }
    push(null, c);
    i++;
  }
  return out.join('');
}

// ---------- LaTeX → KaTeX ----------


function texToKatexHtml(tex, { displayMode = false } = {}) {
  if (!tex) return '';
  if (typeof katex === 'undefined') {
    return `<span class="fallback">${escapeHtml(tex)} [katex not loaded]</span>`;
  }
  try {
    const html = katex.renderToString(tex, {
      displayMode, throwOnError: false, strict: 'ignore', output: 'html',
      errorColor: '#983327',
    });
    return html || `<span class="fallback">${escapeHtml(tex)} [empty render]</span>`;
  } catch (err) {
    return `<span class="fallback">${escapeHtml(tex)} [${escapeHtml(err.message)}]</span>`;
  }
}


// Find indices of `\to` / `\wedge` tokens that sit at the top level
// of `tex` (not inside any `(...)` or `{...}`). Used by
// `breakAtTopLevelArrows` to insert line breaks at every top-level
// connective so the statement reads as a vertical list.
function topLevelBreakPositions(tex) {
  const out = [];
  let depth = 0;
  for (let i = 0; i < tex.length - 2; i++) {
    const c = tex[i];
    if (c === '\\') {
      if (depth === 0) {
        // Recognise the connectives we break at. Each must be
        // followed by a non-letter char so we don't match `\toot`
        // or similar prefixes.
        if (tex.substr(i, 3) === '\\to' && /\W|$/.test(tex[i+3] || '')) {
          out.push({ pos: i, len: 3, kind: 'to' });
        } else if (tex.substr(i, 6) === '\\wedge' && /\W|$/.test(tex[i+6] || '')) {
          out.push({ pos: i, len: 6, kind: 'wedge' });
        }
      }
      // Skip past the macro name.
      let j = i + 1;
      while (j < tex.length && /[A-Za-z]/.test(tex[j])) j++;
      i = j - 1;
      continue;
    }
    if (c === '(' || c === '{') depth++;
    else if (c === ')' || c === '}') depth--;
  }
  return out;
}

// Strip parens around predicate atoms — `(L \text{ intersects } \overline{AC})`
// adds visual noise inside `… ∨ … ∧ …` chains and the parens carry no
// precedence information when the contents have no top-level binary
// operator. Iterate to fixed point so nested `((…))` peels both layers.
function stripPredicateParens(tex) {
  let prev;
  do {
    prev = tex;
    tex = tex.replace(/\(([^()]+?)\)/g, (m, inner) =>
      /\\to\b|\\wedge\b|\\vee\b|\\implies\b|\\Leftrightarrow\b/.test(inner) ? m : inner);
  } while (tex !== prev);
  return tex;
}

// Insert breaks at top-level `\to` / `\wedge` so the statement reads
// vertically: each hypothesis on its own line, conjuncts of the
// conclusion stacked underneath the implication arrow. Every row
// starts with `&` so the `aligned` environment left-aligns the
// whole stack at a single column.
//
// The LAST `\to` (separating the final hypothesis from the
// conclusion) is upgraded to `\implies` and gets `[10pt]` of extra
// vertical space above it, so hypothesis-block and conclusion-block
// read as visually distinct chunks.
// Find the position of the comma that closes the quantifier section
// (the run of `\forall <name> : <type>` prefixes). Returns -1 if the
// statement has no quantifier prefix. Locates the LAST top-level
// ` : ` token — which always appears inside a binder, never inside
// the hypothesis chain — and breaks at the next top-level comma
// after it. Robust against both the regex pipeline's
// `\forall A B C : Point, L : Line, body` shape and the LeanTeX
// `\forall A B C : Point, \forall L : Line, body` shape.
function findQuantifierEndPos(tex) {
  let lastColonEnd = -1;
  let depth = 0;
  let i = 0;
  while (i < tex.length - 3) {
    const c = tex[i];
    if (c === '\\') {
      let j = i + 1;
      while (j < tex.length && /[A-Za-z]/.test(tex[j])) j++;
      i = j;
      continue;
    }
    if (c === '(' || c === '{') { depth++; i++; continue; }
    if (c === ')' || c === '}') { depth--; i++; continue; }
    if (depth === 0 && tex.substr(i, 3) === ' : ') {
      lastColonEnd = i + 3;
      i = lastColonEnd;
      continue;
    }
    i++;
  }
  if (lastColonEnd === -1) return -1;
  let pos = lastColonEnd;
  depth = 0;
  while (pos < tex.length) {
    const c = tex[pos];
    if (c === '\\') {
      let j = pos + 1;
      while (j < tex.length && /[A-Za-z]/.test(tex[j])) j++;
      pos = j;
      continue;
    }
    if (c === '(' || c === '{') { depth++; pos++; continue; }
    if (c === ')' || c === '}') { depth--; pos++; continue; }
    if (c === ',' && depth === 0) return pos;
    pos++;
  }
  return -1;
}

function breakAtTopLevelArrows(tex) {
  const arrowBreaks = topLevelBreakPositions(tex);
  const qEndPos = findQuantifierEndPos(tex);
  // Stitch the quantifier-section terminator into the same break
  // sequence as the arrows; arrow breaks before the quantifier end
  // would mean a paren-depth bookkeeping error, so just drop them.
  const breaks = [];
  if (qEndPos !== -1) {
    breaks.push({ pos: qEndPos, len: 1, kind: 'qend' });
  }
  for (const b of arrowBreaks) {
    if (b.pos > qEndPos) breaks.push(b);
  }
  if (breaks.length === 0) return tex;
  // Inline `\wedge` breaks when both conjuncts are short — `A \wedge B`
  // shouldn't fragment onto two lines if the entire conjunction fits
  // comfortably alongside its neighbouring connectives. Threshold tuned
  // for the common `<dash chain> \wedge <dash chain>` shape; long
  // parenthesized conjuncts (Pasch's conclusion) still break.
  const WEDGE_INLINE_MAX = 30;
  const filteredBreaks = [];
  for (let k = 0; k < breaks.length; k++) {
    const b = breaks[k];
    if (b.kind === 'wedge') {
      const prevEnd = k > 0 ? breaks[k - 1].pos + breaks[k - 1].len : 0;
      const nextStart = k + 1 < breaks.length ? breaks[k + 1].pos : tex.length;
      const lhs = tex.substring(prevEnd, b.pos).trim();
      const rhs = tex.substring(b.pos + b.len, nextStart).trim();
      if (lhs.length < WEDGE_INLINE_MAX && rhs.length < WEDGE_INLINE_MAX) continue;
    }
    filteredBreaks.push(b);
  }
  if (filteredBreaks.length === 0) return tex;
  breaks.length = 0;
  Array.prototype.push.apply(breaks, filteredBreaks);
  // Find the LAST top-level `\to` — that's the conclusion arrow.
  let lastToIdx = -1;
  for (let i = 0; i < breaks.length; i++) {
    if (breaks[i].kind === 'to') lastToIdx = i;
  }
  const pieces = [];
  let cursor = 0;
  for (let i = 0; i < breaks.length; i++) {
    const b = breaks[i];
    pieces.push(tex.substring(cursor, b.pos).trimEnd());
    const isConclusionArrow = i === lastToIdx;
    if (b.kind === 'qend') {
      pieces.push(', \\\\\n  &');
    } else if (isConclusionArrow) {
      pieces.push(' \\\\[10pt]\n  &\\implies\\ ');
    } else if (b.kind === 'wedge') {
      pieces.push(' \\\\\n  &\\wedge\\ ');
    } else {
      pieces.push(' \\\\\n  &\\to\\ ');
    }
    cursor = b.pos + b.len;
    while (cursor < tex.length && /\s/.test(tex[cursor])) cursor++;
  }
  pieces.push(tex.substring(cursor));
  return `\\begin{aligned}\n  &${pieces.join('')}\n\\end{aligned}`;
}


// Render a finished LaTeX string (from LeanTeX's AST-walking pretty
// printer) to KaTeX-rendered HTML. Translates word-form connectives
// (`\implies`, `\mathrm{and}`, `\mathrm{or}`) to math symbols, strips
// redundant predicate parens, then breaks at top-level connectives so
// the statement reads as a multi-line aligned block.
function renderTypeHtmlFromTex(latexString, opts = {}) {
  if (!latexString) return '';
  let tex = latexString
    .replace(/\\implies\b/g, '\\to')
    .replace(/\\mathrel\{\\mathrm\{and\}\}/g, '\\wedge')
    .replace(/\\mathrel\{\\mathrm\{or\}\}/g, '\\vee');
  tex = stripPredicateParens(tex);
  tex = breakAtTopLevelArrows(tex);
  return texToKatexHtml(tex, { ...opts, displayMode: true });
}

// ---------- Markers + side-by-side source ----------

function renderMarkerLeft(m) {
  // Every marker gets a `data-line` attribute carrying its source-
  // line anchor. The click handler in toc.html treats marker blocks
  // exactly like `.bn-line` source spans — a click toggles a line
  // flag at `m.line`. Lets reviewers flag a specific quoting /
  // comment without needing to dig out the original source line.
  const line = (typeof m.line === 'number') ? m.line : 0;
  const lineAttr = `data-line="${line}"`;
  if (m._kind === 'quoting') {
    const isExplicit = m.step != null;
    const stepChip = isExplicit
      ? `<span class="bn-step">(${m.step})</span>`
      : `<span class="bn-step bn-step-cont">…</span>`;
    const pageChip = (isExplicit && m.resolvedPage != null)
      ? `<span class="bn-page">p.${m.resolvedPage}</span>` : '';
    const trail = m.trailing ? '<span class="bn-ellipsis">…</span>' : '';
    // Wrap chips in a single grid-column slot so step + page stay
    // together regardless of how many chips a marker carries.
    return `<div class="bn-marker bn-marker-quoting" ${lineAttr}>
      <span class="bn-chip-slot">${stepChip}${pageChip}</span><span class="bn-text">${escapeHtml(m.text)}${trail}</span>
    </div>`;
  }
  if (m._kind === 'comment') {
    return `<div class="bn-marker bn-marker-comment" ${lineAttr}>
      <span class="bn-chip-slot"><span class="bn-chip">Ed.</span></span><span class="bn-text">${escapeHtml(m.text)}</span>
    </div>`;
  }
  if (m._kind === 'page_break') {
    return `<div class="bn-marker bn-marker-pagebreak" ${lineAttr}>
      <span class="bn-rule"></span><span class="bn-pagebreak-label">page break</span><span class="bn-rule"></span>
    </div>`;
  }
  const extendedKinds = new Set([
    'idea','intuition','motivation','caution','aside','cf','todo','fixme','detail'
  ]);
  if (extendedKinds.has(m._kind)) {
    return `<div class="bn-marker bn-marker-${m._kind}" ${lineAttr}>
      <span class="bn-chip-slot"><span class="bn-chip bn-chip-${m._kind}">${m._kind}</span></span><span class="bn-text">${escapeHtml(m.text)}</span>
    </div>`;
  }
  if (m._kind === 'aux-figure') {
    // Inline figure delta from an `auxillary { … }` block: a small
    // SVG embedded next to the proof step that introduces it. Sits
    // in the RHS commentary column at the slid-forward anchor line.
    const desc = m.description
      ? `<div class="aux-figure-desc">${escapeHtml(m.description)}</div>` : '';
    return `<div class="bn-marker bn-marker-aux-figure" ${lineAttr}>
      <span class="bn-chip-slot"><span class="bn-chip bn-chip-aux-figure">fig</span></span>
      <div class="bn-text aux-figure-body">
        <div class="aux-figure-svg">${m.svg || ''}</div>
        ${desc}
      </div>
    </div>`;
  }
  return '';
}

// Wrap each line of source in a `bn-line` span tagged with the
// absolute file line number, so the line-flag UI can address it by
// click. Highlighting runs per-line so token <span>s stay nested
// inside their owning line.
function wrapLines(text, baseLine) {
  const lines = text.split('\n');
  return lines.map((line, i) => {
    const abs = baseLine + i;
    const inner = highlightLean(line) || '&nbsp;';
    return `<span class="bn-line" data-line="${abs}">${inner}</span>`;
  }).join('\n');
}

function renderSourceWithMarkers(d) {
  const source = d.source || '';
  if (!source) return { hasMarkers: false, html: '' };
  const baseLine = d.line_start || 1;
  const ms = (window.markersByDecl && window.markersByDecl[d.id]) || null;
  if (!ms || ms.length === 0) {
    return {
      hasMarkers: false,
      html: `<pre class="bn-source-plain">${wrapLines(source, baseLine)}</pre>`,
    };
  }

  const markersByLine = {};
  for (const m of ms) {
    (markersByLine[m.line] ||= []).push(m);
  }
  const lines = source.split('\n');

  // Each segment tracks `firstLine` — the absolute file line where its
  // codeLines start. The renderer below uses that to give each code
  // line a `data-line` attribute, so the line-flag UI can address
  // individual lines even when they're split across marker boundaries.
  const segments = [{ marker: null, codeLines: [], firstLine: baseLine }];
  for (let i = 0; i < lines.length; i++) {
    const absLine = baseLine + i;
    const here = markersByLine[absLine];
    if (here) {
      for (const mk of here) {
        segments.push({ marker: mk, codeLines: [], firstLine: absLine + 1 });
      }
      continue;
    }
    segments[segments.length - 1].codeLines.push(lines[i]);
  }
  const cleanSegs = segments.filter(seg =>
    seg.marker !== null || seg.codeLines.some(l => l.trim() !== ''));

  const rows = cleanSegs.map(seg => {
    const left = seg.marker ? renderMarkerLeft(seg.marker) : '';
    const codeText = seg.codeLines.join('\n');
    const right = codeText.trim() === ''
      ? '' : `<pre class="bn-code">${wrapLines(codeText, seg.firstLine)}</pre>`;
    return `<div class="bn-seg"><div class="bn-seg-left">${left}</div><div class="bn-seg-right">${right}</div></div>`;
  }).join('');

  return { hasMarkers: true, html: `<div class="bn-grid">${rows}</div>` };
}

// ---------- Commentary section ----------

function renderCommentarySection(declId) {
  const cb = (window.commentaryByDecl && window.commentaryByDecl[declId]) || null;
  if (!cb) return '';
  const pageChip = cb.page
    ? `<span class="cb-page">📖 p.${escapeHtml(cb.page)}${cb.page_end ? '–' + escapeHtml(cb.page_end) : ''}</span>` : '';
  const nameLine = cb.name ? `<div class="cb-name">${escapeHtml(cb.name)}</div>` : '';
  const aliasesChips = (cb.aliases && cb.aliases.length)
    ? `<div class="cb-aliases">aka: ${cb.aliases.map(a =>
        `<span class="cb-alias-chip">${escapeHtml(a)}</span>`).join(' ')}</div>` : '';
  const tagsChips = (cb.tags && cb.tags.length)
    ? `<div class="cb-tags">${cb.tags.map(t =>
        `<span class="cb-tag-chip">#${escapeHtml(t)}</span>`).join(' ')}</div>` : '';
  const preface = cb.preface ? `<blockquote class="cb-preface">${escapeHtml(cb.preface)}</blockquote>` : '';
  const notes = cb.notes ? `<div class="cb-notes"><span class="cb-notes-label">Ed.</span> ${escapeHtml(cb.notes)}</div>` : '';
  return `
    <section class="card-section card-commentary">
      <div class="card-section-label">commentary</div>
      <div class="cb-body">
        <div class="cb-head">${nameLine}${pageChip}</div>
        ${aliasesChips}${tagsChips}${preface}${notes}
      </div>
    </section>`;
}

// ---------- Editorial card ----------

// Wrap a section body in the standard card-section template. When
// `withFlag` is true (toc viewer), a flag toggle button is rendered
// for the per-section flag UI; graph viewer disables flags.
function flaggableSection(name, label, body, withFlag = true) {
  const safeName = escapeHtml(name);
  const flagBtn = withFlag
    ? `<button class="flag-btn" data-flag-section="${safeName}">flag</button>` : '';
  return `
    <section class="card-section" data-section="${safeName}">
      ${flagBtn}
      <div class="card-section-label">${escapeHtml(label)}</div>
      ${body}
    </section>`;
}

// Compute the set of absolute file lines we drop from the proof
// source column. Two categories: the decl prelude (everything from
// `atlas <kind> <num> "…"` / `theorem foo …` through the line with
// `:= by`) and marker syntax (`quoting …` / `comment …` / `idea …`
// / etc. — whose parsed text already shows in the LHS/RHS proof
// columns). `auxillary { … }` blocks also elide here.
const MARKER_KW = /^\s*(?:·\s+)?(quoting|comment|idea|intuition|motivation|caution|aside|cf|todo|fixme|detail|page_break)\b/;
function computeMarkerLines(source, baseLine) {
  const elided = new Set();
  const lines = source.split('\n');

  let preludeEnd = -1;
  for (let i = 0; i < lines.length; i++) {
    const code = lines[i].replace(/--.*/, '').trimEnd();
    if (code.endsWith(':= by')) { preludeEnd = i; break; }
  }
  for (let i = 0; i <= preludeEnd; i++) elided.add(baseLine + i);

  // `auxillary { … }` brace-balanced spans.
  const AUX_KW = /^\s*(?:·\s+)?auxillary\b/;
  let ai = preludeEnd + 1;
  while (ai < lines.length) {
    if (!AUX_KW.test(lines[ai])) { ai++; continue; }
    let depth = 0, sawOpen = false, inStr = false, k = ai;
    while (k < lines.length) {
      elided.add(baseLine + k);
      const ln = lines[k];
      for (let p = 0; p < ln.length; p++) {
        const ch = ln[p];
        if (ch === '\\') { p++; continue; }
        if (ch === '"') { inStr = !inStr; continue; }
        if (inStr) continue;
        if (ch === '{') { depth++; sawOpen = true; }
        else if (ch === '}') { depth--; }
      }
      if (sawOpen && depth === 0) break;
      k++;
    }
    ai = k + 1;
  }

  let i = preludeEnd + 1;
  while (i < lines.length) {
    if (!MARKER_KW.test(lines[i])) { i++; continue; }
    elided.add(baseLine + i);
    let inString = false;
    let scanIdx = 0;
    let k = i;
    while (k < lines.length) {
      const ln = lines[k];
      while (scanIdx < ln.length) {
        const ch = ln[scanIdx];
        if (ch === '\\') { scanIdx += 2; continue; }
        if (ch === '"') {
          inString = !inString;
          scanIdx++;
          if (!inString) break;
          continue;
        }
        scanIdx++;
      }
      if (!inString) break;
      k++;
      if (k < lines.length) elided.add(baseLine + k);
      scanIdx = 0;
    }
    i = k + 1;
  }
  return elided;
}

// Render the 3-column proof view (quoting / source / commentary) for
// the decl. Markers and aux figures attach to source lines via
// `grid-row` placement; aux figures span across empty rows beneath
// their anchor to absorb vertical slack.
function renderProofTriColumn(d) {
  const source = d.source || '';
  if (!source) return `<div class="bn-empty">no source</div>`;
  const baseLine = d.line_start || 1;
  const lines = source.split('\n');
  const ms = (window.markersByDecl && window.markersByDecl[d.id]) || [];
  const elided = computeMarkerLines(source, baseLine);
  const lastAbs = baseLine + lines.length - 1;

  const slideForward = (line) => {
    let n = line;
    while (n <= lastAbs && elided.has(n)) n++;
    return n > lastAbs ? line : n;
  };
  const leftByLine = {};
  const rightByLine = {};
  for (const m of ms) {
    const anchor = slideForward(m.line);
    if (m._kind === 'quoting' || m._kind === 'page_break') {
      (leftByLine[anchor] ||= []).push(m);
    } else {
      (rightByLine[anchor] ||= []).push(m);
    }
  }
  for (const fig of (d.aux_figures || [])) {
    const anchor = slideForward(fig.line);
    (rightByLine[anchor] ||= []).push({
      _kind: 'aux-figure',
      line: fig.line,
      svg: fig.svg,
      description: fig.description,
    });
  }

  const kept = [];
  let prevBlank = false;
  for (let i = 0; i < lines.length; i++) {
    const abs = baseLine + i;
    if (elided.has(abs)) { prevBlank = false; continue; }
    const isBlank = lines[i].trim() === '';
    if (isBlank && prevBlank) continue;
    kept.push({ abs, line: lines[i], isBlank });
    prevBlank = isBlank;
  }
  while (kept.length && kept[0].isBlank) kept.shift();
  while (kept.length && kept[kept.length-1].isBlank) kept.pop();

  const sourceCells = kept.map(({ abs, line }, i) => {
    const codeInner = highlightLean(line) || '&nbsp;';
    const gridRow = i + 1;
    return `<div class="proof-col-source" style="grid-row:${gridRow}">`
         + `<pre class="bn-code"><span class="bn-line" data-line="${abs}">${codeInner}</span></pre>`
         + `</div>`;
  });

  const rowOfAbs = new Map(kept.map(({ abs }, i) => [abs, i + 1]));
  const lastRowPlusOne = kept.length + 1;
  function placeMarkers(byLine, colClass, spanAuxToNext) {
    const anchors = Object.keys(byLine).map(Number).sort((a, b) => a - b);
    return anchors.map((anchor, i) => {
      const startRow = rowOfAbs.get(anchor);
      if (!startRow) return '';
      const items = byLine[anchor];
      const hasAuxFigure = items.some(it => it._kind === 'aux-figure');
      let style = `grid-row:${startRow}`;
      if (spanAuxToNext && hasAuxFigure) {
        const next = anchors[i + 1];
        const endRow = (next != null && rowOfAbs.get(next)) || lastRowPlusOne;
        if (endRow > startRow + 1) {
          style = `grid-row:${startRow} / ${endRow}`;
        }
      }
      const inner = items.map(renderMarkerLeft).join('');
      return `<div class="${colClass}" style="${style}">${inner}</div>`;
    }).join('');
  }
  const leftCells  = placeMarkers(leftByLine,  'proof-col-quoting', false);
  const rightCells = placeMarkers(rightByLine, 'proof-col-commentary', true);

  return `<div class="proof-grid">${sourceCells.join('')}${leftCells}${rightCells}</div>`;
}

// Render the full editorial card. `opts.withFlags` controls whether
// the per-section flag UI is emitted (toc viewer wants it, graph
// viewer doesn't). `opts.refsHtml` and `opts.extraSections` slot in
// host-page-specific sections (the toc viewer plugs its references
// + notes blocks here; the graph viewer omits them).
function renderCard(d, opts = {}) {
  const {
    withFlags = true,
    refsHtml = '',
    extraSections = [],
  } = opts;
  const typeTexHtml = d.type_tex ? renderTypeHtmlFromTex(d.type_tex) : '';
  const cb = (window.commentaryByDecl && window.commentaryByDecl[d.id]) || null;

  const statementBody = `<div class="card-statement${typeTexHtml ? '' : ' empty'}">${typeTexHtml || '(no type signature)'}</div>`;
  const figureBody = d.figure_svg
    ? `<div class="card-figure">${d.figure_svg}</div>`
    : `<div class="card-figure placeholder">no figure</div>`;

  const titleName = (cb && cb.name) || d.atlas_title || d.label;
  const titleMetaChips = [];
  if (cb && cb.page) {
    const pe = cb.page_end ? '–' + escapeHtml(cb.page_end) : '';
    titleMetaChips.push(`<span class="cb-page">📖 p.${escapeHtml(cb.page)}${pe}</span>`);
  }
  if (cb && cb.aliases && cb.aliases.length) {
    titleMetaChips.push(`<div class="cb-aliases">aka: ${cb.aliases.map(a =>
      `<span class="cb-alias-chip">${escapeHtml(a)}</span>`).join(' ')}</div>`);
  }
  if (cb && cb.tags && cb.tags.length) {
    titleMetaChips.push(`<div class="cb-tags">${cb.tags.map(t =>
      `<span class="cb-tag-chip">#${escapeHtml(t)}</span>`).join(' ')}</div>`);
  }
  const titleBlock = `
    <section class="title-block">
      <div class="cb-name">${escapeHtml(titleName)}</div>
      ${titleMetaChips.length ? `<div class="title-meta">${titleMetaChips.join('')}</div>` : ''}
      ${d.doc ? `<div class="card-doc">${escapeHtml(d.doc)}</div>` : ''}
    </section>`;

  const prefaceBody = (cb && cb.preface)
    ? `<blockquote class="cb-preface">${escapeHtml(cb.preface)}</blockquote>`
    : '<div class="bn-empty">no preface</div>';
  const ednotesBody = (cb && cb.notes)
    ? `<div class="cb-notes">${escapeHtml(cb.notes)}</div>`
    : '<div class="bn-empty">no editorial notes</div>';

  return `
    <header class="card-head">
      <span class="card-head-kind">§ ${escapeHtml(d.atlas_kind || d.kind)}</span>
      ${d.atlas_number ? `<span class="card-head-sep">·</span><span class="card-head-number">${escapeHtml(d.atlas_number)}</span>` : ''}
      ${d.has_sorry ? '<span class="card-head-sorry">sorry</span>' : ''}
    </header>
    <div class="lhs-stack">
      ${titleBlock}
      ${flaggableSection('preface',   'preface',   prefaceBody,   withFlags)}
      ${flaggableSection('statement', 'statement', statementBody, withFlags)}
      ${flaggableSection('ednotes',   'ed. notes', ednotesBody,   withFlags)}
    </div>
    ${flaggableSection('figure', 'figure', figureBody, withFlags)}
    ${flaggableSection('proof',  'proof',  renderProofTriColumn(d), withFlags)}
    ${refsHtml}
    ${extraSections.join('')}

    <footer class="card-meta">
      <span>${escapeHtml(d.module || '')}</span>
      ${d.line_start ? `<span class="card-meta-sep">·</span><span>L${d.line_start}${d.line_end && d.line_end !== d.line_start ? `–${d.line_end}` : ''}</span>` : ''}
      <span class="card-meta-sep">·</span><span>${escapeHtml(d.file || '')}</span>
      <div class="card-fqn">${escapeHtml(d.id)}</div>
    </footer>`;
}

// ---------- Public API ----------

window.AtlasCard = {
  escapeHtml, escapeMath,
  LEAN_KEYWORDS, highlightLean,
  texToKatexHtml, renderTypeHtmlFromTex,
  renderMarkerLeft, renderSourceWithMarkers, wrapLines,
  renderCommentarySection,
  flaggableSection, computeMarkerLines, renderProofTriColumn, renderCard,
  MARKER_KW,
};

})();
