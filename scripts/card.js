/*
 * card.js — shared card rendering for the atlas viewer.
 *
 * Ported (verbatim where possible) from `graph.html`'s inline helpers
 * so the TOC viewer and graph viewer can use the same renderers. The
 * Lean → LaTeX → KaTeX pipeline, the side-by-side commentary view,
 * the source highlighter, and the per-marker rendering all live here.
 *
 * Everything is attached to `window.AtlasCard`. KaTeX must already be
 * loaded on the page (the renderTypeHtml call uses it).
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

// ---------- Lean type pretty-print → LaTeX ----------

const LEAN_TO_TEX_OPS = [
  ['↔','\\iff '],['→','\\to '],['∀','\\forall '],['∃!','\\exists! '],['∃','\\exists '],
  ['¬','\\neg '],['≠','\\neq '],['≤','\\leq '],['≥','\\geq '],['∈','\\in '],['∉','\\notin '],
  ['∪','\\cup '],['∩','\\cap '],['⊆','\\subseteq '],['⊂','\\subset '],['⊇','\\supseteq '],
  ['⊃','\\supset '],['∅','\\emptyset '],['∧','\\wedge '],['∨','\\vee '],['⟨','\\langle '],
  ['⟩','\\rangle '],['≡','\\equiv '],['≅','\\cong '],['ℕ','\\mathbb{N} '],['ℤ','\\mathbb{Z} '],
  ['ℝ','\\mathbb{R} '],['ℚ','\\mathbb{Q} '],['ℂ','\\mathbb{C} '],['↦','\\mapsto '],
  ['⊢','\\vdash '],['⊥','\\bot '],['⊤','\\top '],['∎','\\blacksquare '],
];

// Balanced parenthesised expression up to 4 levels, or a dotted ident.
const ARG_PAT = (() => {
  const grow = (inner) => String.raw`\([^()]*(?:${inner}[^()]*)*\)`;
  let p = String.raw`\([^()]*\)`;
  p = grow(p); p = grow(p); p = grow(p); p = grow(p);
  return String.raw`(?:${p}|[\w.]+)`;
})();

function leanToLatex(raw) {
  if (!raw) return '';
  let s = String(raw);

  // Strip noise prefixes / universe annotations / instance brackets.
  s = s.replace(/Geometry\.Theory\./g, '');
  s = s.replace(/Geometry\.Ch[0-9]+\.[\w.]*\./g, '');
  s = s.replace(/\.\{[^}]*\}/g, '');
  s = s.replace(/\[inst[^\]]*\]/g, '');
  s = s.replace(/\s+/g, ' ');

  // Escape literal braces BEFORE the tokenizer wraps things in
  // \mathrm{...}; otherwise KaTeX swallows them.
  s = s.replace(/\{/g, '\\{').replace(/\}/g, '\\}');

  const rewrites = [
    // Point-on-Line membership reads naturally as "P on L" / "P off L"
    // in Greenberg's prose. Specific rule must precede the generic
    // `instMembership*.mem → ∈` and the generic `Not (X) → ¬X` so
    // those don't get a shot first. Covers PointLine, PointLineThrough,
    // PointRay, PointSegment — anything whose container is a 1-D
    // geometric subset.
    //
    // Sentinels use private-use Unicode codepoints — they have no
    // letters, so the post-tokenize multi-letter wrapper leaves them
    // alone. The geom block converts them to `\text{ on } / \text{ off }`.
    [new RegExp(`\\bNot\\s*\\(\\s*instMembershipPoint\\w+\\.mem (${ARG_PAT}) (${ARG_PAT})\\s*\\)`, 'g'),
     '$2  $1'],
    [new RegExp(`\\binstMembershipPoint\\w+\\.mem (${ARG_PAT}) (${ARG_PAT})`, 'g'),
     '$2  $1'],
    // `autoParam (X) <auto-fn-name>` is Lean's `(x : T := by tac)` desugar
    // — the second arg is a synthetic decl name like `Foo._auto_3` that
    // we never want to display. The auto-fn name may include
    // french-quoted segments with spaces (when its enclosing decl is
    // french-quoted), so we lazy-match up to the `._auto_N` suffix.
    [new RegExp(`\\bautoParam\\s+(${ARG_PAT})\\s+.+?\\._auto_\\d+`, 'g'), '$1'],
    // `Set.instMembership.mem`, `instMembershipPointLine.mem`, etc. all
    // mean "first arg contains second" — Lean's `Membership α β` instance
    // has `mem : β → α → Prop` so the FQN-first form is `mem container elt`.
    [new RegExp(`\\binst\\w*[Mm]embership\\w*\\.mem (${ARG_PAT}) (${ARG_PAT})`, 'g'), '$2 ∈ $1'],
    [new RegExp(`Set\\.instMembership\\.mem (${ARG_PAT}) (${ARG_PAT})`, 'g'), '$2 ∈ $1'],
    // Same generalization for HasSubset: `instHasSubsetLine.Subset A B` → `A ⊆ B`.
    [new RegExp(`\\binst\\w*HasSubset\\w*\\.Subset (${ARG_PAT}) (${ARG_PAT})`, 'g'), '$1 ⊆ $2'],
    [new RegExp(`Set\\.instHasSubset\\.Subset (${ARG_PAT}) (${ARG_PAT})`, 'g'), '$1 ⊆ $2'],
    // `{ toSet := X.carrier }` is the Line→Set coercion (or similar
    // setoid wrapper) Lean emits when comparing a Line to a Set. The
    // underlying X is the only thing the reader cares about; strip
    // the wrapper.
    // Drop the wrapper — the inner X often becomes a parenthesised
    // expression of its own once subsequent rules (e.g. `Segment.between
    // A B` → `(Segment A B)`) fire, so adding our own parens here
    // causes a double-wrap that defeats post-tokenize ARG_PAT match.
    [/\\\{\s*toSet\s*:=\s*\(([^()]+)\)\.carrier\s*\\\}/g, '$1'],
    [/\\\{\s*toSet\s*:=\s*([^\s\\]+)\.carrier\s*\\\}/g, '$1'],
    // `Segment.between A B`, `Ray.from_ A B`, `LineThrough.through A B`
    // are the constructor forms. Reduce each to its bare-name shape so
    // the post-tokenize geom rules collapse it to `\overline{AB}`,
    // `\overrightarrow{AB}`, `\overleftrightarrow{AB}` respectively.
    // Wrap in parens so a containing `Subset (Segment.between A B)`
    // sees it as a single ARG_PAT match.
    [new RegExp(`Segment\\.between (${ARG_PAT}) (${ARG_PAT})`, 'g'), '(Segment $1 $2)'],
    [new RegExp(`Ray\\.from_ (${ARG_PAT}) (${ARG_PAT})`, 'g'), '(Ray $1 $2)'],
    [new RegExp(`LineThrough\\.through (${ARG_PAT}) (${ARG_PAT})`, 'g'), '(LineThrough $1 $2)'],
    [new RegExp(`\\bIff (${ARG_PAT}) (${ARG_PAT})`, 'g'), '$1 ↔ $2'],
    [new RegExp(`\\bOr (${ARG_PAT}) (${ARG_PAT})`,  'g'), '$1 ∨ $2'],
    [new RegExp(`\\bAnd (${ARG_PAT}) (${ARG_PAT})`, 'g'), '$1 ∧ $2'],
    [new RegExp(`\\bNe (${ARG_PAT}) (${ARG_PAT})`,  'g'), '$1 ≠ $2'],
    [new RegExp(`\\bEq (${ARG_PAT}) (${ARG_PAT})`,  'g'), '$1 = $2'],
    [new RegExp(`\\bNot (${ARG_PAT})`, 'g'), '¬$1'],
    [/\bExistsUnique fun (\w+) =>\s*/g, '∃! $1, '],
    [/\bExists fun (\w+) =>\s*/g,       '∃ $1, '],
    [/Finset\.instSingleton\.singleton (\w+)/g, '⦃$1⦄'],
    [/Finset\.instInsert\.insert (\w+) ⦃([^⦃⦄]*)⦄/g, '⦃$1, $2⦄'],
    [/\(\s*(⦃[^⦃⦄]*⦄)\s*\)/g, '$1'],
  ];
  for (let pass = 0; pass < 8; pass++) {
    let changed = false;
    for (const [re, repl] of rewrites) {
      const next = s.replace(re, repl);
      if (next !== s) { s = next; changed = true; }
    }
    if (!changed) break;
  }
  s = s.replace(/⦃/g, '\\{').replace(/⦄/g, '\\}');

  // Tokenize: multi-letter idents → \mathrm{...}, singletons → math var.
  const out = [];
  let i = 0;
  while (i < s.length) {
    const c = s[i];
    if (/[A-Za-z]/.test(c)) {
      let j = i + 1;
      while (j < s.length && /[A-Za-z0-9_']/.test(s[j])) j++;
      const id = s.slice(i, j);
      if (id.length === 1) out.push(id);
      else out.push(`\\mathrm{${escapeMath(id)}}`);
      i = j;
    } else { out.push(c); i++; }
  }
  s = out.join('');

  // Geometry-specific aliases (run after tokenization). TOK must match
  // *anything* that an earlier rule could have emitted, so chains like
  // `Intersects L \overline{AB} X` collapse all the way through. Order
  // matters: longer alternatives first.
  const TOK = String.raw`(?:\\(?:overleftrightarrow|overrightarrow|overline)\{[^{}]*\}|\\mathrm\{[^}]+\}|[A-Za-z]|\([^()]+\))`;
  const geom = [
    [new RegExp(`\\\\mathrm\\{LineThrough\\}\\s+(${TOK})\\s+(${TOK})`, 'g'),
     '\\overleftrightarrow{$1$2}'],
    [new RegExp(`\\\\mathrm\\{Ray\\}\\s+(${TOK})\\s+(${TOK})`, 'g'),
     '\\overrightarrow{$1$2}'],
    [new RegExp(`\\\\mathrm\\{Segment\\}\\s+(${TOK})\\s+(${TOK})`, 'g'),
     '\\overline{$1$2}'],
    [new RegExp(`\\\\mathrm\\{Between\\}\\s+(${TOK})\\s+(${TOK})\\s+(${TOK})`, 'g'),
     '$1 - $2 - $3'],
    [new RegExp(`\\\\mathrm\\{IntersectsSome\\}\\s+(${TOK})\\s+(${TOK})`, 'g'),
     '$1 \\text{ intersects } $2'],
    [new RegExp(`\\\\mathrm\\{Intersects\\}\\s+(${TOK})\\s+(${TOK})\\s+(${TOK})`, 'g'),
     '$1 \\text{ meets } $2 \\text{ at } $3'],
    [new RegExp(`\\\\mathrm\\{Parallel\\}\\s+(${TOK})\\s+(${TOK})`, 'g'),
     '$1 \\parallel $2'],
    [new RegExp(`¬\\(\\\\mathrm\\{SameSide\\}\\s+(${TOK})\\s+(${TOK})\\s+(${TOK})\\)`, 'g'),
     '$1 \\text{ splits } $2, $3'],
    [new RegExp(`\\\\mathrm\\{SameSide\\}\\s+(${TOK})\\s+(${TOK})\\s+(${TOK})`, 'g'),
     '$1 \\text{ guards } $2, $3'],
    // `Distinct {A,B,C,D} 4` — the trailing cardinality is redundant
    // (the set already shows its size). Drop the digit; specific rule
    // must come before the bare `Distinct → \text{distinct}\,` below.
    [new RegExp(`\\\\mathrm\\{Distinct\\}\\s+(${TOK}|\\\\\\{[^\\\\]*\\\\\\})\\s+\\d+`, 'g'),
     '\\text{distinct}\\,$1'],
    // Convert the on/off sentinels emitted by the pre-tokenize
    // Point-membership rules into proper `\text{ … }` macros. Has
    // to be in the geom block (post-tokenize) so `text` itself
    // doesn't get re-wrapped in `\mathrm{}`.
    [//g, '\\text{ on }'],
    [//g, '\\text{ off }'],
    [/\\mathrm\{Distinct\}/g,   '\\text{distinct}\\,'],
    [/\\mathrm\{Collinear\}/g,  '\\text{collinear}\\,'],
    [/\\mathrm\{Concurrent\}/g, '\\text{concurrent}\\,'],
    [/\\mathrm\{Extension\}/g,  '\\text{ext}\\,'],
  ];
  for (const [re, repl] of geom) s = s.replace(re, repl);

  // Strip redundant parens around geometry overlines. Looped because
  // the rewrite pass can produce nested wrappers like `((\overline{AB}))`
  // when a Segment.between appears inside an already-parenthesized arg.
  const stripParen = /\(\s*(\\(?:overleftrightarrow|overrightarrow|overline)\{[^{}]*\})\s*\)/g;
  for (let pass = 0; pass < 4; pass++) {
    const next = s.replace(stripParen, '$1');
    if (next === s) break;
    s = next;
  }

  // Thin space between juxtaposed single letters.
  s = s.replace(/(\b[A-Za-z])\s+(?=[A-Za-z]\b)/g, '$1\\,');

  for (const [u, t] of LEAN_TO_TEX_OPS) s = s.split(u).join(t);
  return s.trim();
}

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

function renderTypeHtml(rawType, opts = {}) {
  if (!rawType) return '';
  return texToKatexHtml(leanToLatex(rawType), opts);
}

// ---------- Markers + side-by-side source ----------

function renderMarkerLeft(m) {
  if (m._kind === 'quoting') {
    const isExplicit = m.step != null;
    const stepChip = isExplicit
      ? `<span class="bn-step">(${m.step})</span>`
      : `<span class="bn-step bn-step-cont">…</span>`;
    const pageChip = (isExplicit && m.resolvedPage != null)
      ? `<span class="bn-page">p.${m.resolvedPage}</span>` : '';
    const trail = m.trailing ? '<span class="bn-ellipsis">…</span>' : '';
    return `<div class="bn-marker bn-marker-quoting">
      ${stepChip}${pageChip}<span class="bn-text">${escapeHtml(m.text)}${trail}</span>
    </div>`;
  }
  if (m._kind === 'comment') {
    return `<div class="bn-marker bn-marker-comment">
      <span class="bn-chip">Ed.</span><span class="bn-text">${escapeHtml(m.text)}</span>
    </div>`;
  }
  if (m._kind === 'page_break') {
    return `<div class="bn-marker bn-marker-pagebreak">
      <span class="bn-rule"></span><span class="bn-pagebreak-label">page break</span><span class="bn-rule"></span>
    </div>`;
  }
  const extendedKinds = new Set([
    'idea','intuition','motivation','caution','aside','cf','todo','fixme','detail'
  ]);
  if (extendedKinds.has(m._kind)) {
    return `<div class="bn-marker bn-marker-${m._kind}">
      <span class="bn-chip bn-chip-${m._kind}">${m._kind}</span><span class="bn-text">${escapeHtml(m.text)}</span>
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

// ---------- Public API ----------

window.AtlasCard = {
  escapeHtml, escapeMath,
  LEAN_KEYWORDS, highlightLean,
  LEAN_TO_TEX_OPS, ARG_PAT, leanToLatex,
  texToKatexHtml, renderTypeHtml,
  renderMarkerLeft, renderSourceWithMarkers, wrapLines,
  renderCommentarySection,
};

})();
