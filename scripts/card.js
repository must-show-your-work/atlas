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

// Balanced parenthesised expression up to 4 levels, a bracket-balanced
// list literal, or a token that runs to whitespace. The bare-token
// alternative includes Lean idents plus the unicode operators earlier
// rewrites emit (∅, ∪, ∩, ⊊, ⊆, ≠) so that chains like `Eq (L ∩ M) ∅`
// see `∅` as a single token. The bracket alternative lets `List.cons C [\,]`
// match by treating the nil placeholder as a single arg.
const ARG_PAT = (() => {
  const grow = (inner) => String.raw`\([^()]*(?:${inner}[^()]*)*\)`;
  let p = String.raw`\([^()]*\)`;
  p = grow(p); p = grow(p); p = grow(p); p = grow(p);
  return String.raw`(?:${p}|\[[^\[\]]*\]|[\w.∅∪∩⊊⊆≠⊥⊤]+)`;
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
    // The leading `(?:[\w.]+\.)?` consumes the type-prefix (e.g.
    // `Set.`) so it doesn't survive past the collapse.
    [new RegExp(`(?:[\\w.]+\\.)?inst\\w*[Mm]embership\\w*\\.mem (${ARG_PAT}) (${ARG_PAT})`, 'g'), '$2 ∈ $1'],
    // Subset variants — `Set.instHasSubset`, `instHasSubsetLine`, …
    [new RegExp(`(?:[\\w.]+\\.)?inst\\w*HasSubset\\w*\\.Subset (${ARG_PAT}) (${ARG_PAT})`, 'g'), '$1 ⊆ $2'],
    // Strict subset (⊊)
    [new RegExp(`(?:[\\w.]+\\.)?inst\\w*HasSSubset\\w*\\.SSubset (${ARG_PAT}) (${ARG_PAT})`, 'g'), '$1 ⊊ $2'],
    // Set ∪ / ∩ / ∅ — handle both the dotted-prefix and bare forms so
    // `Set.instInter.inter A B`, `instInterLine.inter A B`, etc. all
    // collapse to the operator notation.
    [new RegExp(`(?:[\\w.]+\\.)?inst\\w*Union\\w*\\.union (${ARG_PAT}) (${ARG_PAT})`, 'g'), '$1 ∪ $2'],
    [new RegExp(`(?:[\\w.]+\\.)?inst\\w*Inter\\w*\\.inter (${ARG_PAT}) (${ARG_PAT})`, 'g'), '$1 ∩ $2'],
    [/(?:[\w.]+\.)?inst\w*EmptyCollection\w*\.emptyCollection/g, '∅'],
    // Splits / Guards: Greenberg's geometry uses these as ternary
    // relations. `Splits L A B` reads "L splits A and B"; `Guards`
    // takes the line in the THIRD slot (point, point, line). Both
    // typeset like the SameSide-derived rules; sentinel codepoints
    // (private-use) survive tokenize and get expanded in the geom
    // block.
    [new RegExp(`\\bSplits (${ARG_PAT}) (${ARG_PAT}) (${ARG_PAT})`, 'g'), '$1  $2, $3'],
    [new RegExp(`\\bGuards (${ARG_PAT}) (${ARG_PAT}) (${ARG_PAT})`, 'g'), '$3  $1, $2'],
    // List cons — `List.cons A xs` is `A :: xs`. Recursive rule chain
    // lets `List.cons A (List.cons B (List.cons C rest))` reduce to
    // `A :: B :: C :: rest`. Will compose into a list literal in a
    // future pass if needed.
    [new RegExp(`(?:[\\w.]+\\.)?List\\.cons (${ARG_PAT}) (${ARG_PAT})`, 'g'), '$1 :: $2'],
    // Strip List.nil down to []
    [/(?:[\w.]+\.)?List\.nil\b/g, '[\\,]'],
    // `instSingletonPointLine.singleton X` → `{X}`.
    // Excludes `Finset.instSingleton.singleton X` via negative lookbehind:
    // the Finset literal goes through the `⦃ … ⦄` placeholder chain
    // below so multi-element forms (`insert A ⦃B, C⦄`) compose.
    [new RegExp(`(?<!Finset\\.)\\binst\\w*Singleton\\w*\\.singleton (${ARG_PAT})`, 'g'), '\\{$1\\}'],
    // Universe-variable noise. Lean prints `u_1` etc. for synthesised
    // universe params; in our domain we're always in `Type 0` so it's
    // never informative. Hide.
    [/\bu_\d+\b/g, ''],
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
    // `.carrier` accessor on a bare/parenthesised expr (not inside a
    // `{toSet := ...}` wrapper — that's handled by the rules above).
    // Must come AFTER toSet so the wrapper's `.carrier` anchor is
    // still present for that rule to recognise.
    [/(\)|\b[\w]+)\.carrier\b/g, '$1'],
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
    // Convert the on/off/splits/guards sentinels emitted by the
    // pre-tokenize relation rules into proper `\text{ … }` macros.
    // Has to be in the geom block (post-tokenize) so `text` itself
    // doesn't get re-wrapped in `\mathrm{}`.
    [//g, '\\text{ on }'],
    [//g, '\\text{ off }'],
    [//g, '\\text{ splits } '],
    [//g, '\\text{ guards } '],
    [/\\mathrm\{Distinct\}/g,   '\\text{distinct}\\,'],
    [/\\mathrm\{Collinear\}/g,  '\\text{collinear}\\,'],
    [/\\mathrm\{Concurrent\}/g, '\\text{concurrent}\\,'],
    [/\\mathrm\{Extension\}/g,  '\\text{ext}\\,'],
  ];
  for (const [re, repl] of geom) s = s.replace(re, repl);

  // Greenberg prose treats `distinct {A,B,C}` / `collinear {A,B,C}`
  // as `distinct A B C` / `collinear A B C` — the brace set notation
  // is a Lean detail. Replace commas with thin spaces. `\neg(collinear …)`
  // folds further to `noncollinear …` since that's how the prose reads.
  const dropBraces = (args) =>
    args.split(',').map(t => t.trim()).filter(Boolean).join('\\,');
  // `¬` (unicode) still in string at this point — the LEAN_TO_TEX_OPS
  // unicode-to-`\neg` map runs at the very end of leanToLatex.
  s = s.replace(/¬\s*\(\s*\\text\{collinear\}\\,\s*\\\{([^{}]+)\\\}\s*\)/g,
                (_, a) => `\\text{noncollinear}\\,${dropBraces(a)}`);
  s = s.replace(/\\text\{distinct\}\\,\s*\\\{([^{}]+)\\\}/g,
                (_, a) => `\\text{distinct}\\,${dropBraces(a)}`);
  s = s.replace(/\\text\{collinear\}\\,\s*\\\{([^{}]+)\\\}/g,
                (_, a) => `\\text{collinear}\\,${dropBraces(a)}`);

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

// Restructure the binder section of a `\forall …, body` so the
// result reads close to what a mathematician would write:
//
//   - Type-binders (`{A : Point}`, `{B : Point}`, `{L : Line}`) drop
//     the braces and merge consecutive ones of the same type into
//     `∀ A B : Point, L : Line`.
//   - Prop-binders (`{distinctABC : distinct A B C}`, `{h : A on L}`)
//     drop the auto-generated name entirely and move into the body
//     as `→`-hypotheses. The name was Lean machinery; the assertion
//     is what the reader cares about.
//
// Walks the binder section by depth-tracked scanning (treats `\{`,
// `\(`, `\)`, `\}` as bracket changes since brace-escape ran earlier).
// If we can't find the top-level comma separating binders from body
// (or there's no `\forall` to begin with), returns input unchanged.
function restructureBinders(tex) {
  const FOR = '\\forall';
  if (!tex.startsWith(FOR)) return tex;
  let i = FOR.length;
  while (i < tex.length && /\s/.test(tex[i])) i++;
  const binderStart = i;
  let depth = 0;
  let commaIdx = -1;
  for (let j = binderStart; j < tex.length; j++) {
    const c = tex[j];
    if (c === '\\') {
      const next = tex[j+1];
      if (next === '{' || next === '(') { depth++; j++; continue; }
      if (next === '}' || next === ')') { depth--; j++; continue; }
      // Otherwise it's a macro like `\mathrm`, `\text`, etc. — skip
      // the alphabetic macro name so its letters don't get scanned.
      let k = j + 1;
      while (k < tex.length && /[A-Za-z]/.test(tex[k])) k++;
      j = k - 1;
      continue;
    }
    if (c === '{' || c === '(') depth++;
    else if (c === '}' || c === ')') depth--;
    else if (c === ',' && depth === 0) { commaIdx = j; break; }
  }
  if (commaIdx === -1) return tex;
  const binderSection = tex.substring(binderStart, commaIdx);
  const body = tex.substring(commaIdx + 1).trimStart();

  // Parse the binder section into individual `\{…\}` / `\(…\)` groups.
  const binders = [];
  let pos = 0;
  while (pos < binderSection.length) {
    while (pos < binderSection.length && /\s/.test(binderSection[pos])) pos++;
    if (pos >= binderSection.length) break;
    const open = binderSection.substr(pos, 2);
    let close;
    if (open === '\\{') close = '\\}';
    else if (open === '\\(') close = '\\)';
    else return tex;            // unexpected — bail and keep the original
    let bDepth = 1;
    let k = pos + 2;
    while (k < binderSection.length && bDepth > 0) {
      const two = binderSection.substr(k, 2);
      if (two === open)  { bDepth++; k += 2; }
      else if (two === close) { bDepth--; k += 2; }
      else k++;
    }
    binders.push(binderSection.substring(pos + 2, k - 2));
    pos = k;
  }

  // Each binder is `<vars> : <type>` — find the first ` : ` at depth 0.
  const parsed = [];
  for (const raw of binders) {
    let d = 0;
    let cut = -1;
    for (let j = 0; j < raw.length - 2; j++) {
      const c = raw[j];
      if (c === '\\') {
        const n = raw[j+1];
        if (n === '{' || n === '(') { d++; j++; continue; }
        if (n === '}' || n === ')') { d--; j++; continue; }
        let k = j + 1;
        while (k < raw.length && /[A-Za-z]/.test(raw[k])) k++;
        j = k - 1;
        continue;
      }
      if (c === '{' || c === '(') d++;
      else if (c === '}' || c === ')') d--;
      else if (d === 0 && raw.substr(j, 3) === ' : ') { cut = j; break; }
    }
    if (cut === -1) { parsed.push({ vars: raw.trim(), type: '' }); continue; }
    parsed.push({
      vars: raw.substring(0, cut).trim(),
      type: raw.substring(cut + 3).trim(),
    });
  }

  // Classify. A "type-binder" looks like `{A B : Point}` — type is a
  // single capitalised \mathrm{} identifier. Everything else is a
  // proposition (membership claim, equality, betweenness, etc.).
  const isType = (t) => /^\\mathrm\{[A-Z]\w*\}$/.test(t);

  // Walk binders, grouping consecutive type-binders sharing a type.
  const groups = [];
  for (const p of parsed) {
    if (isType(p.type)) {
      const last = groups[groups.length - 1];
      if (last && last.kind === 'type' && last.type === p.type) {
        last.vars += '\\,' + p.vars;
      } else {
        groups.push({ kind: 'type', vars: p.vars, type: p.type });
      }
    } else {
      groups.push({ kind: 'prop', prop: p.type });
    }
  }

  const typeBinders = groups.filter(g => g.kind === 'type');
  const propBinders = groups.filter(g => g.kind === 'prop');

  let out = '';
  if (typeBinders.length > 0) {
    out += '\\forall ' + typeBinders.map(g => `${g.vars} : ${g.type}`).join(', ') + ', ';
  }
  if (propBinders.length > 0) {
    out += propBinders.map(g => g.prop).join(' \\to ') + ' \\to ';
  }
  out += body;
  return out;
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

function renderTypeHtml(rawType, opts = {}) {
  if (!rawType) return '';
  let tex = leanToLatex(rawType);
  tex = restructureBinders(tex);     // drop Lean binder names + combine same-type
  tex = stripPredicateParens(tex);   // drop redundant `(P)` around atoms
  tex = breakAtTopLevelArrows(tex);  // multi-line aligned with conclusion set-off
  // Force display mode — the multi-line `aligned` only typesets right
  // in display style.
  return texToKatexHtml(tex, { ...opts, displayMode: true });
}

// AST-path render: take a finished LaTeX string from LeanTeX,
// translate its word-form connectives (`\implies`, `\mathrm{and}`,
// `\mathrm{or}`) to the math-symbol forms the existing pipeline
// breaks on (`\to`, `\wedge`, `\vee`), then run the same paren
// strip + multi-line aligned break the regex path applies. Result
// is visually parallel to `renderTypeHtml` so the two surfaces
// match while we drive LeanTeX coverage closed.
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

// ---------- Public API ----------

window.AtlasCard = {
  escapeHtml, escapeMath,
  LEAN_KEYWORDS, highlightLean,
  LEAN_TO_TEX_OPS, ARG_PAT, leanToLatex,
  texToKatexHtml, renderTypeHtml, renderTypeHtmlFromTex,
  renderMarkerLeft, renderSourceWithMarkers, wrapLines,
  renderCommentarySection,
};

})();
