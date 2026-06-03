#!/usr/bin/env node
/*
 * latex-lint.js — scan a graph.json dump's type_pp through
 * `card.js`'s leanToLatex and flag any decl whose output still
 * contains Lean idioms that should have been collapsed.
 *
 * Usage:
 *   node atlas/scripts/latex-lint.js [path/to/blueprint/graph.json]
 *
 * Defaults to `<cwd>/blueprint/graph.json` so it works from a
 * consumer-project root.
 *
 * The lint is a checklist of patterns that *almost always* indicate
 * a missed rewrite. The intent is to give "I should add a rule for
 * X" a place to land: every time you add a rule, the lint shrinks.
 *
 * Patterns that fire today:
 *   - `\mathrm{<Capitalized>}` immediately followed by a token  →
 *     uncollapsed prefix (e.g. `\mathrm{IntersectsSome} L M`).
 *   - `\mathrm{[A-Za-z]+}\.\mathrm{` — dotted access (constructor
 *     form not collapsed, e.g. `\mathrm{Foo}.\mathrm{bar}`).
 *   - `\mathrm{(?:inst|aux)[A-Z]\w*}` — instance/internal name
 *     leaking through.
 *   - `\\_` — escaped underscore in a token name (often
 *     `\mathrm{from\_}` etc.) — usually solvable with a constructor
 *     rewrite.
 *
 * Not every hit is a bug — `\mathrm{Point}` and `\mathrm{Line}` on
 * the type side are fine. Suppress those by adding to KNOWN_GOOD.
 */

'use strict';

const fs = require('fs');
const path = require('path');

// Shim window for AtlasCard registration.
global.window = global;
global.katex = { renderToString: (tex) => tex };
require(path.join(__dirname, 'card.js'));
const A = global.AtlasCard;

const KNOWN_GOOD = new Set([
  // Geometric primitives
  'Point', 'Line', 'LineSegment', 'Ray', 'Segment',
  'Circle', 'Angle', 'Triangle', 'HalfPlane',
  // Container/structural
  'Set', 'List', 'Prop', 'Type', 'Sort', 'Nat', 'Bool',
  'True', 'False', 'And', 'Or', 'Not',
  // Greenberg / giyf-specific predicates that read fine as their bare name
  'Arrangement', 'Consequences',
  // Half-plane convention binders the user uses ('left'/'right' half-planes)
  'Hl', 'Hr',
]);

const LINTS = [
  {
    name: 'instance-leak',
    re: /\\mathrm\{(inst[A-Z]\w*)\}/g,
    msg: 'instance prefix leaked through — likely needs a new `.mem` / `.Subset` / etc. constructor rewrite',
  },
  {
    name: 'dotted-access',
    re: /\\mathrm\{([A-Z]\w*)\}\.\\mathrm\{([a-z]\w*)\}/g,
    msg: 'dotted constructor not collapsed — add `<Type>.<ctor> A B …` → `<Type> A B …` (or directly to its geom rule)',
  },
  {
    name: 'escaped-underscore',
    re: /\\mathrm\{[^}]*\\_\w+\}/g,
    msg: 'identifier with `\\_` escape — usually a Lean ctor name like `from_` or `to_`; collapse before tokenize',
  },
  {
    name: 'capitalized-prefix',
    re: /\\mathrm\{([A-Z]\w+)\}\s+(?=[A-Za-z\\(])/g,
    msg: 'uncollapsed capitalized prefix followed by args — likely missing a geom-block rewrite',
    skipIf: (m) => KNOWN_GOOD.has(m[1]),
  },
];

function lintOne(d) {
  const out = A.leanToLatex(d.type_pp || '');
  const hits = [];
  for (const lint of LINTS) {
    lint.re.lastIndex = 0;
    let m;
    while ((m = lint.re.exec(out)) !== null) {
      if (lint.skipIf && lint.skipIf(m)) continue;
      hits.push({ lint: lint.name, match: m[0], msg: lint.msg });
    }
  }
  return { decl: d, output: out, hits };
}

function main() {
  const inputPath = process.argv[2] || path.join(process.cwd(), 'blueprint', 'graph.json');
  if (!fs.existsSync(inputPath)) {
    console.error(`latex-lint: ${inputPath} not found`);
    process.exit(2);
  }
  const g = JSON.parse(fs.readFileSync(inputPath, 'utf8'));
  const decls = g.nodes.map(n => n.data).filter(d => d.atlas_kind);

  const reports = decls.map(lintOne).filter(r => r.hits.length > 0);
  console.log(`Scanned ${decls.length} atlas-tagged decls. ${reports.length} have unresolved latex idioms.`);
  console.log();

  // Group by lint kind so the punch list reads as "fix this rule, kill
  // N decls at once".
  const byLint = {};
  for (const r of reports) {
    for (const h of r.hits) {
      (byLint[h.lint] ||= []).push({ decl: r.decl, match: h.match });
    }
  }
  for (const [kind, hits] of Object.entries(byLint)) {
    console.log(`# ${kind}  (${hits.length} hit${hits.length === 1 ? '' : 's'})`);
    console.log(`  ${LINTS.find(l => l.name === kind).msg}`);
    const samples = hits.slice(0, 6);
    for (const h of samples) {
      console.log(`  ${h.decl.atlas_kind} ${h.decl.atlas_number}  → ${h.match}`);
    }
    if (hits.length > samples.length) {
      console.log(`  … and ${hits.length - samples.length} more`);
    }
    console.log();
  }

  // Exit non-zero if any hit so CI can gate on this if desired.
  process.exit(reports.length > 0 ? 1 : 0);
}

main();
