---
name: atlas_latex attribute (planned)
description: Planned refactor — move LaTeX rendering rules for geometry constructs out of scripts/graph.html regex heuristics and into per-decl `@[atlas_latex "template"]` attributes on the def sites.
type: project
originSessionId: b2c5b236-d177-419d-ba65-917e999e75a8
---
# `@[atlas_latex "template"]` — planned refactor

## Motivation
`scripts/graph.html` currently hard-codes LaTeX rewrites for `LineThrough` / `Ray` / `Segment` / `Between` / `IntersectsSome` / `SameSide` / etc. in a brittle regex layer ("step 5a" in `leanToLatex`). Anyone adding a new geometry construct has to remember to also edit `graph.html`. Move the rendering rule *to* the def.

## Shape

```lean
@[atlas_latex "\\overline{$1$2}"]           def Segment      (A B : Point) := …
@[atlas_latex "\\overrightarrow{$1$2}"]      def Ray          (A B : Point) := …
@[atlas_latex "\\overleftrightarrow{$1$2}"]  def LineThrough  (A B : Point) := …
@[atlas_latex "$1 - $2 - $3"]                def Between      (A B C : Point) := …
@[atlas_latex "$1 \\text{ guards } $2, $3"]  def SameSide     (L : Line) (A B : Point) := …
```

Positional `$1`, `$2`, … bind to applied arguments (1-indexed).

## Implementation outline
1. **`Atlas.lean`**: register `atlasLatexExt : PersistentEnvExtension (Name × String) …`. Attribute syntax `syntax (name := atlasLatex) "atlas_latex" str : attr`. Hook stores `(decl, template)` pairs.
2. **Query helper**: `Atlas.atlasLatexTemplate? : Environment → Name → Option String`.
3. **`scripts/DumpDecls.lean`**: when dumping each decl, also emit `atlas_latex` field when present. Optional: also dump a top-level `blueprint/latex_templates.json` mapping name → template for fast viewer lookup.
4. **`scripts/graph.html`'s `leanToLatex`**:
   - Drop the hardcoded geometry-name rewrites (currently lines ~1580–1620, the `geom` array).
   - Add a substitution step: walk `\mathrm{Name} <tok> <tok> …` patterns; if `Name` has a template in the loaded map, do positional substitution; otherwise leave as `\mathrm{Name}`.
   - Keep the Unicode-op subs, the Finset-literal collapse, and the prefix→infix prop-combinator rewrites (those are Mathlib-side, not ours to tag).

## Trade-offs and limitations
- **Pro**: extensible without viewer edits; rendering rule lives next to the def; new constructs auto-work.
- **Con**: doesn't help with Mathlib-side names (`Set.instMembership.mem`, `Finset.instInsert.insert`) — those still need the regex layer.
- **Open question**: how to handle templates that need to apply *inside* a parenthesised expression (the current `\overline{(AB)}` → `\overline{AB}` paren-stripping). Probably keep the cleanup pass even after this refactor.

## Order
Wait until the bulk theorem migration is finished. Knowing which constructs show up *most often after migration* tells us which to tag first.

## Cost estimate
~30 LOC in `Atlas.lean` + ~5 LOC in `DumpDecls.lean` + ~40 LOC in `graph.html` (mostly deletion) + per-construct annotations as you go.
