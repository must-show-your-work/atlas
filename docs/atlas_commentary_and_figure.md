---
name: atlas commentary & figure attributes (planned)
description: Planned standalone attribute-style commands for attaching long-form explanatory commentary and figures to atlas decls, displayed in the viewer alongside the theorem card.
type: project
originSessionId: b2c5b236-d177-419d-ba65-917e999e75a8
---
# `atlas commentary <ref> "<long text>"` and `atlas figure <ref> "<path>"` — planned

## Motivation
Doc comments on theorem decls work for short statements ("p.114, …") but get unwieldy when you want a long-form discussion or to associate a diagram. Currently you can only attach a single docstring. The user wants:

- **Commentary**: arbitrary explanatory text alongside a theorem ("here's why this matters", "the book's intuition is …", historical note, derivation sketch).
- **Figure**: a path to an image asset (Greenberg's figures, hand-drawn diagrams, generated SVGs) that the viewer displays.

## Shape

```lean
atlas proposition 3.4 "Line separation through a vertex" : … := …

atlas commentary 3.4 "Pasch's Postulate is one of the more subtle betweenness
results. The proof here follows Greenberg's, with an extra case split that the
informal version glosses over. See §3.4 for context."

atlas figure 3.4 "Geometry/figures/3-4-line-separation.svg"
```

The `<ref>` (here `3.4`) refers to the atlas number of the target decl. Multiple commentaries / figures per number are allowed. They don't generate Lean decls — they just push entries into separate env extensions for later consumption by the viewer.

## Storage

Two additional `PersistentEnvExtension`s in `Atlas.lean`:
- `atlasCommentaryExt : Array (numRef : String, text : String)` — every commentary entry, keyed by number ref it attaches to.
- `atlasFigureExt : Array (numRef : String, path : String, caption? : Option String)` — figures with optional captions.

Both can have multiple entries per number ref.

## Viewer integration

Inspector pane gains two new sections:
- **Commentary**: rendered as a `<p>` block with the text. Could support Markdown via marked.js if it's already loaded.
- **Figures**: rendered as `<img src="path/to/asset.svg">` with optional caption underneath.

Both are folded out below the existing type-signature and source-code panes.

## Dump path
`DumpDecls.lean` already walks the env; emit `atlas_commentary` and `atlas_figure` arrays per decl. Alternative: separate JSON files (`blueprint/commentary.json`, `blueprint/figures.json`) loaded by the viewer at boot.

## Open design questions
- **Markdown support in commentary?** Probably yes — long text reads much better with paragraphs, lists, links. Adds a dependency (marked.js or similar) to the viewer.
- **Asset path resolution.** Relative to project root? Relative to the `.lean` file? Pick one and document.
- **Multiple-attachment semantics.** Multiple commentaries on the same number → render as multiple sections or merge? Probably multiple sections with author / source labels.
- **Figure metadata.** Beyond just a path, maybe an optional caption argument and an `alt-text` argument for accessibility.

## Order
After the bulk theorem migration + the planned `atlas_latex` and `atlas page-reference` features. This is a viewer-side enrichment that builds on the established `@[atlas]` infrastructure.

## Cost estimate
~50 LOC in `Atlas.lean` (two new extensions + two new commands), ~10 LOC in `DumpDecls.lean`, ~80 LOC in `graph.html` for the new inspector sections, plus per-commentary/per-figure annotations as you write them.
