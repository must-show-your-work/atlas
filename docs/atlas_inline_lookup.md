---
name: Atlas in-editor lookup for ref forms (planned)
description: Tooling so that `ref lemma 1.0.31` is readable in-editor without maintaining a snake_case alias as a third name alongside the number and the French-quoted title.
type: project
originSessionId: b2c5b236-d177-419d-ba65-917e999e75a8
---
**Goal:** make `ref lemma 1.0.31` (and `proposition 2.1`, `corollary
["B.4.iii"]`, etc.) self-explanatory in the editor — hover/goto/info
should surface the title + doc + signature — so the codebase doesn't
need a third "shortname" identifier as a memory aid.

**Motivation:** the atlas migration left every declaration with two
canonical handles: the *number* (`1.0.31`) and the *title*
(`«Pointed intersection is symmetric in its line arguments»`). The
snake_case `alias`es that used to bridge these are gone (inlined). The
risk is that readers seeing `ref lemma 1.0.31` in a proof can't tell
what it asserts without jumping somewhere. The user wants to avoid
re-introducing aliases as a workaround.

**Why:** the user's explicit preference is to avoid maintaining three
names per decl (number, title, snake_case shortname). The
ref-form-only approach keeps the source clean but pushes the
discoverability burden onto tooling.

**How to apply:** when picking up this work, the implementation paths
in rough priority order are:

1. **Verify Lean's stock LSP hover already shows it.** Hovering on
   `ref lemma 1.0.31` should resolve to the constant
   `Geometry.Theory.Intersection.«Pointed intersection is symmetric
   ...»` and show its title (the constant's name *is* the title) plus
   its docstring. Test this first — it may already be sufficient.

2. **Augment with a custom hover provider** if (1) is insufficient.
   Likely as a small VSCode extension or a Lean-side `@[hover]`-like
   attribute that, on `ref <kind> <num>` syntax, surfaces the resolved
   title in plain prose.

3. **Add `#info ref lemma N.K.J` / `#info proposition N.K`** commands
   that print kind + number + title + docstring + type in a single
   readable chunk. Cheaper than a hover provider and useful even
   without IDE support.

4. **Generate an HTML/Markdown atlas index** from the existing
   `blueprint/graph.json` pipeline — a glossary the user can grep
   when no editor is available.

**When to apply:** after the chapter-1 renumbering compaction (the
sibling TODO) lands, since pre-renumber lookups would point at
soon-to-change numbers.
