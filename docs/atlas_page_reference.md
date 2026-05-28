---
name: atlas page-reference field (planned)
description: Planned optional field on `@[atlas]` for source-book page references — `atlas proposition 2.5 p71 "Title" : T := proof` — which can eventually replace doc-comment-only page citations.
type: project
originSessionId: b2c5b236-d177-419d-ba65-917e999e75a8
---
# `atlas <kind> <number> <page>? "<title>" …` — planned optional page-reference field

## Motivation
Most doc comments in `Geometry/Ch{N}/Prop/*.lean` are currently just `/-- p71, "<book statement>" -/` or `/-- pp. 71 ... -/` — the page reference is informal text inside the docstring. A structured optional field would:

- Let the atlas viewer surface the page reference as a badge ("📖 p. 71") on the card
- Normalize formats (currently mixed: "p71", "pp. 71", "p. 71", "p.114")
- Remove the need for purely-citational doc comments

## Shape

```lean
atlas proposition 2.5 p71 "Every point has at least two distinct lines through it"
  : ∀ P : Point, … := …

atlas proposition 3.4 p113 "Line-separation through a vertex"
  : ∀ {A B C P : Point}, … := …

atlas alternate 2.1 p72 "Direct proof of unique intersection"
  : … := …
```

`p<num>` parses as an identifier in Lean — the macro takes it as `p<num>` ident, strips the leading `p`, stores the number in the atlas entry as a separate `page : Option String` field.

## Position in the syntax
Optional between the number and the title. Distinguishable by the `p` prefix or by parsing — straightforward.

```
atlas <kind> <num> [p<page>] "<title>" [<binders>] : <type> := <body>
```

## Storage
Extend `AtlasEntry` with `page : Option String`. Attribute hook accepts a 4th positional arg or named `page :=`. Dump path emits `atlas_page` JSON field.

## Viewer integration
Render as a small chip near the kind+number — e.g., `§ PROPOSITION · 2.5 · p. 71`.

## Order
- Do this AFTER the bulk theorem migration so we know the actual page-reference patterns used.
- One pass after migration to lift all "p71"-style citations from doc comments into structured fields, then strip the citations from the docs.

## Cost estimate
~10 LOC in `Atlas.lean` (extending struct, parsing, hook), ~3 LOC in `DumpDecls.lean`, ~5 LOC in viewer for the chip.
