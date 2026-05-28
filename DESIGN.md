# Design Notes

Consolidated design memos for the GIYF project (Greenberg formalization)
and the Atlas extension system that will eventually migrate to its own
repo. Recovered from auto-memory after a crash; preserved here so future
sessions have ground truth.

Status conventions:
- **done** — implemented and merged on this branch
- **in-flight** — partially implemented; current work in progress
- **planned** — designed, not started
- **superseded** — replaced by a later design

---

## Table of contents

- [Atlas: commentary block + inline `quoting`/`comment` markers](#atlas-commentary-block--inline-quoting--comment-markers) — in-flight
- [Inline-annotation vocabulary (`idea`, `intuition`, `cf`, …)](#inline-annotation-vocabulary) — planned
- [Atlas positioning vs Blueprint](#atlas-positioning-vs-blueprint) — framing
- [Theorem complexes + applicators](#theorem-complexes--applicators) — planned
- [Figures & generated constructions (GeoGebra)](#figures--generated-constructions) — planned
- [Viewer node sizing — PageRank-based importance](#viewer-node-sizing--pagerank-based-importance) — planned
- [External tagging — noninvasive atlas overlays](#external-tagging--noninvasive-atlas-overlays) — planned
- [Shipping a CLI with a Lean library](#shipping-a-cli-with-a-lean-library) — open question
- [Atlas third-name / multi-form references](#atlas-third-name--multi-form-references) — planned (partially absorbed by `aliases`)
- [Atlas page-reference field](#atlas-page-reference-field) — superseded by commentary block's `page`
- [Atlas commentary + figure attributes (original)](#atlas-commentary--figure-attributes-original) — superseded
- [Atlas kind tiers — vocabulary + visual cues](#atlas-kind-tiers--vocabulary--visual-cues) — vocabulary done; visual planned
- [Atlas function-position dispatch (`via`)](#atlas-function-position-dispatch-via) — done
- [Atlas in-editor lookup for `ref` forms](#atlas-in-editor-lookup-for-ref-forms) — planned
- [`@[atlas_latex]` attribute](#atlas_latex-attribute) — planned
- [`obvious` as codification of Greenberg's tactical repertoire](#obvious-as-codification-of-greenbergs-tactical-repertoire) — in-flight
- [Card "cites" tile](#card-cites-tile) — planned
- [Card visual polish — deferred](#card-visual-polish--deferred) — deferred
- [Live Kuzu queries in viewer](#live-kuzu-queries-in-viewer) — planned
- [Chapter-1 renumber compaction](#chapter-1-renumber-compaction) — planned
- [Atlas standalone extraction — Mathlib dep](#atlas-standalone-extraction--mathlib-dep) — planned (gated on Atlas extraction)

---

## Atlas commentary block + inline `quoting` / `comment` markers

**Status:** in-flight. Phase 1 (markers) and Phase 2 (commentary block) are
implemented in `Atlas.lean`. Mechanical conversion of existing doc-comment
metadata is in progress (Phase 3); `Geometry/Ch3/Prop/P4.lean` is the only
converted file at time of writing.

Supersedes the earlier figure-and-commentary attribute plan; partially
absorbs the third-name and page-reference designs (aliases / page live on
the commentary block).

The pseudocode sketch in the bottom comment of `Geometry/Ch3/Prop/P4.lean`
(lines ~100–201 at time of writing) is the spec — don't delete.

### Three mechanisms, distinct purposes

#### A. `atlas commentary := by` — top-level metadata block

Tactic-block-style metadata, separate from the atlas decl itself:

```lean
atlas commentary := by
  ref proposition 3.4
  page 131                       -- or `pages 109..113` for multi-page
  name "Line separation property"
  aliases [Line.separation, P3.4_via_betweenness]
  preface """
  If C - A - B and l is the line through A, B, and C, then for every
  point P lying on l, P lies either on ray A B or on the opposite ray
  A C.
  """
  notes """
  Editorial commentary about why this matters / which book section it's
  from / etc.
  """
  tags ["separation", "B-3", "ray"]
```

- `ref <kind> <num>` identifies the target decl. Required. Resolved at
  dump time, not elab time, so commentary blocks can precede their target.
- `aliases [...]` — solves the third-name problem. Each name should
  ideally become a valid `ref` target. **v1 status:** aliases are *recorded
  in the env extension but NOT emitted as Lean-level decls* — generating
  `abbrev`/`def`/`notation` fought either the target's implicit arguments
  or Lean's antiquotation system. Viewer can display them as chips; for
  proof-side usage, write `abbrev Line.separation := @«Line separation…»`
  manually. See `Atlas.lean:1040-1049`.
- `name "..."` — long-form title. **Eventually replaces** the French-quoted
  title on the atlas decl, which becomes optional/omitted. Migration is
  mechanical. (Currently both coexist; phase out the on-decl title later.)
- `preface` / `notes` use triple-quoted strings for multi-line.
- `tags` — freeform string array. Useful for cross-cutting viewer filters.

**Casing convention for `aliases`:** leaf identifier is lowercase
(`Line.separation`, not `Line.Separation`); namespaces stay PascalCase.
See `feedback_atlas_alias_casing.md`.

#### B. `quoting` — inline Greenberg verbatim markers

Lives inside the proof body. Records Greenberg's narrative
position-by-position, anchored to source location for side-by-side
rendering of book-text and code.

```lean
quoting (1) "Either P lies on ray A B or it does not (Law of the Excluded Middle)"
rcases Classical.em (P on ray A B) with PonRayAB | PoffRayAB
· quoting (2) "If P does lie on ray A B, we are done" ...
  left; trivial
· quoting ... "so assume it doesn't; then P - A - B (Betweenness Axiom 3)"
  ...
```

Step indicator is **required**, two forms:
- `quoting (N) "..."` — explicit step number `N`. Starts a new step.
- `quoting ... "..."` — `...` literal = continuation. Inherits step
  number AND page from the prior marker.

Bare `quoting "..."` (no `(N)`, no leading `...`) is **not allowed**.
The `...` is a positive flag for "don't update anything" — without it,
the parser can't distinguish "I meant continuation but forgot `...`"
from "I meant step N+1 but forgot the number."

Trailing `...` after the string is **decorative** — indicates the book
text continues beyond this excerpt (ellipsis in the quote). Renders as
`…` in the viewer.

#### B'. `page break` — inline page-boundary marker

```lean
quoting (4) "..."
some_proof_step
page break
quoting (5) "..."
```

No-op at elab time; records source position only. The viewer maintains
a page counter from the commentary block's `page` (or first of `pages
109..113`) and increments on each `page break` in source order. Much
simpler than per-`quoting` page overrides.

Storage: separate `atlasPageBreakExt`.

#### C. `comment` — inline editorial markers

Source-position-anchored author voice (not Greenberg's):

```lean
comment "Some mise en place"
clearly A ≠ P; clearly B ≠ P; clearly C ≠ P
comment "Expose the pairwise inequalities for the `forgetting` casts below."
separate at distinctABCP
```

Distinct from `notes` in the commentary block: `notes` is decl-level
editorial prose; `comment` is anchored to a specific proof region.

### Storage

Four persistent env extensions in `Atlas.lean`:
- `atlasCommentaryExt : Array CommentaryBlock` — resolved at dump time
  (1:1 pairing to target decl; ambiguous (kind, num) → error)
- `atlasQuotingExt : Array QuotingMarker` (decl, modName, line, column, step?, text, trailing)
- `atlasCommentExt : Array CommentMarker`
- `atlasPageBreakExt : Array PageBreakMarker`

All use `asyncMode := .sync` so `modifyEnv` calls from inside tactic
elaboration survive past the tactic boundary.

### Viewer integration

- **Commentary block**: card-header section above the type signature —
  name, page, tags as chips, preface in citation block, notes folded out.
- **`quoting` markers**: source pane shifts to two-column layout when any
  `quoting` calls exist. Left: book quote (italic, indented citation
  style). Right: code between this marker and the next. Step rendered as
  `(N)` in the left margin; `...` markers as `…` continuation.
- **`comment` markers**: left-margin annotations on the code (not separate
  column), styled with Ed.-label.
- **`aliases`**: alternate-citation chips on the card.

### Implementation phases

1. **Phase 1** — `quoting` and `comment` macros. ~50 LOC Atlas + ~15 LOC
   DumpDecls + ~120 LOC viewer. **Done.**
2. **Phase 2** — `atlas commentary := by` block, alias registration, viewer
   card-header. ~120 LOC Atlas + ~20 LOC DumpDecls + ~80 LOC viewer. **Done**
   except alias decl emission (see v1 note above) and the title-on-decl
   optionalization sub-decision below.
3. **Phase 3** — migrate existing doc-comment metadata. Walk every atlas
   decl, lift `p<NNN>` into commentary blocks, lift inline `/- (N) "..." -/`
   into `quoting` calls. **In progress (mechanical conversion, one file at a time).**

### Title-on-decl optionalization (Phase 2 sub-decision)

Three possible end states:
- **(A)** Keep both: `atlas proposition 3.4 "Title"` plus optional
  commentary `name "..."` that overrides. Lowest-friction migration.
- **(B)** Thin atlas entry: title strips from the decl entirely; only
  commentary's `name` names it. Cleaner conceptually — user's preference.
- **(C)** Big-hack: everything inside one `atlas commentary := by` block
  (signature + proof + metadata), with `proof do ...` for the body. Single
  source of truth but invasive.

**Decision:** start with (A) for Phase 1/2; revisit (B) after commentary
block lands and is in use across the corpus. (C) is on the table only if
(B) feels insufficient.

### Resolved design questions — don't re-litigate

- `...` semantics — leading = continuation flag, trailing = decorative
  ellipsis. One of `(N)` or leading `...` is required.
- Multi-page proofs — inline `page break` marker; viewer counts breaks.
  No per-`quoting` page override.
- `comment` vs `notes` — `comment` is region-anchored; `notes` is decl-level.
- Naming — `quoting` (not `quote`, collides with Lean's `quote`),
  `comment` (not `note`, collides with Mathlib's `note` attr).
- Block style — `atlas commentary := by ...` re-uses Lean's tactic parser
  visual idiom for a list of statements. No actual proof obligation;
  custom command elab walks the field-tactics.

### Out of scope (for now)

- Bibliography mechanism (`atlas quote-source "Greenberg, p.109"`). Book
  is implicit project-wide.
- Markdown/treesitter highlighting in `preface`/`notes`/`quoting` text.
- Editor (nvim/VS Code) hover integration — web viewer only.

---

## Inline-annotation vocabulary

**Status:** planned. Extends the marker family.

Current marker set: `quoting`, `comment`, `page break`. User-requested
additions:

Two families:

**Reader-cue annotations** (pedagogical / book-companion):

| Kind | Purpose | Tone |
|---|---|---|
| `idea` | the key insight / "trick" | luminous; foregrounded |
| `intuition` | mental picture to hold | softer / parenthetical |
| `motivation` | why this proof matters | scene-setting |
| `caution` | thing readers commonly miss | warning |
| `aside` | tangent / context | parenthetical |
| `cf` | informal cross-reference (not a real `ref`) | hyperlinky |
| `see also` | same as `cf`, prose form | hyperlinky |

**Code-state annotations** (formalization-side, not book commentary):

| Kind | Purpose | Tone |
|---|---|---|
| `todo` | work the author plans to do | task-tracker style |
| `fixme` | known broken / placeholder | task-tracker, warning hue |
| `detail` | implementation-detail question (replaces `-- NOTE`) | quiet; scratch-pad |

`detail` is distinct from `comment`: existing `-- NOTE` line comments are
typically impl-detail questions ("do I need to dispatch both at once?",
"have to be specific here to avoid coercion issues") — different audience
from authorial editorial commentary about the book. `todo` / `fixme` are
likewise tracked code state, not book content — viewer can surface a
cross-cutting "pending" view by aggregating them per decl/chapter.

### Tag prefixes on code-state markers (planned)

The code-state kinds (`todo`, `fixme`, `detail`) should support an optional
category tag in brackets, mirroring the existing convention in line
comments (`-- TODO[refactor]: ...`):

```lean
todo[refactor] "nested ref-in-ref pattern; lift inner symm out"
fixme[blocked] "needs B-3 case split before this works"
detail[coercion] "have to be specific here to avoid coercion issues"
todo[refactor, perf] "two tags, comma-separated"
```

Marker records gain a `tags : Array String` field (empty by default).
The viewer can then filter / group / colour by tag, and the planned
"pending" aggregate view can break down by category.

Tag prefixes are **code-state only** — reader-cue markers (`idea`,
`intuition`, etc.) wouldn't get them since they don't have category
structure to track. Conceptually tags are mini-`tags` (the commentary
block already has a per-decl `tags [...]` field; this is the per-marker
analogue at the code-state level).

`cf` and `see also` are aliases of the same kind — record under the same
bucket so the viewer doesn't need to know which form was written. The
multi-token form parses like `page break`: `syntax "see" "also" str : tactic`.

`figure "<path>"` is already on the roadmap for diagram assets (see
superseded note below); belongs in this family conceptually.

### Implementation shape

Mechanically identical to the existing markers:
- `syntax "idea" str : tactic` (per kind)
- No-op tactic that records to a `SimplePersistentEnvExtension` with
  `asyncMode := .sync`
- `DumpDecls` emits per-kind array in `markers.json`
- Viewer renders each kind with distinct visual treatment

Conventions to lock in once ~3 kinds exist:
- All marker tactics registered with `#allow_unused_tactic!`
- Shared field schema: `decl`, `modName`, `line`, `column`, `text`. Maybe
  a single `InlineMarker` struct with a `kind : Name` field — DRY but
  loses Lean-side type separation. Decide once we have ~3 kinds.
- Single `markers.json` keyed by kind: `{ idea: [...], intuition: [...], ... }`.

### Visual treatment

- `idea`: bright (yellow card-stock? sun-glyph chip?), distinct border
- `intuition`: muted, italic
- `motivation`: small caps preface label
- `caution`: red border-left (like `comment`'s Ed.-style)
- `aside`: parenthetical brackets, smaller
- `cf` / `see also`: identical rendering — "cf." or "see also" label
  preceding the referenced text, link-style if the target is an atlas
  decl (clickable warp to its card), prose otherwise

Don't introduce these unless the reader-cue is genuinely distinct. Start
with `idea` + 1–2 others; expand as use cases appear in the text.

### Sequencing

Land after current Phase 2 wraps. Mechanism is well-trodden by now; each
new kind is ~30 LOC Lean + ~30 LOC viewer.

---

## Atlas positioning vs Blueprint

**Status:** framing note.

Lean's existing `leanblueprint` tool is the obvious comparison. The
distinction matters because confusing the two leads to mis-set
expectations.

- **Blueprint is a roadmap.** Author writes the intended structure of
  a project up-front; the tool tracks formalization progress against
  that human-authored plan. Goals are declared; the tool reports which
  ones are met.
- **Atlas is a survey.** It walks what's *actually elaborated* in the
  Lean source and renders the de-facto theorem structure. Edges in the
  graph are *actual `ref` / `via` uses*, not expected dependencies. A
  theorem cited by another theorem shows up because the citation is in
  the code, not because someone planned it.

The two are complementary, not in competition — but knowing which kind
of tool Atlas is matters for how it's used. Atlas isn't a place to
declare "I will formalize Wiles' 1995 paper"; it's a place where Wiles
shows up *after* you've actually cited him. The roadmap-vs-survey split
is the cleanest one-liner for someone who has Blueprint in their head.

---

## Theorem complexes + applicators

**Status:** planned.

The author frequently presents a *cluster* of related statements under a
single book number — a primary proposition, its alternate proof(s), one or
more corollaries, alternates of those corollaries, etc. Greenberg's P3.1
and P3.3 are canonical examples. Today each member of a cluster gets its
own atlas decl (with disambiguator like `3.1.i` / `3.1.ii` once the
sub-letter parser lands), but there's no first-class concept binding them
together.

### What we want

Cite the *whole cluster* in one go:

```lean
-- somewhere in a proof:
ref proposition 3.1    -- tries all members of complex P3.1, dispatching by type
-- or as a named complex:
ref complex P3.1 args  -- explicit complex-ref form
```

Mechanism analogy: a named static `simp` set, but for atlas decls — a
small, ergonomic batch of related facts, used liberally rather than
forcing the caller to know exactly which sub-part fits.

### Shape (sketch)

A new commentary tactic / attribute marking a decl as a member of a
named complex:

```lean
atlas commentary := by
  ref proposition 3.1.i
  complex P3.1                -- this decl is a member of the P3.1 complex
  ...

atlas commentary := by
  ref proposition 3.1.ii
  complex P3.1
  ...

atlas commentary := by
  ref corollary 3.1.a
  complex P3.1
  ...
```

Lookup:
- `ref complex P3.1 args` — try each member's dispatch with `args` (like
  `via` does today for paired decls) and pick the one whose return type
  unifies with the expected type.
- `ref proposition 3.1 args` (no sub-letter) — could also fall back to
  complex dispatch if there's a complex matching that number. Backward-
  compatible with the existing dispatch.

### Why distinct from `aliases`

- `aliases` is a per-decl renaming channel; same target.
- A complex is a per-decl *membership* channel; one citation form
  resolves to *any* of N targets via type-driven dispatch.

Same record-and-render pipeline as the other commentary fields. Viewer
could render complex membership as a chip (`[complex P3.1]`) and visually
group cluster members.

### Applicators (extension)

The README introduces a second piece of the complex story: each complex
can carry a **custom applicator** — a macro or tactic encapsulating
the canonical way to invoke the complex's members with a recurring
shape of arguments.

Motivation: when a complex's members all take similar args (e.g.
P3.3.i and P3.3.ii both take `⟨A-B-C, A-C-D⟩`), and there's a
recurring caller-site pattern (e.g. "use the i form unless the C
position is ambiguous"), the applicator captures that pattern once.
Caller writes `applicator P3.3 args*` and the right member is invoked
with the right shape.

Sketch:

```lean
atlas complex P3.3 where
  members := [proposition 3.3.i, proposition 3.3.ii]
  -- applicator name + body. Looks like a tactic/term macro tied to
  -- the complex; sees the args and decides which member fits.
  applicator chain (h : A - B - C) (k : A - C - D) :=
    via proposition 3.3.i ⟨h, k⟩
```

Then `applicator P3.3.chain ABC ACD` is the natural invocation. Multiple
applicators per complex if the complex has multiple distinct
caller-side patterns.

Distinct from `via` (which already does type-directed dispatch over a
complex's members): an applicator captures a *patterned argument
shape*, not just a dispatch decision. Closer in spirit to a Mathlib
`simp` lemma set with a custom apply tactic than to a single overload.

### Order

After the sub-letter parser extension lands (so members have distinct
numbers to point to). May obsolete some of the third-name design (below)
if complexes provide enough ergonomics on their own. Applicators are
the next layer after basic complex membership; design them once basic
`ref complex` is working.

---

## Figures & generated constructions

**Status:** planned. Two-phase: simple `figure` field now, generated
constructions later.

### Phase 1 — `figure` field on `atlas commentary` (cheap)

A list of asset paths (SVG, PNG, JPG) attached per-decl that the viewer
embeds inline on the card:

```lean
atlas commentary := by
  ref proposition 3.7
  page 114
  name "Pasch's Postulate"
  preface "..."
  figure [
    "Geometry/figures/3-7-pasch-main.svg",
    "Geometry/figures/3-7-pasch-cases.svg"
  ]
```

Diagrams are authored by hand for now (Inkscape, hand-drawn scans,
Greenberg's own figures if rights permit, etc.). Viewer renders them in
the card body, captioned. Multiple per decl allowed.

Storage / dump: extend `CommentaryBlock` with `figureList : Array String`.
Viewer fetches each path relative to the project root and embeds via
`<img>`.

### Phase 2 — `construction` field, generated diagrams

A declarative construction spec inside the commentary block that the
build pipeline renders into a GeoGebra (or similar) construction file
and a static SVG snapshot. Lets diagrams stay in sync with the formal
content — rename a point, the diagram updates.

Shape (sketch):

```lean
atlas commentary := by
  ref proposition 3.7
  ...
  construction := by
    points A B C { not_collinear }
    line L { meets segment A B at X with A-X-B }
    cases
    | "L meets AC"  => line_to L (segment A C)
    | "L meets BC"  => line_to L (segment B C)
```

The DSL specifies: which points exist, what constraints they satisfy,
which lines/segments to draw, and (optionally) named cases the figure
should illustrate side-by-side.

Tooling:
- A Lean-side or Python-side compiler that reads the construction spec
  and emits a `.ggb` (GeoGebra file) plus a rendered `.svg` snapshot.
- Viewer embeds the SVG by default; "open in GeoGebra" link for
  interactive exploration.
- **In-editor preview via ProofWidgets4**: the same widget framework
  proposed for the in-editor ref lookup
  (https://github.com/leanprover-community/ProofWidgets4) can host the
  rendered figure in the InfoView panel — see the construction live
  while writing the proof, with the diagram updating as the construction
  spec is edited. Single dependency covers both use cases.

### Trade-offs

- **Pro (phase 2):** diagrams stay in sync with the formalization;
  multi-case figures generate uniformly; authors don't have to draw.
- **Con:** writing a robust constraint-satisfying renderer is real work.
  Hand-authored figures (phase 1) cover the gap until phase 2 is worth
  the investment.

Phase 1 is small (~10 LOC Atlas, ~20 LOC viewer). Phase 2 is a separate
multi-week project — design but don't build until phase 1 reveals how
many figures we actually want.

---

## Atlas as semi-literate programming for Lean

**Status:** vision / framing. Not a feature itself; the framing that
drives prioritisation of features below.

The Lean source is one face of the artifact; Atlas's commentary blocks,
inline markers, and graph dumps are the other face. The two halves
together produce something that reads as a book and elaborates as a
proof corpus. **The source IS the book.**

### What this means

- **Commentary blocks are a structured metadata holder spanning both
  halves.** Some fields lean code-side (`ref` is a pointer, `aliases`
  are alternate Lean identifiers), some lean book-side (`page` /
  `pages` cite a source, `preface` carries book prose, `notes` is
  editorial sidebar), and some are equally either (`name`, `tags`).
  The block is one structure; what it holds varies by use.
- **Inline markers carry the narrative**. `quoting` (book voice),
  `comment` (editor), `idea` / `intuition` / etc. (pedagogical cues).
  The proof body is the formal half; the markers are the prose half.
- **Atlas should eventually auto-structure the source into a book.**
  Group decls into chapters by namespace / atlas number prefix.
  Inline commentary in book-reading order. Render proofs as
  side-by-side: prose on the left, Lean on the right. Generate a PDF
  / HTML book from the atlas state.

### What's new vs. classic literate programming

Knuth's WEB/CWEB interleaves prose and code in one source file with
explicit `@<...@>` blocks; the tangle/weave step extracts each.

Atlas is **semi**-literate because the Lean source remains primary —
proofs are written in tactic mode, not narrative-first prose — but
commentary blocks and markers attach prose to specific positions that
the dump pipeline re-assembles into a book-shaped artifact. You can
read the source as code OR as a book; the dump bridges.

### Related features

This vision ties together several individually-planned items in this
document: theorem complexes, figures & constructions, card cites tile,
tag prefixes on markers, kind-tier visual cues, live Kuzu queries,
ProofWidgets4 in-editor lookup. None individually constitute "the
book"; together they're a literate-programming-shaped workflow.

### Design heuristic

When evaluating a new Atlas feature, ask:
1. Does this serve "the source IS the book?"
2. Or is this metadata-about-code / pure tooling?

(1) gets prioritised. (2) is fine but not what Atlas is for.

---

## Atlas third-name / multi-form references

**Status:** planned, partially absorbed by `aliases` on the commentary
block. Title-string lookup still wanted; namespaced short-name as
first-class atlas concept still planned.

User wants every atlas decl reachable via *three* equivalent forms:

```lean
ref proposition 3.4                          -- by number (terse, citation-style)
ref proposition "Line Separation Property"   -- by title-string
ref property Line.separation                  -- by namespaced short-name
```

Motivation: numbered refs read like citations but lack semantics; titles
carry meaning but are wordy; short namespaced names read most naturally
inside proofs. Pick whichever reads best at each call site.

This is a re-introduction of the alias mechanism removed earlier — but as
a *first-class atlas concept*, owned by the macro, not a side-channel
`alias X := «...»` line per decl. Plus title-string lookup.

### Flat-namespace auto-generation (refinement)

User's preference: short-name follows a standard production
`Geometry.Theory.<kind>_<X>_<Y>[_<Z>]`:
- `<kind>` = atlas kind word (lowercased)
- `<X>_<Y>` = dotted parts of the number (e.g. `3_1`, `1_0_28`, `B_1b`)
- `<Z>` = optional sub-letter for paired decls (`a`/`b`/`c`/…)

So `atlas exercise 3.1 "..."` auto-generates `Geometry.Theory.exercise_3_1`
(or `_3_1_a` / `_3_1_b` if paired). The user can then write `exercise_3_1_a`
directly in proofs.

Auto-letter assignment is risky (depends on file processing order); paired
decls declare suffix explicitly via an `as a` clause:

```lean
atlas exercise 3.1 "Distinct from Chain" as a : T := body
atlas exercise 3.1 "Collinear from Chain" as b : T := body
```

`as` is optional for unpaired decls. Conflict on auto-name should be a
compile-time error pointing at the `as` clause.

### Reference syntax extensions

| Form | Looks up | Currently |
|---|---|---|
| `ref proposition 3.4` | (kind, number) | done |
| `«Line Separation Property»` | constant name directly | done |
| `ref proposition "Line Separation Property"` | (kind, title) | needs `str` form in `atlasNum` |
| `Line.separation` | constant via Lean's resolution | done once alias exists |
| `ref property Line.separation` | named index | new |

`ref property` would be a new term-position kind that does namespaced-name
lookup. The literal `property` is a synonym for "any kind" — a
human-readable category word that need not match a registered atlas kind.

### Companion: more `.symm`-style dot-notation projections

User also wants more lemmas callable "on" a fact-in-evidence via dot
notation (the way `BCD.symm` works for B-1b). Separate, lighter ergonomics
improvement — doesn't need atlas-side work:

```lean
def Between.swap (h : A - B - C) : C - B - A := (ref axiom B-1b).mp h
```

These don't go through atlas (they're "natural properties of the underlying
struct" per earlier guidance) — see `Between.symm` as the canonical example.

---

## Atlas page-reference field

**Status:** superseded by the `page` / `pages` fields on the commentary
block. Preserved for historical context.

Original design: optional positional field on the atlas decl
(`atlas proposition 2.5 p71 "Title"`). The commentary block subsumes it;
page is now a commentary field, not part of the decl signature.

If the commentary block is *not* present, the decl has no structured page
reference — the doc comment (where it still exists) is the freeform fallback.
After Phase 3 migration completes, every decl should have a commentary
block with a `page` field; doc comments become redundant for citation.

---

## Atlas commentary + figure attributes (original)

**Status:** superseded by the three-piece commentary/quoting/comment design.

Original shape was a standalone `atlas commentary <ref> "<long text>"` and
`atlas figure <ref> "<path>"` — attribute-style commands attaching text/images
to a numbered ref. Replaced by the commentary block + inline marker family
which carries the same information more structurally.

**`figure` part still relevant** if/when we add diagrams. Suggested location:
inline marker form `figure "<path>" "<caption>?"` consistent with the rest
of the marker vocabulary (anchored to source position, not just decl).

---

## Viewer node sizing — PageRank-based importance

**Status:** planned.

The README promises that the viewer "scales theorems by their importance
(via pagerank) and arranges them in layers with axioms at the bottom and
theory growing up from it." Today the layered layout part is real (ELK
layered + kind tiers pin axioms/definitions to the bottom), but node
sizing is uniform. PageRank-by-citation would make heavily-cited
theorems visually larger / more central.

### What PageRank gives us

Standard PageRank on the dependency graph: nodes that get cited by
many other nodes (and especially by nodes that are themselves cited
heavily) score higher. The exact tuning is conventional:

- Edge direction: dependency `A → B` (A cites B) is the inbound edge
  for B. PageRank propagates rank to dependencies.
- Damping factor 0.85 is the textbook choice.
- Iteration to convergence (or fixed ~50 iterations); small graphs
  converge fast.

A "main result" with many corollaries citing it ranks high. An axiom
cited by every theorem also ranks high (the foundational layer).
"Leaf" lemmas that nothing cites rank low.

### Where it plugs in

Two viewer-side hooks:

1. **Node size** — visual scale proportional to `√rank` (square root
   compresses the dynamic range so the biggest nodes don't dwarf the
   rest). The Cytoscape layout would receive per-node `width`/`height`
   from the PageRank pass.
2. **Layout weighting** — ELK's layered algorithm doesn't directly
   support node importance, but the kuzu pre-pass can output a
   bias-ordered node list that the layout uses to break ties (e.g.
   higher rank → more central position within its layer).

### Dump-side mechanism

PageRank is a graph computation, not a Lean concern. It runs against
the kuzu DB:

- Either a Cypher-based PageRank query (kuzu has algorithm extensions),
- Or a Python pass that reads the dep graph from kuzu, runs networkx's
  PageRank, and writes back per-node scores to a new property.

The score becomes a node attribute the viewer reads. New TODO:
"PageRank pass in the dump pipeline."

### When

After basic node rendering is stable. Doesn't block other work.
Tunable separately from the layered algorithm.

---

## External tagging — noninvasive atlas overlays

**Status:** planned.

The README's third use-case: an interested party tags *someone else's*
existing Lean code with atlas metadata without modifying it. The
target library stays untouched; the tagger's project imports the
target and applies atlas attributes from a separate "overlay" file.

### Why this matters

- Lets you explore a library you don't own — Mathlib, stdlib, someone
  else's research code — through Atlas's lens (the graph, the cards,
  the queries).
- Lets a teacher tag selected results from a textbook + Mathlib
  combination as the formal companion to a course, without forking
  Mathlib.
- Makes contribution lighter: instead of PR-ing atlas tags into a
  library, ship the overlay file separately.

### Mechanism (sketch)

The standard `atlas <kind> N "Title" : T := body` form generates the
decl as it tags. For external tagging, we need a tag-existing form:

```lean
import Mathlib.Topology.Basic
-- ... import the target

-- Tag-existing form: refer to a Mathlib decl by full name, attach
-- atlas metadata without creating a new decl.
atlas mathlib_proposition 1.5 "Continuous functions compose"
  := Continuous.comp
```

The macro emits `@[atlas "mathlib_proposition" "1.5" "Continuous functions compose"] noncomputable def «Continuous functions compose» := Continuous.comp` (or similar — needs to be a real decl so the attribute hangs somewhere, but its only job is to point at the target).

Caveats:
- The "overlay" decl shows up as its own node in the dep graph, with
  a single edge to the target. We probably want the viewer to *splice
  through* the overlay so the original Mathlib decl is what renders,
  not the alias. Needs a "passthrough" hint in the dump.
- Multi-target overlays (same atlas number tagging two Mathlib decls)
  fall back to paired-decl semantics — same machinery as paired
  propositions.
- Commentary blocks (`atlas commentary := by ref ...`) work
  unchanged — they target by `(kind, num)`, which the overlay sets.

### Order

After extraction, after the dumper-parameterisation work. The
overlay use-case puts pressure on `--target` to accept multiple
modules (the target lib + the overlay lib).

---

## Atlas kind tiers — vocabulary + visual cues

**Status:** vocabulary done; visual cues planned.

Atlas has a tiered kind hierarchy used by term-position elab to disambiguate
`<kind> N` references: when multiple decls share `N`, the lookup cascades
through tiers and Lean's overload-choice mechanism picks by type unification.
See `kindTiers` in `Atlas.lean`.

Current tiers:
- **T1 (main results):** theorem, proposition, postulate, lemma, axiom,
  exercise, law, principle, fact, scholium
- **T2 (derived):** corollary, consequence, claim
- **T3 (commentary):** remark, note, observation, example, discussion
- **Exact-only (no cascade):** alternate, definition

Deliberately omitted: `conjecture`, `hypothesis` (name unproven things,
don't fit "result"/"commentary" framing — add later if needed).

### Visual cue per tier (planned)

Right now cards differ visually only by *kind* (the kind chip). Two cards
both tagged `proposition` look identical to a `corollary` and a `remark` if
the user zooms past chips. The tier should be obvious at a glance — *"this
is a main result vs a derived note"* — without reading.

Suggestion: tint per tier, not per kind. One per-tier visual signal
(left-edge band? title-strip color? paper-tint shift?):
- T1 → cream/ivory (default, most numerous)
- T2 → ochre tint (warm — derived from the main)
- T3 → muted slate / lavender (cooler — commentary, lower-stakes)

Definitions and axioms are foundational (already pinned to the bottom layer
via `elk.layered.layering.layerConstraint: LAST`) and keep their existing
tint scheme.

How to apply:
- Set `data-tier` on each card from a small JS lookup (kind → tier).
- Add CSS rules `.node-card[data-tier="2"] { ... }` etc.
- Pick palette that coexists with existing kind-specific per-card tints
  (kind chip can still be coloured by kind; tier tint is a separate channel).

---

## Atlas function-position dispatch (`via`)

**Status:** done.

Bucket-3 (paired-decl) dispatch is solved via a separate `via kind N args*`
syntax that captures trailing args as part of the parse, then manually
elaborates each candidate against the full application + the caller's
`expectedType?` to pick the one whose inferred type matches via
`Lean.Meta.isDefEq`.

### Why `ref kind N args` alone couldn't do this

Lean's `elabAppFn` (`Elab/App.lean:1853`) only dispatches choice nodes
whose syntax kind is literally `choiceKind` — checked *before* any macro
expansion of `stx[0]`. When `f = ref kind N` is a custom syntax kind, the
check fails and `elabAppFn` falls through to `elabTerm f none catchPostpone`
(line 1908), passing `expectedType? = none`. Our term elab can't see the
return type at all in function-application position.

### Mechanism

`via kind N args*` parses as one syntactic unit:

```lean
syntax:max (name := atlasVia) "via" rawIdent atlasNum
    (ppSpace colGt term:max)+ : term
```

Elab (in `elabAtlasApplyTerm`):
1. Look up candidates (exact-kind only — cascade disabled here; see below).
2. Single match: emit `cand args*` and elaborate normally.
3. Multi-match: `tryPostponeIfHasMVars? expectedType?` to wait for
   surrounding metavariables (e.g., from a sibling slot in `⟨…, sibling⟩`)
   to pin. Then loop over candidates:
   - `elabTerm (cand args*) (some expected)` in a saved-state snapshot
   - `synthesizeSyntheticMVarsNoPostponing` to force-resolve
   - Reject if `e.hasExprMVar` (implicits unresolved → didn't fit)
   - Otherwise `isDefEq inferredType expected`; keep if it matches
   - Restore state and try next candidate
4. Re-elaborate the unique winner cleanly.

### Two non-obvious gotchas

- **`tryPostponeIfNoneOrMVar` is the wrong helper** — it only checks
  whether the type's *head* is a metavariable. For our case (nested
  constructor slots), the head is typically a concrete relation like
  `Between` but the *arguments* are metavariables. Need
  `tryPostponeIfHasMVars?` which scans the whole expression.
- **Cascade must be disabled for `via`**. `ref proposition 3.3` loose-matches
  through T1→T2 (so `corollary 3.3` is pulled in for `ref theorem 3.3`-style
  calls). That's wrong for `via proposition 3.3`: user is explicit about the
  kind, and pulling in adjacent kinds yields candidates that may type-check
  ambiguously when point-implicits unify across the application. `via` uses
  `atlasLookupByNumber env kind numStr` (exact) instead of
  `atlasLookupCascading`.

### Coexistence with `ref`

`ref kind N` unchanged — canonical form for unambiguous lookups. Use
`via kind N args*` only when:
- The lookup is multi-candidate (paired decls), AND
- You're via'ing it to args, AND
- The expected return type can be pinned (via `: T` annotation, `exact`
  against a known goal, or surrounding constructor args).

**Greedy-vararg gotcha:** `ref a 1 ref b 2` parses with sibling refs
correctly because `ref` has no varargs. `via a 1 ref b 2` would parse as
`via` capturing `ref b 2` as an arg — at sites where multiple atlas refs
are arguments to a single call, use `ref` form or wrap subordinate refs
in parens.

### Code locations

- Syntax: `Atlas.lean:524` — `syntax:max (name := atlasVia) "via" …`
- Elab: `Atlas.lean:566-` — `elabAtlasApplyTerm`
- Helpers: `Lean.Elab.Term.tryPostponeIfHasMVars?`,
  `synthesizeSyntheticMVarsNoPostponing`, `Lean.Meta.isDefEq`,
  `Lean.instantiateMVars`.

All 11 Bucket-3 sites (P3, P4, Ex1) converted. The third-name flat-namespace
mechanism is no longer needed for these sites; it remains relevant only if
a future use case needs a third *readable* citation form (which the
commentary mechanism may absorb instead).

---

## Atlas in-editor lookup for `ref` forms

**Status:** planned.

**Goal:** make `ref lemma 1.0.31` (and `proposition 2.1`, `corollary
["B.4.iii"]`, etc.) self-explanatory in the editor — hover/goto/info should
surface title + doc + signature — so the codebase doesn't need a third
"shortname" identifier as a memory aid.

**Motivation:** atlas migration left every decl with two canonical handles:
the *number* (`1.0.31`) and the *title* (`«Pointed intersection is symmetric
in its line arguments»`). Snake_case aliases that used to bridge these are
gone. Readers seeing `ref lemma 1.0.31` in a proof can't tell what it
asserts without jumping somewhere. User wants to avoid re-introducing
aliases as a workaround.

**Why:** user's explicit preference to avoid maintaining three names per
decl. Ref-form-only approach keeps source clean but pushes discoverability
onto tooling.

### Implementation paths (rough priority order)

1. **Verify Lean's stock LSP hover already shows it.** Hovering on
   `ref lemma 1.0.31` should resolve to the constant
   `Geometry.Theory.Intersection.«Pointed intersection is symmetric ...»`
   and show its title (the constant's name *is* the title) plus its
   docstring. Test first — may already be sufficient.
2. **ProofWidgets4 panel** showing referenced lemmas with their long
   names. `https://github.com/leanprover-community/ProofWidgets4` renders
   custom HTML in the goal/InfoView panel — perfect for a "referenced
   lemmas in this proof state" sidebar that lists each `ref`/`via`-reachable
   decl with its kind, number, title, and a one-line preface. Solves the
   discoverability gap without forcing alias names back into source code.
   Updates live as the cursor moves through the proof.
3. **Custom hover provider** if (2) feels too heavyweight. Small VSCode
   extension or Lean-side `@[hover]`-like attribute that surfaces the
   resolved title in plain prose on `ref <kind> <num>` syntax.
4. **`#info ref lemma N.K.J` command** that prints kind + number + title +
   docstring + type in one readable chunk. Cheaper than a hover provider;
   useful even without IDE.
5. **Generated HTML/Markdown atlas index** from `blueprint/graph.json`
   pipeline — glossary the user can grep when no editor is available.

**When:** after the chapter-1 renumbering compaction lands (pre-renumber
lookups would point at soon-to-change numbers).

---

## `@[atlas_latex]` attribute

**Status:** planned.

### Motivation

`scripts/graph.html` currently hard-codes LaTeX rewrites for `LineThrough`,
`Ray`, `Segment`, `Between`, `IntersectsSome`, `SameSide`, etc. in a
brittle regex layer ("step 5a" in `leanToLatex`). Anyone adding a new
geometry construct has to remember to also edit `graph.html`. Move the
rendering rule *to* the def.

### Shape

```lean
@[atlas_latex "\\overline{$1$2}"]            def Segment      (A B : Point) := …
@[atlas_latex "\\overrightarrow{$1$2}"]      def Ray          (A B : Point) := …
@[atlas_latex "\\overleftrightarrow{$1$2}"]  def LineThrough  (A B : Point) := …
@[atlas_latex "$1 - $2 - $3"]                def Between      (A B C : Point) := …
@[atlas_latex "$1 \\text{ guards } $2, $3"]  def SameSide     (L : Line) (A B : Point) := …
```

Positional `$1`, `$2`, … bind to applied arguments (1-indexed).

### Implementation outline

1. **`Atlas.lean`**: register `atlasLatexExt : PersistentEnvExtension (Name × String) …`.
   Attribute syntax `syntax (name := atlasLatex) "atlas_latex" str : attr`.
   Hook stores `(decl, template)` pairs.
2. **Query helper**: `Atlas.atlasLatexTemplate? : Environment → Name → Option String`.
3. **`scripts/DumpDecls.lean`**: per-decl emit `atlas_latex` when present.
   Optional: dump top-level `blueprint/latex_templates.json` for fast viewer lookup.
4. **`scripts/graph.html`'s `leanToLatex`**:
   - Drop hardcoded geometry-name rewrites (currently lines ~1580–1620,
     the `geom` array).
   - Add substitution step: walk `\mathrm{Name} <tok> <tok> …` patterns;
     if `Name` has a template in the loaded map, do positional substitution;
     otherwise leave as `\mathrm{Name}`.
   - Keep Unicode-op subs, Finset-literal collapse, and prefix→infix
     prop-combinator rewrites (Mathlib-side, not ours to tag).

### Trade-offs

- **Pro**: extensible without viewer edits; rendering rule lives next to
  def; new constructs auto-work.
- **Con**: doesn't help with Mathlib-side names (`Set.instMembership.mem`,
  `Finset.instInsert.insert`) — those still need the regex layer.
- **Open question**: how to handle templates that need to apply *inside*
  a parenthesised expression (current `\overline{(AB)}` → `\overline{AB}`
  paren-stripping). Probably keep the cleanup pass even after this refactor.

### Order

Wait until bulk theorem migration is finished. Knowing which constructs
show up *most often after migration* tells us which to tag first.

### Cost

~30 LOC `Atlas.lean` + ~5 LOC `DumpDecls.lean` + ~40 LOC `graph.html`
(mostly deletion) + per-construct annotations as you go.

---

## `obvious` as codification of Greenberg's tactical repertoire

**Status:** in-flight (simp-set extension). `argument` atlas kind is planned.

`obvious` aims to capture **Greenberg's tactics**, not just his results.
The stuff Greenberg delegates **entirely to the reader's intuition** — the
*minimum-standard intuition* the text assumes. When the author writes "and
clearly", they're not citing; they're invoking shared background. `obvious`
is that background, made explicit.

The distinction:
- **A *result* of the book** → an atlas decl (lemma, proposition, theorem).
  Referenced by `ref kind N` / `via kind N args`.
- **A *tactical move* of the book** → a piece of `obvious`'s logic. Invoked
  by `obvious` (no name, no citation — author considered it beneath mention).

When Greenberg writes "and clearly P", what's clear is some *combination* of:
- Canonical simp-normalizations (commutativities, definitional unfoldings)
- A pattern of pre-fab argument structures the author has already taught
  the reader to "see through" by this point in the text
- A sequencing of tactics idiomatic for this corner of geometry

`obvious` should look at the proof state, recognize when one of these
patterns applies, and discharge it — *not* a Swiss-army knife like `aesop`,
but a curated, chapter-by-chapter accumulating record of "what the author
treats as background."

### Near-term: simp-set extension

`register_simp_attr obvious`. Each chapter tags its contribution: canonical
commutativities, definitional rewrites. `obvious`'s `simp_all only [obvious, ...]`
expands to all tagged-before-this-point lemmas — progressive extension by
import order.

Handles the "definitional rewrites" half of Greenberg's tactics but not
the structural patterns.

### Attribute name + atlas surfacing

User wants the attribute spelled `@[obvious]`. Two options:
- Plain rename: `register_simp_attr obvious`. Risk: `obvious` is also the
  tactic macro name. Lean attribute and tactic namespaces are separate, so
  this probably works but needs verification.
- Compromise: `@[obvious]` as a *label attribute* (Mathlib's
  `register_label_attr`-style) that also triggers a simp tag. Decouples
  user-facing name from implementation.

Atlas surfacing: a decl tagged `@[obvious]` should be visible in atlas
metadata — at minimum so the viewer can render those nodes with a visual
flag ("part of the obvious set"). Either an `atlasObviousExt` env extension,
or have the dumper query the `obvious` simp set directly via
`Lean.Meta.Simp.getSimpExtension?`.

### What this doesn't handle yet — structural patterns

The `@[obvious]`-as-simp-tag mechanism captures *definitional rewrites*.
It doesn't capture *structural argument patterns* — "split this betweenness
via B-3 then case on the three witnesses", "the LHS of the inequality
follows from the RHS by symmetry", etc.

### Longer-term: atlas `argument` kind

A new atlas kind `argument` representing *reusable proof-state manipulations*.
Named like an atlas decl but its "content" is a tactic block, not a Prop.
The rule for promoting something to an `argument`: "we found ourselves
doing this same proof-state shuffle three times; it's tactical knowledge,
not a theorem."

```lean
atlas argument 2.A "splitting an intersection condition by axiom B-3" := by
  ...
```

`obvious` would invoke registered `argument`s as part of its sequencing —
not as simp-rules, but as small tactic-mode subroutines tried in order.
Sequencing: definitional simps first, then specific arguments by chapter
relevance, then a generic fallback.

`argument` is **NOT** a Prop-valued decl, so sits outside the type-checking
discipline of regular atlas decls. Closer to a Mathlib "macro" or "tactic"
— but registered through atlas so it inherits the metadata (chapter,
number, title, page reference) and shows up in the dep graph viewer.

### Why this is worth the complexity

Greenberg's text is dense with "and clearly", "by an analogous argument",
"as before", "as in 2.1". Each one is a place where the author points at
a tactic the reader has internalized — not a theorem they can cite. A
Lean formalization that only models the *results* misses half of what the
book teaches. `obvious` (and eventually `argument`) is how we model the rest.

### Pre-condition for `argument`

Simp-set version reveals the shape of what *can't* be captured as simp
rules — that's the shape `argument` needs to fill. Don't design `argument`
before the simp-set version is in use.

---

## Card "cites" tile

**Status:** planned.

User-facing line per cited decl, prose form:

> cites: lemma 1.2.3 "Two distinct points on two lines force the lines to coincide"
> cites: proposition 3.3 "Betweenness from shared outer pair: B-C-D from A-B-C and A-C-D"
> cites: axiom B-3 "Three distinct collinear points have exactly one between-arrangement"

### Mechanism (already wired)

`DumpDecls.lean` already emits per-decl `deps: [<atlas-fqn>, ...]` (filtered
to atlas-tagged callers). The viewer has every decl's `atlas_kind`,
`atlas_number`, `atlas_title`. Building the prose list is viewer-only:

```js
const citesList = d.deps
  .map(name => nodesById.get(name))
  .filter(Boolean)
  .map(target =>
    `cites: ${target.atlas_kind} ${target.atlas_number} ` +
    `"${target.atlas_title}"`);
```

### Placement

New card section (`.node-section node-cites`) above or below the source
pane. Probably below — source is the meaty bit; reading top-down hits
metadata → statement → source → cites → narrative.

### Interactive: click-to-warp

Each cited entry's `kind N "title"` is a clickable link. Clicking pans/zooms
the canvas to the target node's card and highlights it (reuse existing
tap-on-node handler — likely `cy.center(node)` + selection style):

```js
`<a class="cites-link" data-target="${target.id}">${kind} N "title"</a>`
// delegated handler:
document.addEventListener('click', e => {
  const link = e.target.closest('.cites-link');
  if (!link) return;
  const tgt = cy.getElementById(link.dataset.target);
  if (tgt.length) { cy.center(tgt); cy.fit(tgt, 200); tgt.flashClass?.('cited-flash'); }
});
```

Verify the existing tap handler's effects (selection, source-pane update,
etc.) and reuse rather than reimplement — `tgt.trigger('tap')` may be the
right delegation.

### Variations to consider once it's in

- **De-dup**: if a decl is cited multiple times in the proof, list once.
- **Indirect citations**: direct deps only for now; transitive is a separate query.
- **Tier-sort**: axioms first, then propositions, then lemmas? Or by
  chapter/number order ("as it appears in the proof" feel)? Number-order
  is simpler and reads naturally.
- **Citation inversion**: also a "cited by" list ("used in...") — bigger
  UX choice, defer until requested.

### Cost

~30 LOC viewer-side. No backend or pipeline work.

---

## Card visual polish — deferred

**Status:** deferred until commentary metadata work lands.

After Phase 1 side-by-side landing, three known visual nits to address
once we're done iterating on data structures:

### 1. Syntax highlighting lost in `.bn-code`

Right-column `<pre class="bn-code">` doesn't inherit the highlighting CSS
from `.node-source-body`. `highlightLean(codeText)` still emits the right
`<span class="lean-kw">` / `lean-const` / `lean-var` tokens, but the new
`.bn-code` selector doesn't carry the per-class color rules.

Fix: either copy color rules under `.bn-code` (cheap, duplicates CSS) or
extend existing `.node-source-body .lean-*` selectors to also target
`.bn-code .lean-*` (cleaner). Probably the latter.

### 2. Background mismatch between segments and card body

`.bn-grid` has `background: rgba(238, 232, 213, 0.3)` and `.bn-seg-left`
has `0.55` — visible band against the parent card's paper-color
(`#ede1c7` for theorems). Looks like a strip laid on top rather than part
of the card.

Fix options:
- Drop `.bn-grid` background entirely; let it inherit the card's paper
  color. Add subtle borders between segments instead.
- Match `.bn-grid` background to card's kind-specific paper color via CSS
  variable.

Card-kind backgrounds computed in `cardBgForKind`. Easiest path: expose
that as a CSS variable on the card root and have `.bn-grid` reference it.

### 3. Multi-line `comment "..."` not fully filtered from source pane

Observed in `proposition 3.3.i` (`Ch3/Prop/P3.lean`): the multi-line
`comment "..."` right after the `quoting (4)` block leaks into the
right-column code chunk instead of being stripped out. Single-line
markers filter cleanly; multi-line content does not. The marker-stripping
pass likely only matches up to the first newline of the string literal.

Same problem will affect multi-line `quoting (N) "..."` markers if any
exist.

Fix: extend the regex / parser that locates marker spans in the source
text to match across newlines (Lean strings allow literal newlines).

Recorded; not yet fixed.

### 4. Card content overflow — can't scroll

Long content (large source pane, deep book-narrative grids) overflows the
card's bounding box but isn't scrollable. User can see content is clipped
but has no way to reach it without resizing via the corner handle.

Fix: `.node-card-body` (and/or `.node-source-body`, `.bn-grid`) should be
`overflow-y: auto` with some max-height. Watch out for cytoscape's
`nodeHtmlLabel` mechanism — overflow may interact badly with how cytoscape
sizes the underlying node. May need to use the inspector pane (which has
its own scroll context) for long content; let the on-canvas card show a
teaser only.

Cards are sized via per-card resize handles already; scroll inside the
resized box is the natural complement.

### Why deferred

Once Phase 2 (commentary block, aliases, preface, notes) lands and the
cites-tile is wired up, the card has its final structural shape —
restyling makes sense then. Restyling now risks doing it twice.

---

## Live Kuzu queries in viewer

**Status:** planned.

**Goal:** the dep-graph viewer at `scripts/graph.html` currently shows a
single pre-baked Cytoscape snapshot derived from `blueprint/graph.json`.
Drop that intermediate JSON in favour of running arbitrary Cypher queries
live against `blueprint/graph.kuzu/` from the page.

### Recommended path: embed `kuzu-wasm`

`@kuzu/kuzu-wasm` npm package. GH-Pages-hostable confirmed — official
kuzu-wasm docs site lives at `unswdb.github.io/kuzu-wasm/`. Load WASM from
CDN (`https://unpkg.com/@kuzu/kuzu-wasm@latest/dist/kuzu-browser.js`),
fetch `blueprint/graph.kuzu/*` over HTTP into the in-browser virtual
filesystem, open via `kuzu.Database` + `kuzu.Connection`, then
`conn.query("MATCH ...")` returns JSON.

GH-Pages caveats: COOP/COEP headers for SharedArrayBuffer aren't set by
default — use single-threaded kuzu-wasm build to sidestep. `.wasm` MIME
type served correctly out of the box.

### Why over alternatives

- Tiny-Python-backend (Flask/FastAPI `/query` endpoint): works, but not
  static; can't host on GH Pages; needs `nix develop` to start.
- Persistent `kuzu` CLI over socket: same loss-of-static-hosting + more glue.

WASM route is a strict superset of the existing flow — keep
`blueprint/graph.json` as fallback if WASM init fails.

### What to build

1. Replace JSON-load in `graph.html` with `kuzu-wasm` init that fetches
   `blueprint/graph.kuzu/*` and opens a connection. Keep Cytoscape rendering
   layer; just swap the data source.
2. Add a query UI. User unsure of exact UX:
   (a) raw Cypher textbox with run button + result pane
   (b) `scripts/queries/*.cypher` as a dropdown of canned queries
   (c) inspector-pane auto-queries (click a node → forward/reverse deps
       without typing)
   Pick one or stage as a, b, c.
3. Wire result rendering: subgraph overlay/highlight on Cytoscape view +
   table pane for raw rows.
4. Verify `.kuzu` directory size is reasonable to ship as static asset.

### How to apply

Sanity-check that `kuzu-wasm` can actually open a DB written by the
desktop kuzu version `just graph` currently uses — same on-disk format
expected, but verify with a smoke test before sinking time into the
viewer rewrite. If incompatible, the export step would need to re-serialise
via the WASM build.

### When

After chapter-1 renumber compaction lands so canned queries don't reference
soon-to-change numbers.

### Not a blocker

User: "it's not a blocker if it doesn't but it'd be nice." If WASM hits
unexpected snags, fall back to the tiny-Python-backend route — same viewer
UX, just needs `just graph-view` to spawn the query server alongside the
static file server.

---

## Chapter-1 renumber compaction

**Status:** planned, one-time operation.

**Goal:** sweep through chapter-1 theory-lemma numbers and re-number to be
contiguous, then propagate new numbers to every `ref lemma 1.0.N` call site.

### Current state

Atlas decls under chapter 1 live at slots `1.0.{1, 2, 5, 6, 7, 10, 11, 12,
…, 40}` — gaps at `{3, 4, 8, 9}`. Gaps came from the renumber-script
(`/tmp/renumber.py`) mistakenly matching `atlas axiom "B.1.a" "Title"` and
similar pre-bracketed-string forms before they were fixed to
`atlas axiom ["B.1.a"] "Title"`. Numbers are unique, so atlas extension
works correctly — sequentiality is broken, mildly annoying.

### Why

User flagged this as separate from inline-lookup work. "Get it right
once" — compact before publishing or before call sites multiply further.

### How

1. Build `(file, line, current_num) → new_num` mapping for chapter 1 only,
   allocating new numbers in source-order starting at `1.0.1`.
2. Edit each atlas decl to use new number.
3. Global substitution `ref lemma 1.0.<old> → ref lemma 1.0.<new>` across
   all `.lean` files in `Geometry/`.
4. `lake build Geometry AtlasTest` — verify no regressions.

### When

Before any other planned atlas features (`atlas_latex`, page reference,
commentary/figure) land — those will also touch call sites; one pass through
them is enough.

One-time operation. Subsequent insertions should extend the chapter range
rather than re-compact.

---

## Shipping a CLI with a Lean library

**Status:** open question. No good standard answer in the Lean
ecosystem yet.

Atlas's CLI tool (`atlas dump`, `atlas serve`, etc.) is shipped via:
- `scripts/atlas.py` — Python implementation.
- `bin/atlas` — bash shim that resolves the atlas package root via
  `readlink` and exec's the Python.

The end-state UX we want: a downstream project does `require atlas`,
runs `lake update`, and then `./atlas <verb>` works from their repo
root with zero further setup. We're currently one short: the symlink
`./atlas → .lake/packages/atlas/bin/atlas` is a one-time manual step.

### Why this is hard

Lake doesn't have a post-`require` / post-update hook that runs in
the consumer's workspace. The patterns that would auto-install a
console script (Cargo's `cargo install`, Python's
`pip install -e .` writing entry points, Node's `npm i` with
`bin` scripts in package.json) all require a non-Lean ecosystem
hook. Lean has none.

### Workarounds explored

- **Lake exe + `lake exe atlas`** — possible (we have `dumpdecls` /
  `dumpimports` working this way). But it's a Lean exe; for our CLI
  to be Python we'd write a tiny Lean shim that spawns Python, which
  has its own atlas-root-resolution headache. And `lake exe` is
  still a two-word invocation; doesn't get the user to `./atlas`.

- **Symlink the bin script** — what we ship. One manual step
  per-project. Clear, no magic, but not "zero setup."

- **`shellHook` in `flake.nix`** — atlas exposes a `shellHook` that
  the consumer's flake includes; on `nix develop`, the symlink is
  created. Works for the nix-using subset of users; not universal.

- **`atlas init`** — a CLI subcommand that creates the symlink +
  `.gitignore` line on first run. Still requires the user to invoke
  it once.

- **Pure-Lean CLI** — write `atlas` as a Lean exe with kuzu FFI and
  Lean's HTTP server. Then `lake exe atlas` is the canonical
  invocation; no Python dep. User has noted the FFI is "rough"; not
  on the near-term path. Still wouldn't solve the `./atlas`
  ergonomics — `lake exe` is the closest you'd get.

### The broader question

Is there a "right" way to ship a CLI tool with a Lean library that
the broader Lean ecosystem should adopt? Worth raising with the Lean
community at some point — if there's a pattern proposed for Lake to
support, atlas should be one of the early users.

Until then: the symlink-the-bin-script pattern is the best
available. Documented + automated via flake `shellHook` covers the
common cases.

---

## Atlas standalone extraction — Mathlib dep

**Status:** planned. Gated on Atlas extraction.

Atlas in-repo currently imports one Mathlib file purely for the
unused-tactic linter exemption:

```lean
import Mathlib.Tactic.Linter.UnusedTacticExtension  -- in Atlas.lean

#allow_unused_tactic! Atlas.quotingExplicit Atlas.quotingContinuation
                       Atlas.commentMarker Atlas.pageBreakMarker
```

The four marker tactics intentionally don't modify goal state (record
metadata to env extensions), so Lean's `linter.unusedTactic` flags every
call site. Mathlib's `#allow_unused_tactic!` is a clean per-syntax-kind
exemption — but it's a Mathlib feature.

### What standalone Atlas should do

Three viable patterns when Atlas is its own library:

1. **Split into Mathlib-compat shim**. Atlas-core has no Mathlib dependency.
   Separate optional `Atlas.MathlibCompat` file contains the
   `#allow_unused_tactic!` directive and imports the Mathlib linter.
   Downstream users with Mathlib import the shim; users without don't.
2. **Document and punt**. README tells users to add the directive in their
   own setup file if they care about clean lint output. Cheapest; adds
   boilerplate at every user-site.
3. **Find a Lean-core equivalent**. Lean core has `linter.unusedTactic`
   option but no per-syntax allow-list as of 2026-05. If one appears,
   switch to it.

**Recommended: option 1.** Shim is one file, lives alongside the core
library, Mathlib coupling is opt-in.

### Why exemption is the right semantics (not a fix)

User confirmed: "they are being used, just not for proving." Exemption
isn't a hack to silence a warning — it's a correct statement about what
these tactics do. Linter's heuristic (no goal-state change = unused) is
reasonable for proof tactics in general; markers are the legitimate exception.

### Other Mathlib deps in this repo's Atlas

None on the macro/elab side. Other Mathlib usage is in the project's
geometric content (`Geometry/Tactics.lean` imports Mathlib chunks for
`tauto`, `aesop`, `ext`, etc.) which is independent of Atlas's extraction.

### Touchpoints when extracting

- `Atlas.lean:1-2`: drop `Mathlib.Tactic.Linter.UnusedTacticExtension` import.
- `Atlas.lean:bottom`: move `#allow_unused_tactic!` into shim file.
- Atlas core's `import Lean` stays.
- All env extensions and macros are pure Lean-core.
