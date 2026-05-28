# Atlas TODO

Atlas is a Lean 4 + JS/Python tool for tagging declarations with
book-style metadata (kind / number / title), annotating proofs with
inline markers (`quoting`, `comment`, `idea`, …), and surveying the
resulting theorem graph through a static-hosted viewer. The full
"what is Atlas" pitch lives in `README.md`; the architectural design
lives in `DESIGN.md`; this file is the punchlist.

This directory is a **point-in-time snapshot** of Atlas as it lived
in `~/rivendell/geometry_is_your_friend` (GIYF) at the time of
extraction. Active development still happens in GIYF until the
extraction is complete and GIYF pulls Atlas as a Lake dependency.
See `CHECKPOINT.md` for the snapshot bookkeeping.

---

## In flight — finishing the extraction

- [ ] **Extraction to standalone library.** Move Atlas out of GIYF
  into this repo as its own Lean package; GIYF depends on it via
  Lake. Pre-conditions met: file split (below), fixture corpus
  shipped, mereology demo scaffolded. Remaining: dumper-
  parameterisation, manifest pin, GIYF lakefile update.

- [ ] **Mereology demo proofs.** Chapter 1 is fully proved; Ch2–4
  are scaffolded with `sorry`'d proof bodies + full commentary.
  Fill in proofs as the spirit moves. Per `README.md`, a full
  formalization is out of scope — the demo's job is to render
  beautifully and exercise every Atlas feature, not to be
  authoritative mereology.

- [ ] **SHA-connected dumps for CI.** Each `blueprint/*.json` dump
  carries the git SHA it was built from; CI accumulates dumps over
  commits to track the theorem graph over time. Lets the viewer
  diff between revisions, show growth curves, etc. Requires:
  - Dump scripts read `git rev-parse HEAD` (or accept `--sha` flag).
  - Output layout supports multiple SHAs.
  - Retention policy so CI doesn't accumulate forever.

- [ ] **Parameterise the dumpers over the target library.**
  `DumpDecls.lean` / `DumpImports.lean` / `DumpTactics.lean` /
  `AtlasProbe.lean` all hardcode `import Geometry` and walk
  `Geometry/**`. For Atlas-as-a-library, this needs to be CLI / env
  / Lake-metadata driven. First cut: `ATLAS_TARGET_MODULE` env var,
  read by both the Lean dumpers and the Python helpers. *Blocks*
  the Atlas-local corpus from actually dumping anything.

- [ ] **`atlas` CLI — full implementation.** Skeleton landed at
  `bin/atlas` (shell shim) + `scripts/atlas.py` (Python entry
  point); subcommands stubbed with argparse. Next: wire each verb
  to its real backend.
  - `dump` — orchestrate `lake build` + `lake exe dumpdecls` +
    `dumpimports` + `run_dumptactics.py` + `ingest.py`. Wants
    `--target <module>` (tightly coupled to the dumper-
    parameterisation TODO above) and `--sha` for SHA-connected
    dumps.
  - `import <file|dir>` — atomic-import a single dump or a
    directory of per-SHA dumps. Today's `ingest.py` does the full
    pipeline; we need a finer-grained entry point.
  - `serve` — wrap `python -m http.server` (or successor) on a
    configurable port. `--watch` later.
  - `query` / `q` — `run_query.py` / `q.sh` re-implemented in
    Python for consistent UX.
  - `show <kind> <num>` — JSON read of `decls.json` +
    `commentary.json`, pretty-printed.
  - `stats` — the coverage tool (separate TODO).
  - `check` — sanity scan (orphan commentary, paired-decl
    ambiguities, etc.).
  - `db init` / `db reset`.

- [ ] **Ingest markers + commentary into kuzu.** Today the dump
  writes `blueprint/{markers,commentary}.json` and the viewer reads
  them directly, but `scripts/schema.cypher` and `ingest.py` only
  cover `Decl` / `Module` / `Tactic` / `USES` / `DECLARED_IN` /
  `IMPORTS` / `USED_TACTIC`. The README promises that markers
  (`todo`, `fixme`, etc.) and commentary fields are *queryable* via
  Cypher; that's not true yet. Add:
  - `Marker` node table (kind, decl, file, line, column, text, +
    `step` / `trailing` for `quoting`, + `tags` once tag prefixes
    land).
  - `Commentary` node table (target decl, page, name, preface,
    notes, aliases-array, tags-array).
  - `HAS_MARKER` and `HAS_COMMENTARY` rels from `Decl`.
  - Bundled queries for the obvious cuts: `todo` count by file,
    sorry'd decls by chapter, etc.

- [ ] **Coverage tool (`atlas stats`).** Cross-check the dump
  against the feature registries:
  - Every kind in `Atlas/Basic.lean::kindTiers` (plus exact-only)
    should appear in at least one decl.
  - Every `atlasNum` syntax form should be exercised.
  - Every marker tactic name in `Atlas/Markers.lean` (incl. the
    `cf` / `see also` shared bucket) should appear.
  - Every commentary field (`page`, `pages`, `name`, `aliases`,
    `preface`, `notes`, `tags`) should be populated somewhere.
  Output: ✓ / ✗ table + first-sample-decl per feature. Run against
  the combined Corpus + Mereology dump. CI-friendly non-zero exit
  on miss.

- [ ] **Atlas-as-a-Lake-dep ergonomics.** Currently `require atlas`
  + `lake update` + a one-time
  `ln -s .lake/packages/atlas/bin/atlas ./atlas` symlink gives the
  consumer a working `./atlas <verb>`. Lake has no post-update
  hook to automate the symlink. Workarounds in priority order:
  1. Document the symlink + `.gitignore` line (one manual step).
  2. Ship a `shellHook` in `flake.nix` for the nix-using subset
     so `nix develop` does the symlink on entry.
  3. `atlas init` subcommand that creates the symlink + writes
     `.gitignore` on first run.
  Long-term, raise this with the Lean community — see
  `DESIGN.md` "Shipping a CLI with a Lean library."

---

## Planned features

Each item has a longer write-up in `DESIGN.md`. Status-tagged
inline. Grouped by where the work lands.

### Lean-side (Atlas core)

- [ ] **Theorem complexes.** First-class named clusters of related
  decls (proposition + alternates + corollaries). `ref complex
  P3.1 args` dispatches across all members by type. Distinct from
  `aliases` (renaming) — `complex` is multi-target membership.

- [ ] **Applicators on complexes.** Per-complex tactic/term macros
  that encapsulate the canonical *patterned argument shape* for
  invoking the complex. Caller writes `applicator P3.3.chain args`
  instead of remembering which member fits and in what order.
  Layer on top of basic complex membership.

- [ ] **Tag prefixes on code-state markers.**
  `todo[refactor] "..."`, `fixme[blocked] "..."`,
  `detail[coercion] "..."`. Marker records gain a
  `tags : Array String` field. Viewer filters/groups by tag.
  Code-state markers only.

- [ ] **Atlas third-name / multi-form references.** Re-introduce a
  short-name alias channel (`Geometry.Theory.line.separation`) so
  each decl is reachable by number, title, OR namespaced
  short-name. Commentary block's `aliases [...]` field already
  records these but doesn't yet emit Lean-level aliases —
  finishing the elab side is what's pending. Theorem complexes
  may absorb some of the motivation here.

- [ ] **`@[atlas_latex "template"]` attribute.** Move per-decl
  LaTeX rendering rules from the viewer's regex layer
  (`graph.html`) into structured Atlas attributes.

- [ ] **`obvious` as codification of authorial tactics.** Curated
  chapter-accumulating simp set + a small tactic framework
  mirroring what the book treats as background. Near-term:
  `@[obvious]` simp attribute. Long-term: atlas `argument` kind
  for reusable proof-state manipulations beyond simp rules.

- [ ] **Inline annotation vocabulary expansion.** Future marker
  kinds beyond the current 13 (3 original + 10 extended). Mechanism
  is well-trodden (~30 LOC per kind).

- [ ] **External tagging — noninvasive atlas overlays.** Tag
  *someone else's* existing Lean code with atlas metadata without
  modifying it: a separate "overlay" file imports the target and
  applies `atlas mathlib_proposition 1.5 "..." := Continuous.comp`
  forms. Lets a downstream project survey-tag Mathlib or any third-
  party library through Atlas's lens. See `DESIGN.md`.

### Display-half (viewer / pipeline)

- [ ] **Live Kuzu queries in the viewer (kuzu-wasm).** Embed
  `@kuzu/kuzu-wasm` in `scripts/graph.html` so the viewer can run
  arbitrary Cypher against `blueprint/graph.kuzu/` client-side.
  Static-hostable. Use single-threaded build to dodge COOP/COEP.

- [ ] **PageRank-based node sizing.** Today's viewer sizes nodes
  uniformly; the README promises PageRank-weighted sizing.
  PageRank pass in the dump pipeline (Cypher-native or via
  networkx); viewer reads per-node rank attribute and sets size.
  Layered layout (axioms at bottom) stays as-is.

- [ ] **Card "cites" tile.** Prose list of cited atlas decls per
  card, clickable to warp to target. Data already in `d.deps`;
  viewer-only, ~30 LOC.

- [ ] **In-editor lookup for `ref` forms.** ProofWidgets4 panel in
  the InfoView listing referenced lemmas with kind / number /
  title / preface. Same widget framework hosts figure previews
  (below). Fallbacks: hover provider, `#info` command, generated
  HTML index.

- [ ] **Figures & generated constructions** — two-phase:
  - Phase 1: `figure [paths]` field on `atlas commentary` for
    hand-authored SVG / PNG. Viewer embeds inline.
  - Phase 2: declarative `construction := by ...` DSL inside
    commentary; build compiles to GeoGebra (`.ggb`) + rendered
    SVG. Live ProofWidgets4 preview while editing.

- [ ] **Atlas kind-tier visual cues.** Per-tier card tinting (T1
  results / T2 derived / T3 commentary) so tier is obvious at a
  glance.

- [ ] **Final visual design for extended marker vocab.** Current
  rendering (`.bn-chip-<kind>`) is dummy. Per-kind treatment
  (luminous `idea`, italic `aside`, hyperlinky `cf`, etc.) is in
  `DESIGN.md` but not implemented.

- [ ] **Card visual polish — deferred bag.** Four known nits:
  1. Syntax highlighting lost in `.bn-code` (right-column).
  2. Background mismatch between `.bn-grid` and card paper colour.
  3. Multi-line `comment` / `quoting` text leaks into the
     right-column code chunk (the marker-stripping regex only
     matches the first line). Same bug hits multi-line extended
     markers.
  4. Card content overflow — can't scroll; long content gets
     clipped under the resize handle.

- [ ] **Embedded editor in the viewer (vision).** Dynamic theorem
  edits with live re-elaboration. Needs kuzu-wasm + some way to
  talk to a Lean elaborator. Vague — its own design pass when the
  foundation is in place.

### Build / packaging

- [ ] **Pure-Lean atlas implementation (vision).** Long-term, the
  CLI could live as a pure Lean exe — FFI to kuzu, Lean's built-in
  webserver for `serve`, no Python in the dep tree. User noted the
  FFI is "rough." Holding pattern; doesn't block any current work.

- [ ] **Atlas-core Mathlib decoupling.** Current `Atlas.lean`
  imports `Mathlib.Tactic.Linter.UnusedTacticExtension` purely for
  the `#allow_unused_tactic!` directive on the no-op marker
  tactics. Plan: move the directive into an `Atlas.MathlibCompat`
  shim file. Atlas-core stays Mathlib-free; downstream users who
  already have Mathlib pull the shim explicitly.

---

## Already shipped (this snapshot)

### Lean-side

- 3-part numbering `Chapter.Level.Index` via `scientific . num`
  atlasNum (e.g. `2.0.1`).
- Sub-letter numbers `Chapter.Section.suffix` via
  `scientific . ident` atlasNum (e.g. `3.1.i`, `3.1.a`) for paired
  decls.
- Bracketed-string fallback `["B.1.a"]` for compound labels.
- `ref <kind> <num>` uniform term-position form.
- `via <kind> <num> args*` vararg-capturing paired-decl dispatch —
  resolves to the candidate whose return type unifies with the
  expected type.
- Title-based identifier (`«Pasch's Postulate»`) with positionful
  `mkIdentFrom` for tooling-friendly source ranges.
- `Atlas.atlasStateFromImports` helper — workaround for
  `addImportedFn` not reliably propagating across module
  boundaries.
- Commentary block (`atlas commentary := by …`) — top-level
  metadata holder with `ref` / `page` / `pages` / `name` /
  `aliases [...]` / `preface` / `notes` / `tags [...]`. Resolved
  at dump time. Supersedes the old (un-built) `atlas commentary
  <ref> "<text>"` standalone-command plan.
- Inline marker family — `quoting (N)`, `quoting ...`, `comment`,
  `page break` (book voice + page tracking).
- Extended marker vocabulary — `idea`, `intuition`, `motivation`,
  `caution`, `aside`, `cf` / `see also`, `todo`, `fixme`, `detail`.
  Unified `InlineMarker` schema, single env extension,
  bucketed-by-kind in `markers.json`.
- Monolithic `Atlas.lean` (1230 LOC) split into
  `Atlas/{Basic,Number,Command,Ref,Via,Markers,Commentary}.lean`
  + thin `Atlas.lean` re-export.

### Display-half

- `DumpDecls` / `DumpImports` / `DumpTactics` — extract atlas
  state + dep graph + per-decl tactic occurrences into
  `blueprint/*.json` and `blueprint/graph.kuzu/`.
- Static-hosted viewer (`scripts/graph.html`) — Cytoscape dep
  graph with per-decl cards, side-by-side book↔proof narrative
  grid for marker-tagged proofs, commentary block rendered as
  card-header section.
- Kuzu schema + 9 bundled Cypher queries + `q` dispatch helper.
- Surface-and-filter for extended marker vocab — markers strip
  from the right-column code chunk automatically; render as
  kind-coloured chips in the left column.

### Tooling / packaging

- Fixture corpus (`Corpus/*.lean`) — one file per feature class,
  exercising every `atlasNum` form, every marker kind, every
  commentary field, paired-decl dispatch.
- Mereology demo (`Mereology/*.lean`) — small obscure-theory
  e2e demo. Chapter 1 fully proved; Ch2–4 scaffolded with
  `sorry`'d proofs + full commentary.
- `bin/atlas` shell shim + `scripts/atlas.py` Python entry
  point — CLI skeleton with argparse subcommands.
- Dev-gated `Corpus` and `Mereology` lean_libs
  (`meta if get_config? env = some "dev"`).

---

## Rules / behavioural notes

- [Keyword collision policy](docs/keyword_collision.md) — Why
  `theorem` / `lemma` / `axiom` are *not* exposed as `<kind> N.K`
  term-position references, and the rule for adding new Atlas
  kinds. Critical reading before extending the term-syntax
  surface.

---

## Bootstrap notes

`Atlas.lean` itself only depends on Lean stdlib + one Mathlib
import (`Mathlib.Tactic.Linter.UnusedTacticExtension`) for the
`#allow_unused_tactic!` directive on the no-op marker tactics.
Plan to move that into an `Atlas.MathlibCompat` shim so Atlas-core
stays Mathlib-free — see the build/packaging section above.

`AtlasTest.lean` pulls in `Mathlib.Tactic.Lemma` to exercise the
bare-`lemma` coexistence guarantee.

`Corpus.lean` and `Mereology.lean` depend on `Atlas` only; the
fixture corpus is Mathlib-free, the mereology demo could become so
(no current Mathlib uses in `Mereology/*.lean`).
