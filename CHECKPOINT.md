# Atlas checkpoint — third snapshot

This directory is a **point-in-time copy** of the Atlas system from
`~/rivendell/geometry_is_your_friend` (GIYF). Active development
continues in GIYF until the extraction is complete and GIYF pulls
Atlas as a Lake dependency from this repo. **Don't edit files here
expecting them to flow back to GIYF.**

Three snapshots so far:
- **First** (May 17) — initial drop of the attribute + macro layer
  + the GIYF display tooling. Pre-commentary, pre-extended-vocab.
- **Second** (May 19, earlier) — commentary block, original marker
  family, viewer commentary rendering. `Atlas.lean` reached 1230
  LOC.
- **Third** (this snapshot, May 19) — extended marker vocab, file
  split, fixture corpus, mereology demo, CLI skeleton, dev-gating.

## What's new since the second snapshot

### `Atlas.lean` split

The 1230-LOC monolith is now seven files under `Atlas/` plus a
57-LOC `Atlas.lean` re-export:

- `Atlas/Basic.lean` — types, env extension, attribute, kind tiers.
- `Atlas/Number.lean` — `atlasNum` syntax + canonical render.
- `Atlas/Command.lean` — `atlas <kind> <num> "Title"` command.
- `Atlas/Ref.lean` — term-position `ref kind N` + per-kind shortcuts.
- `Atlas/Via.lean` — vararg-capturing `via kind N args*` dispatch.
- `Atlas/Markers.lean` — all 13 marker tactics + the
  `#allow_unused_tactic!` directive (Mathlib touch point now
  isolated here for the future shim move).
- `Atlas/Commentary.lean` — `atlas commentary := by …` block.

`scientificAtomText` was made non-private so Ref/Via/Commentary can
reuse it. No other semantic changes — split is mechanical.

### Extended inline marker vocabulary

Ten new no-op tactics with a unified `InlineMarker` schema (kind +
position + text). Single env extension; bucketed by kind at emit
time. Viewer has per-kind chip rendering.

- Reader-cue: `idea`, `intuition`, `motivation`, `caution`,
  `aside`, `cf`, `see also` (latter records under kind `cf`).
- Code-state: `todo`, `fixme`, `detail`.

### Fixture corpus

`Corpus/` lib — one file per feature class:

- `Numbers.lean` — every `atlasNum` syntax form.
- `Kinds.lean` — every kind that appears in `kindTiers` plus the
  exact-only ones (`alternate`, `definition`).
- `Markers.lean` — every marker tactic in a single trivial proof.
- `Commentary.lean` — minimal / typical / maximal commentary
  blocks.
- `Dispatch.lean` — paired-decl `via` dispatch + `ref` tier
  cascade.

Goal: exercise the dump → JSON → viewer path at speed without
pulling in any real mathematical content.

### Mereology demo

`Mereology/` lib — small obscure-theory e2e demo (4 chapters of
classical mereology, ~16 atlas decls). Chapter 1 fully proved;
Ch2–4 scaffolded with `sorry`'d proofs + full commentary. Tests
the renderer against book-shaped content (multi-paragraph notes,
`cf` markers to Boolean algebras / Stone duality, paired-decl
sub-letter numbering, etc.).

Originality: the README explicitly notes the commentary in this
demo is original — we don't quote the Casati–Varzi text.

### CLI skeleton

- `bin/atlas` — bash shell shim that follows symlinks (downstream
  projects symlink `./atlas → .lake/packages/atlas/bin/atlas`).
- `scripts/atlas.py` — Python entry point with argparse
  subcommands (`dump`, `import`, `serve`, `query`, `q`, `show`,
  `stats`, `check`, `db init/reset`, `version`). All stubbed.

Smoke-tested: `./atlas version`, `./atlas --help`, symlink-from-
elsewhere via `readlink` chase — all work.

### Dev-gating

`Corpus` and `Mereology` `lean_lib` declarations in `lakefile.lean`
wrapped in `meta if get_config? env = some "dev"` so downstream
consumers who `require atlas` don't see them.

```
lake -Kenv=dev build Corpus Mereology   # local dev
lake build                              # consumer surface
```

Same idiom GIYF uses for `doc-gen4`.

### DESIGN.md additions

`DESIGN.md` grew from ~17 sections to ~24, adding:

- "Atlas positioning vs Blueprint" — framing note (survey vs
  roadmap).
- "Theorem complexes + applicators" — extended with custom
  applicator macros per the README.
- "Viewer node sizing — PageRank-based importance" — to match the
  README's PageRank promise.
- "External tagging — noninvasive atlas overlays" — third use case
  from the README.
- "Shipping a CLI with a Lean library" — open-question note about
  the Lake-ecosystem gap.
- "Atlas as semi-literate programming for Lean" — framing
  introduced earlier this session; commentary block is structured
  metadata spanning both code-side and book-side.

## What was copied this round

| Path | Origin | State |
|---|---|---|
| `Atlas.lean` + `Atlas/*.lean` | GIYF | Split into 7 files + 57-LOC re-export (was 1230-LOC monolith) |
| `AtlasTest.lean` | GIYF | unchanged |
| `lean-toolchain` | GIYF | pinned back to v4.27.0-rc1 (Lake bumped it during a probe build) |
| `DESIGN.md` | GIYF | extended to ~24 sections |
| `scripts/AtlasProbe.lean` | GIYF | unchanged, still hardcodes `import Geometry.Ch3.Prop.Pasch` |
| `scripts/DumpDecls.lean` | GIYF | extended for extended-vocab buckets |
| `scripts/DumpImports.lean` | GIYF | unchanged |
| `scripts/DumpTactics.lean` | GIYF | `dropRight → dropEnd` deprecation fix |
| `scripts/run_dumptactics.py` | GIYF | unchanged |
| `scripts/ingest.py`, `export_graph.py`, `run_query.py`, `q.sh` | GIYF | unchanged |
| `scripts/schema.cypher` | GIYF | unchanged |
| `scripts/queries/*.cypher` | GIYF | unchanged |
| `scripts/graph.html` | GIYF | extended for extended marker rendering |

**New files in this snapshot** (no GIYF origin):

- `Corpus.lean` + `Corpus/*.lean` — fixture corpus.
- `Mereology.lean` + `Mereology/*.lean` — demo theory.
- `bin/atlas` — CLI shell shim.
- `scripts/atlas.py` — CLI Python entry point.
- `README.md` — user-authored (don't edit without ask).

**Not copied** (Atlas-side configs already tailored):

- `lakefile.lean` — extended in-place with the dev-gated Corpus
  and Mereology libs.
- `Justfile` — Atlas-specific recipes, unchanged.
- `scripts/vendor/katex/` — unchanged static dep.

## What still needs adapting before this stands alone

1. **Library-under-analysis is hardcoded.** Every `import Geometry`,
   every `Geometry/**` filesystem walk, every `Geometry.*` namespace
   filter is GIYF-specific. First cut: an `ATLAS_TARGET_MODULE` env
   var read by both Lean dumpers and Python helpers. Spans
   `DumpDecls.lean`, `DumpImports.lean`, `DumpTactics.lean`,
   `AtlasProbe.lean`, `run_dumptactics.py`. **Blocks the Atlas-local
   corpus from actually dumping anything.**

2. **`blueprint/` directory layout is assumed.** All output paths
   relative to a `blueprint/` subdir at the project root.
   Configurable via env var would suffice for now.

3. **`Geometry`-specific imports for hover/lookup.**
   `AtlasProbe.lean` loads `Geometry.Ch3.Prop.Pasch` to verify env
   extension wiring. Either rewrite to test against `AtlasTest.lean`
   / `Corpus.lean` / `Mereology.lean` or drop.

4. **Mathlib dependency in Atlas-core.** `Atlas/Markers.lean`
   imports `Mathlib.Tactic.Linter.UnusedTacticExtension` for the
   `#allow_unused_tactic!` directive. Plan: move the directive into
   an `Atlas.MathlibCompat` shim — Atlas-core stays Mathlib-free.
   See `DESIGN.md` "Atlas standalone extraction — Mathlib dep."

5. **Verso / SubVerso dependency.** `DumpTactics.lean` uses
   SubVerso for syntax highlighting + tactic extraction. Likely
   fine to keep as a dep of the dump tooling specifically, but
   worth isolating to a separate lib target so Atlas-core stays
   minimal.

6. **CLI subcommands are all stubs.** The skeleton routes args via
   argparse but every backend just prints a stub message. Wiring
   each verb to its real implementation is the next CLI pass — see
   `TODO.md` "`atlas` CLI — full implementation."

7. **Lake manifest pin.** First `lake update` in this directory
   tried to bump the toolchain to `v4.30.0-rc2` (matching Mathlib
   HEAD); pinned back to `v4.27.0-rc1` to match GIYF. Mathlib and
   Verso `require`s remain unpinned. Before this snapshot truly
   stands alone, pin Mathlib + Verso to specific commits compatible
   with the toolchain. Until pinned, expect Lake to drift on first
   fetch.

8. **CLI ergonomics.** `require atlas` + `lake update` gives
   `.lake/packages/atlas/bin/atlas`. One-time `ln -s ... ./atlas`
   is the only manual step. Workarounds in `TODO.md` (flake
   shellHook for nix users, `atlas init` subcommand, etc.).

## What's deliberately not here

- The `Geometry/` source tree — stays in GIYF.
- `blueprint/` outputs — GIYF-side artifacts.
- Memory files / `CLAUDE.md` / etc. — agent-private state.
- A finished implementation — see `TODO.md`. This snapshot is the
  staging ground for the next phase of work.

## Bigger picture

This snapshot's role: stage everything needed to actually do the
extraction. The pieces that block it are the dumper-parameterisation
and the Mathlib-decoupling work — both small, concrete, well-scoped.
After those, GIYF can `require atlas from "../../angband/human/curu/atlas"`
and have everything work.

The README's framing (Atlas as a tool for formalization, writing
textbooks, and exploring existing work, with a stretch goal of an
embedded editor in the viewer) is the larger destination. This
snapshot is roughly the cardboard prototype of the formalization
half; the editor + dynamic-editing vision is further out.
