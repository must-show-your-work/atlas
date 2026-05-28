# Resume — picking back up in Atlas

Short orientation for a new session. Read this first; everything
else is in the docs it points at.

## What this repo is

Standalone-in-progress Atlas: book-style theorem metadata for Lean 4
+ a static-hosted graph viewer. Today it's a **point-in-time copy**
of the Atlas system from
`~/rivendell/geometry_is_your_friend` (GIYF), staged for the
extraction. Active development still happens in GIYF until GIYF can
`require atlas` from this repo as a Lake dependency.

## Read for context (in order)

1. **`README.md`** — public-facing "what is Atlas." User-authored.
   *Don't edit without asking.* Has an empty CLI section the user
   will fill in.
2. **`CHECKPOINT.md`** — what's in this snapshot, what differs from
   the second snapshot, what's GIYF-specific and needs adapting
   before this stands alone (8 items, in priority order).
3. **`TODO.md`** — punchlist. "In flight," "Planned features"
   (Lean-side / Display-half / Build), "Already shipped (this
   snapshot)."
4. **`DESIGN.md`** — architectural detail for every major feature,
   shipped or planned. ~24 sections, status-tagged.

## Current state in one paragraph

Atlas-the-library has been split from a 1230-LOC monolith into
`Atlas/{Basic,Number,Command,Ref,Via,Markers,Commentary}.lean`
with a thin `Atlas.lean` re-export. Two demo libs are dev-gated:
`Corpus/` (fixture-style coverage of every Atlas feature) and
`Mereology/` (small obscure-theory e2e demo; Ch1 fully proved,
Ch2–4 stubbed with `sorry`). A Python+bash CLI skeleton lives at
`scripts/atlas.py` + `bin/atlas`, with argparse subcommands all
stubbed. Nothing actually builds in this repo yet — Lake's first
`lake update` wants to bump the toolchain past what GIYF pins.

## Immediate next moves (in dependency order)

1. **Resolve the Lake manifest.** Pin Mathlib + Verso to commits
   compatible with `lean-toolchain` (`leanprover/lean4:v4.27.0-rc1`).
   Until done, no Lean code here builds.
2. **Parameterise the dumpers** (`DumpDecls.lean`, `DumpImports.lean`,
   `DumpTactics.lean`, `AtlasProbe.lean`, `run_dumptactics.py`)
   over `ATLAS_TARGET_MODULE`. Today they hardcode `import Geometry`.
   Until done, the Corpus + Mereology libs can't actually be dumped.
3. **Move the `#allow_unused_tactic!` Mathlib import** to an
   `Atlas.MathlibCompat` shim. Atlas-core stays Mathlib-free.
4. **Wire `atlas` CLI subcommands** to real backends — `dump`,
   `import`, `serve`, `query`, `q`, `show`, `stats`, `check`, `db
   init/reset`. Skeleton is in place; the stubs need to call the
   actual `lake exe` / `ingest.py` / `http.server` / etc.
5. **Ingest markers + commentary into kuzu.** README promises that
   `todo` / `fixme` and other markers are queryable via Cypher;
   currently they're in JSON but not in the graph DB. Schema +
   ingest update.

These five unlock most of the rest of `TODO.md`.

## Then: GIYF imports Atlas

After the above (or even just steps 1–2), GIYF can:
- Add `require atlas from "../../angband/human/curu/atlas"` (or a
  git URL once published) to its `lakefile.lean`.
- Delete its local `Atlas.lean` + `AtlasTest.lean` + the duplicated
  `scripts/*` (the canonical copies live here).
- Keep its `Geometry/` source tree, `Justfile`, blueprint outputs.

That's the "import it back and use it here" the user mentioned.

## Don't

- Don't touch `README.md` without asking — user-authored.
- Don't `lake update` casually — it'll re-bump the toolchain.
  Pinning the manifest is the right move; updating before pinning
  loses the pin.
- Don't promote `Corpus` / `Mereology` out of the `dev` gate —
  they're not meant for consumer surface.
- Don't fill in Mereology Ch2–4 proofs unless explicitly asked.
  The user's stance (in README) is that a full Casati–Varzi
  formalization is out of scope; the demo just needs to render
  beautifully.

## Open questions worth surfacing

- **Lake post-update hook to auto-symlink `./atlas`** — Lake
  doesn't have one. Workaround is `ln -s
  .lake/packages/atlas/bin/atlas ./atlas` one-time. Worth raising
  with the Lean community (see DESIGN.md "Shipping a CLI with a
  Lean library").
- **Coverage measurement** — TODO records the goal: cross-check
  the dump against feature registries. Not yet implemented.
- **Theorem complexes + applicators** — designed but not built.
  Pre-condition for letting `ref proposition 3.1` cleanly
  dispatch across paired decls without forcing `via`.

## Provenance

- LLM/agent involvement to date is roughly 80/20 per README. This
  RESUME and most of the recent docs are agent-written; the
  README, the design intent, and the architectural choices are
  the user's.
- Mereology demo + Corpus fixtures were LLM-generated. The user's
  stance is that they likely won't get further attention beyond
  finishing the formalization at the level needed for Atlas to
  exercise its features.
