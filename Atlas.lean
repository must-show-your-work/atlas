/-
# Atlas — book-style theorem metadata for Lean 4

Atlas tags Lean declarations with **kind / number / title** in the
book-mathematics style and adds matching reference + commentary +
inline-marker syntax. The viewer (`scripts/graph.html`) reads dumps
produced from the env extensions and renders proper book-style cards.

This top-level module is a thin re-export. The actual implementation
lives under `Atlas/*` — feature-clustered for navigation and
independent iteration. Importing `Atlas` brings the lot in. Files
under `Atlas/` can also be imported individually if a consumer only
wants part of the surface (e.g. `import Atlas.Basic` for just the
env-extension API without the syntax category and tactics).

## Module map

- `Atlas/Basic.lean` — types, env extension, attribute, kind tiers.
- `Atlas/Number.lean` — `atlasNum` syntax category + canonical render.
- `Atlas/Command.lean` — `atlas <kind> <num> "Title" : T := body`.
- `Atlas/Ref.lean` — term-position `ref kind N` + per-kind shortcuts.
- `Atlas/Via.lean` — vararg-capturing `via kind N args*` dispatch.
- `Atlas/Markers.lean` — inline marker tactics (quoting/comment/page
  break + extended vocab).
- `Atlas/Commentary.lean` — `atlas commentary := by …` block.
- `Atlas/Figure.lean` — `figure := by …` nested field + flip-through
  widget panel for figures attached to atlas decls.
- `Atlas/Refs.lean` — InfoView panel auto-attached to atlas proofs
  showing each decl's atlas-tagged citations + an explicit
  `#refs <name>` command.

## Usage

```
import Atlas

atlas proposition 3.4 "Pasch's Postulate" : <type> := <proof>
atlas commentary := by
  ref proposition 3.4
  page 113
  preface "..."

example : T := ref proposition 3.4
example : T := via proposition 3.4 ⟨arg1, arg2⟩

theorem ex : T := by
  quoting (1) "step text from the book"
  comment "author commentary"
  -- ... proof body ...
```

See `DESIGN.md` for the architectural design notes and `AtlasTest.lean`
for the smoke test that exercises the full elaboration pipeline.
-/

import Atlas.Basic
import Atlas.Number
import Atlas.Command
import Atlas.Ref
import Atlas.Via
import Atlas.Markers
import Atlas.Figure
import Atlas.Commentary
import Atlas.Refs
