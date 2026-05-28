/-
Atlas/Commentary.lean — `atlas commentary := by …` block.

Top-level command (NOT a tactic): a `:= by` layout re-using Lean's
parser for sequential statement parsing, where each "tactic" is one
field setter. Stores per-decl metadata that doesn't fit on the decl
signature: `ref` (required target), `page` / `pages`, `name`,
`aliases [...]`, `preface`, `notes`, `tags [...]`.

Resolved to a target decl at dump time (`scripts/DumpDecls.lean`),
not at elab time — so commentary blocks can appear *before* their
target's `atlas <kind> N` decl.

Two-namespace structure here mirrors the original layout: the
`scoped syntax` field declarations need to be inside `namespace Atlas`,
then the `command_elab` is registered in a second `namespace Atlas`
block. Don't merge — the scoped tokens won't bind correctly otherwise.

Depends on `Atlas/Basic.lean` (atlasExt for dump-time lookup),
`Atlas/Number.lean` (atlasNum + scientificAtomText).
-/

import Lean
import Atlas.Basic
import Atlas.Number
import Atlas.Figure

open Lean Elab Command

namespace Atlas

/-! ## Commentary block: `atlas commentary := by …`

Top-level metadata holder per atlas decl. Tactic-block-style layout
(re-uses Lean's parser for sequential statement parsing without an
actual proof obligation). Each "tactic" inside is one field setter.

```
atlas commentary := by
  ref proposition 3.4
  page 131                       -- or `pages 109..113`
  name "Line separation property"
  aliases [Line.separation, P3_4_via_betweenness]
  preface "If C - A - B and l is the line through A, B, and C, …"
  notes "Editorial commentary about the structure of this proof."
  tags ["separation", "B-3", "ray"]
```

The fields can appear in any order; only `ref` is required. The
viewer reads commentary out of `blueprint/commentary.json` (or
merged into the existing markers/decls dump) and renders the
metadata on the corresponding card.
-/

/-- A commentary block's resolved contents. One per `atlas commentary`.
    Field names deliberately avoid the syntax keywords (`name`,
    `aliases`, `notes`, `preface`, `tags`, `page`, `pages`) since
    declaring those as `syntax` tokens reserves them at the parser
    level and shadows struct-field LHS in literal initialization.

    The target is stored as `(targetKind, targetNum)` rather than
    a resolved `decl : Name` so commentary blocks can appear *before*
    their target's `atlas <kind> N` decl. Resolution happens at dump
    time (DumpDecls walks atlas state and pairs each commentary to
    its target decl). Each ref is intended 1:1 — if `(kind, num)`
    resolves to multiple decls at dump time (paired propositions),
    that's an error the user resolves by being more specific. -/
structure CommentaryBlock where
  targetKind  : String            -- e.g. "proposition"
  targetNum   : String            -- e.g. "3.4"
  bookPage?   : Option String     -- "131" (single page) or first of a range
  bookEnd?    : Option String     -- set when `pages 109..113` form was used
  displayName?: Option String     -- long-form title; viewer prefers this over decl title
  aliasList   : Array Name        -- alternate identifier names for the decl
  -- `(kind, num)` cross-links to OTHER atlas decls — e.g. proposition 3.5
  -- aliasing its corresponding student exercise. Rendered as link chips
  -- in the viewer (separate visual treatment from `aliasList`).
  aliasRefs   : Array (String × String) := #[]
  bookPreface?: Option String     -- book statement / intro, free-form prose
  authorNotes?: Option String     -- editorial decl-level notes
  tagList     : Array String      -- cross-cutting category tags
  deriving Inhabited

-- State stores all commentary blocks in source order. Lookup by
-- target decl happens at dump time (since commentary may appear
-- before its target's `atlas <kind> N` decl, we can't resolve eagerly).
initialize atlasCommentaryExt :
    SimplePersistentEnvExtension CommentaryBlock (Array CommentaryBlock) ←
  registerArrayExt `Atlas.atlasCommentaryExt

-- Field-grammar for the commentary block. A separate syntax category
-- AND `scoped` so the field keywords don't pollute global identifiers.
--
-- `scoped` means the tokens (`name`, `aliases`, `notes`, `tags`,
-- `preface`, `page`, `pages`) are only reserved when `Atlas` is open
-- — otherwise files that use `let tags := …` as variable names blow
-- up. Users of `atlas commentary` need `open Atlas` in scope (or do
-- `open Atlas in atlas commentary := by …`).
declare_syntax_cat atlasCommentaryField

scoped syntax (name := acRef)     "ref"     rawIdent atlasNumLit  : atlasCommentaryField
scoped syntax (name := acPage)    "page"    num                : atlasCommentaryField
scoped syntax (name := acPages)   "pages"   num ".." num       : atlasCommentaryField
scoped syntax (name := acName)    "name"    str                : atlasCommentaryField
-- An `aliases` list entry can be either:
--   * a bare ident (the legacy short-name channel: `Line.separation`)
--   * an atlas cross-ref of shape `<kind> <atlasNumLit>` (e.g.
--     `exercise 3.Review.3.c`) — links to another atlas decl.
-- The category dispatcher's `peekToken` always sees an `ident` here
-- (either the short name or the kind keyword), so the tokenizer trap
-- isn't an issue inside aliases.
declare_syntax_cat aliasEntry
scoped syntax (name := aliasEntryRef)   rawIdent atlasNumLit : aliasEntry
scoped syntax (name := aliasEntryIdent) ident                : aliasEntry

scoped syntax (name := acAliases) "aliases" "[" aliasEntry,* "]" : atlasCommentaryField
scoped syntax (name := acPreface) "preface" str                : atlasCommentaryField
scoped syntax (name := acNotes)   "notes"   str                : atlasCommentaryField
scoped syntax (name := acTags)    "tags"    "[" str,* "]"      : atlasCommentaryField
-- Nested figure block: each `figure := by …` declares one figure with
-- its own metadata. Multiple blocks per commentary are allowed and the
-- viewer's flip-through widget cycles between them.
scoped syntax (name := acFigure)
  "figure" ":=" "by" (ppLine atlasFigureField)*                 : atlasCommentaryField

-- Top-level command. `:= by` is purely cosmetic — re-uses Lean's
-- visual idiom for "indented block of statements." There's no actual
-- `by` tactic block being parsed; we declare the literal tokens and
-- then a list of our own field-category statements.
scoped syntax (name := atlasCommentary)
  "atlas" "commentary" ":=" "by" (ppLine atlasCommentaryField)* : command

end Atlas


namespace Atlas

/-- Convert an `atlasNumLit` syntax to its canonical string key. -/
private def atlasNumToStringCmt (num : Syntax) : MetaM String :=
  match atlasNumToString? num with
  | some s => pure s
  | none   => throwError "atlas commentary: malformed number reference"

open Lean Elab Command in
@[command_elab atlasCommentary]
def elabAtlasCommentary : CommandElab := fun stx => do
  -- stx[4] is the `(ppLine atlasCommentaryField)*` group of fields.
  let fields := stx[4].getArgs
  -- Accumulate fields. Order-independent; later occurrences of the
  -- same field overwrite earlier ones (per-field "last write wins").
  --
  -- Local names deliberately avoid the field keywords (`aliases`,
  -- `tags`, `name`, `notes`, `preface`, `page`, `pages`) — declaring
  -- those as `syntax` tokens reserves them at the parser level, which
  -- can shadow same-named identifiers when Lean re-parses the body.
  let mut tgtKind? : Option String      := none
  let mut tgtNum?  : Option String      := none
  let mut pg?      : Option String      := none
  let mut pgEnd?   : Option String      := none
  let mut nm?      : Option String      := none
  let mut aliasNs  : Array Name         := #[]
  let mut aliasRfs : Array (String × String) := #[]
  let mut pref?    : Option String      := none
  let mut nt?      : Option String      := none
  let mut tagStrs  : Array String       := #[]
  -- Pending figures: each `figure := by …` field is parsed eagerly
  -- (file read happens now), but the env extension push waits for the
  -- target `(kind, num)` to be resolved from the `ref` field below.
  let mut pendingFigs : Array Figure := #[]
  for fld in fields do
    -- Each field's outer node has one of the named kinds we declared
    -- above. Match on kind, then destructure the args.
    match fld with
    | `(atlasCommentaryField| ref $k:ident $n:atlasNumLit) =>
      tgtKind? := some k.getId.toString
      tgtNum?  := some (← liftTermElabM (atlasNumToStringCmt n))
    | `(atlasCommentaryField| page $p:num) =>
      pg? := some (toString p.getNat)
    | `(atlasCommentaryField| pages $a:num .. $b:num) =>
      pg? := some (toString a.getNat)
      pgEnd? := some (toString b.getNat)
    | `(atlasCommentaryField| name $s:str) =>
      nm? := some s.getString
    | `(atlasCommentaryField| aliases [ $entries,* ]) =>
      for entry in entries.getElems do
        match entry with
        | `(aliasEntry| $k:ident $n:atlasNumLit) =>
          let numStr ← liftTermElabM (atlasNumToStringCmt n)
          aliasRfs := aliasRfs.push (k.getId.toString, numStr)
        | `(aliasEntry| $i:ident) =>
          aliasNs := aliasNs.push i.getId
        | _ => throwErrorAt entry "atlas commentary: malformed aliases entry"
    | `(atlasCommentaryField| preface $s:str) =>
      pref? := some s.getString
    | `(atlasCommentaryField| notes $s:str) =>
      nt? := some s.getString
    | `(atlasCommentaryField| tags [ $ts,* ]) =>
      for t in ts.getElems do
        tagStrs := tagStrs.push t.getString
    | `(atlasCommentaryField| figure := by $fs:atlasFigureField*) =>
      let fig ← elabFigureFields fs.raw
      pendingFigs := pendingFigs.push fig
    | _ =>
      throwErrorAt fld "atlas commentary: unrecognized field"
  let some kind := tgtKind? |
    throwError "atlas commentary: missing `ref <kind> <num>` field — every commentary block must declare its target"
  let some num := tgtNum? |
    throwError "atlas commentary: missing `ref <kind> <num>` field — every commentary block must declare its target"
  -- Push the commentary block to the env extension. Target lookup
  -- happens at dump time, not here — commentary may appear before
  -- the matching atlas decl is elaborated.
  let block : CommentaryBlock :=
    { targetKind   := kind
      targetNum    := num
      bookPage?    := pg?
      bookEnd?     := pgEnd?
      displayName? := nm?
      aliasList    := aliasNs
      aliasRefs    := aliasRfs
      bookPreface? := pref?
      authorNotes? := nt?
      tagList      := tagStrs }
  modifyEnv (atlasCommentaryExt.addEntry · block)
  for fig in pendingFigs do
    -- Anonymous constructor: `figure` is now a reserved scoped token
    -- (via `acFigure`) so a `{ …, figure := fig }` LHS won't parse.
    let fb : FigureBlock := ⟨kind, num, fig⟩
    modifyEnv (atlasFigureExt.addEntry · fb)
  -- NOTE: in v1 we record alias names in the commentary block but
  -- *don't* generate Lean-level decls for them. Several attempts to
  -- emit `abbrev`/`def`/`notation` either fought the target's
  -- implicit arguments or Lean's antiquotation system; sidestepping
  -- the entire question is fine for the immediate goal (viewer can
  -- display aliases as chips). If you want `Line_separation` to be a
  -- usable identifier inside proofs, add `abbrev Line_separation :=
  -- @«Line separation by an interior point...»` manually for now;
  -- a future pass can automate this once we settle on the right
  -- decl-emission shape.
  pure ()


end Atlas
