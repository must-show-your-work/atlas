/-
Atlas/Markers.lean — inline marker tactics.

Three original kinds + ten extended-vocabulary kinds, all `pure ()`
semantically with the side effect of pushing a record into a
per-kind env extension. The graph dumper (scripts/DumpDecls.lean)
reads them out, the viewer renders them side-by-side with the source.

Original (book-voice / page-tracking):
- `quoting (N) "..."`, `quoting ... "..."` — Greenberg verbatim,
  step + optional continuation/decorative ellipsis.
- `comment "..."` — author's editorial voice.
- `page break` — page-boundary marker.

Extended (reader-cue + code-state):
- Reader-cue: `idea`, `intuition`, `motivation`, `caution`, `aside`,
  `cf`, `see also` (alias of `cf`).
- Code-state: `todo`, `fixme`, `detail`.

The extended vocabulary shares a unified `InlineMarker` schema
(kind + position + text), one env extension, kind-discriminated at
the elab site. Future planned extension: tag prefixes
(`todo[refactor] "..."`) — see `DESIGN.md`.

`#allow_unused_tactic!` directive at the bottom exempts all 14 tactic
names from the unused-tactic linter. This is the SOLE Mathlib
dependency in Atlas-core; future plan is to move it into an
`Atlas.MathlibCompat` shim once extraction lands.
-/

import Lean
import Mathlib.Tactic.Linter.UnusedTacticExtension
import Atlas.Basic

open Lean Elab Command

namespace Atlas

/-! ## Inline commentary markers: `quoting`, `comment`, `page break`

These four no-op tactics record book-text and authorial annotation at
specific source positions inside proof bodies. The graph viewer reads
them out (via `DumpDecls.lean` → `blueprint/markers.json`) and renders
side-by-side with the code.

- `quoting (N) "..."` — Greenberg verbatim, step N.
- `quoting ... "..."` — continuation of previous quoting marker.
- `comment "..."`     — author commentary, position-anchored.
- `page break`        — page-boundary marker (the viewer counts these
                        before each `quoting` to compute its page).

Each marker is `pure ()` semantically — the proof state is untouched.
The side effect is an entry pushed into the corresponding env extension.

Trailing `...` after a `quoting` string is decorative (renders as `…`
in the viewer to signal the book text continues beyond the excerpt).
It doesn't affect semantics.

Single-line strings only for v1. Multi-line book paragraphs split
into multiple continuation calls — that's the natural side-by-side
rendering granularity anyway. -/

/-- Source-position-anchored quoting marker. `step? = none` means
    "continuation of previous". -/
structure QuotingMarker where
  decl      : Name
  modName   : Name
  line      : Nat
  column    : Nat
  step?     : Option Nat
  text      : String
  trailing  : Bool   -- true if the trailing `...` was present
  deriving Inhabited

/-- Source-position-anchored author commentary marker. -/
structure CommentMarker where
  decl    : Name
  modName : Name
  line    : Nat
  column  : Nat
  text    : String
  deriving Inhabited

/-- Source-position-anchored page-boundary marker. -/
structure PageBreakMarker where
  decl    : Name
  modName : Name
  line    : Nat
  column  : Nat
  deriving Inhabited

-- All three extensions go through `Atlas.Basic.registerArrayExt`, which
-- bakes in `asyncMode := .sync` (required: our `modifyEnv` calls happen
-- inside tactic elab, which runs on parallel env branches; default
-- `.mainOnly` mode silently drops those writes).

initialize atlasQuotingExt : SimplePersistentEnvExtension QuotingMarker (Array QuotingMarker) ←
  registerArrayExt `Atlas.atlasQuotingExt

initialize atlasCommentExt : SimplePersistentEnvExtension CommentMarker (Array CommentMarker) ←
  registerArrayExt `Atlas.atlasCommentExt

initialize atlasPageBreakExt : SimplePersistentEnvExtension PageBreakMarker (Array PageBreakMarker) ←
  registerArrayExt `Atlas.atlasPageBreakExt

/-- Resolve a syntax position to (line, column). Returns `(0, 0)` if
    position info is missing — shouldn't happen for parsed user syntax
    but we don't want a crash if it does. -/
private def markerPos (stx : Syntax) : Lean.Elab.Term.TermElabM (Nat × Nat) := do
  match stx.getPos? with
  | none     => return (0, 0)
  | some pos =>
    let fileMap ← Lean.MonadFileMap.getFileMap
    let p := fileMap.toPosition pos
    return (p.line, p.column)

/-- Resolve the enclosing declaration name (the atlas decl we're inside
    of). Falls back to `.anonymous` if we're not inside a decl, which
    would be a user error — the marker would be orphaned. -/
private def markerDecl : Lean.Elab.Term.TermElabM Name := do
  return (← Lean.Elab.Term.getDeclName?).getD .anonymous

/-- Push a quoting marker to the env extension. -/
private def recordQuoting (stx : Syntax) (step? : Option Nat) (text : String)
    (trailing : Bool) : Lean.Elab.Term.TermElabM Unit := do
  let (line, column) ← markerPos stx
  let decl ← markerDecl
  let modName := (← getEnv).mainModule
  modifyEnv (atlasQuotingExt.addEntry · { decl, modName, line, column, step?, text, trailing })

private def recordComment (stx : Syntax) (text : String) : Lean.Elab.Term.TermElabM Unit := do
  let (line, column) ← markerPos stx
  let decl ← markerDecl
  let modName := (← getEnv).mainModule
  modifyEnv (atlasCommentExt.addEntry · { decl, modName, line, column, text })

private def recordPageBreak (stx : Syntax) : Lean.Elab.Term.TermElabM Unit := do
  let (line, column) ← markerPos stx
  let decl ← markerDecl
  let modName := (← getEnv).mainModule
  modifyEnv (atlasPageBreakExt.addEntry · { decl, modName, line, column })

-- Tactic-mode syntaxes.
--
-- `quoting (N) "text"` — explicit step N, optional trailing `...`.
-- `quoting ... "text"` — continuation, optional trailing `...`.
-- `comment "text"`     — author marker.
-- `page break`         — page-boundary marker.
--
-- `colGt` ensures continuation parsing stays on the same logical line
-- so `quoting (1) "..." \n rcases ...` works (next tactic starts at
-- left-edge column).

syntax (name := quotingExplicit) "quoting" "(" num ")" str ("..." )? : tactic
syntax (name := quotingContinuation) "quoting" "..." str ("..." )? : tactic
syntax (name := commentMarker) "comment" str : tactic
syntax (name := pageBreakMarker) "page" "break" : tactic

open Lean Elab Tactic in
@[tactic quotingExplicit]
def elabQuotingExplicit : Tactic := fun stx => do
  -- Raw structure: "quoting" "(" num ")" str ("...")? — 6 children.
  -- The trailing `...` is an optional null-node group at index 5; if
  -- it has any children, the literal `...` was present.
  let trailing := stx[5].getNumArgs > 0
  let nNat := stx[2].toNat
  let textStr ← match stx[4].isStrLit? with
    | some s => pure s
    | none   => throwError "quoting: expected string literal"
  recordQuoting stx (some nNat) textStr trailing

open Lean Elab Tactic in
@[tactic quotingContinuation]
def elabQuotingContinuation : Tactic := fun stx => do
  -- Raw structure: "quoting" "..." str ("...")? — 4 children.
  let trailing := stx[3].getNumArgs > 0
  let textStr ← match stx[2].isStrLit? with
    | some s => pure s
    | none   => throwError "quoting: expected string literal"
  recordQuoting stx none textStr trailing

open Lean Elab Tactic in
@[tactic commentMarker]
def elabComment : Tactic := fun stx =>
  match stx with
  | `(tactic| comment $t:str) => do
      recordComment stx t.getString
  | _ => throwUnsupportedSyntax

open Lean Elab Tactic in
@[tactic pageBreakMarker]
def elabPageBreak : Tactic := fun stx =>
  match stx with
  | `(tactic| page break) => do
      recordPageBreak stx
  | _ => throwUnsupportedSyntax


/-! ## Extended inline markers — reader-cue and code-state vocabulary

These ten no-op tactics extend the marker family with kinds the design
doc plans for: reader-cue annotations (`idea`, `intuition`, `motivation`,
`caution`, `aside`, `cf` / `see also`) and code-state annotations
(`todo`, `fixme`, `detail`).

All share a uniform schema (`InlineMarker`) — kind, source position,
text — and record into a single env extension `atlasInlineMarkerExt`.
The kind discriminates rendering on the viewer side. `cf` and `see also`
are surface aliases; both record under the same kind (`cf`).

Each marker is `pure ()` semantically; the side effect is the env-
extension push. Linter exemption via `#allow_unused_tactic!` below.

Examples:
```
idea "The trick is to split on `Classical.em (P on ray A B)` first."
intuition "Think of L as a wall separating two halfplanes."
motivation "We need this lemma before tackling Pasch."
caution "Don't apply ref lemma 2.0.4 to the wrong endpoint."
aside "Greenberg revisits this in Ch. 7."
cf "Pasch's Postulate (3.7)"
see also "Greenberg p.121, where this is revisited."
todo "Refactor the ref-in-ref chain on line 88."
fixme "Sorry'd; needs a B-3 case split."
detail "Why does `obvious` not close this? Coercion mismatch?"
```
-/

/-- Source-position-anchored generic inline marker. `kind` discriminates
    among `idea`, `intuition`, `motivation`, `caution`, `aside`, `cf`,
    `todo`, `fixme`, `detail`. -/
structure InlineMarker where
  kind    : Name
  decl    : Name
  modName : Name
  line    : Nat
  column  : Nat
  text    : String
  deriving Inhabited

initialize atlasInlineMarkerExt :
    SimplePersistentEnvExtension InlineMarker (Array InlineMarker) ←
  registerArrayExt `Atlas.atlasInlineMarkerExt

private def recordInlineMarker (kind : Name) (stx : Syntax) (text : String)
    : Lean.Elab.Term.TermElabM Unit := do
  let (line, column) ← markerPos stx
  let decl ← markerDecl
  let modName := (← getEnv).mainModule
  modifyEnv (atlasInlineMarkerExt.addEntry · { kind, decl, modName, line, column, text })

-- Tactic-mode syntaxes for each kind. `see also` parses as a two-token
-- keyword (mirroring `page break`); records under kind `cf` so the
-- viewer treats the two surface forms uniformly.
syntax (name := ideaMarker)       "idea"        str : tactic
syntax (name := intuitionMarker)  "intuition"   str : tactic
syntax (name := motivationMarker) "motivation"  str : tactic
syntax (name := cautionMarker)    "caution"     str : tactic
syntax (name := asideMarker)      "aside"       str : tactic
syntax (name := cfMarker)         "cf"          str : tactic
syntax (name := seeAlsoMarker)    "see" "also"  str : tactic
syntax (name := todoMarker)       "todo"        str : tactic
syntax (name := fixmeMarker)      "fixme"       str : tactic
syntax (name := detailMarker)     "detail"      str : tactic

open Lean Elab Tactic in
@[tactic ideaMarker]
def elabIdea : Tactic := fun stx =>
  match stx with
  | `(tactic| idea $t:str) => recordInlineMarker `idea stx t.getString
  | _ => throwUnsupportedSyntax

open Lean Elab Tactic in
@[tactic intuitionMarker]
def elabIntuition : Tactic := fun stx =>
  match stx with
  | `(tactic| intuition $t:str) => recordInlineMarker `intuition stx t.getString
  | _ => throwUnsupportedSyntax

open Lean Elab Tactic in
@[tactic motivationMarker]
def elabMotivation : Tactic := fun stx =>
  match stx with
  | `(tactic| motivation $t:str) => recordInlineMarker `motivation stx t.getString
  | _ => throwUnsupportedSyntax

open Lean Elab Tactic in
@[tactic cautionMarker]
def elabCaution : Tactic := fun stx =>
  match stx with
  | `(tactic| caution $t:str) => recordInlineMarker `caution stx t.getString
  | _ => throwUnsupportedSyntax

open Lean Elab Tactic in
@[tactic asideMarker]
def elabAside : Tactic := fun stx =>
  match stx with
  | `(tactic| aside $t:str) => recordInlineMarker `aside stx t.getString
  | _ => throwUnsupportedSyntax

open Lean Elab Tactic in
@[tactic cfMarker]
def elabCf : Tactic := fun stx =>
  match stx with
  | `(tactic| cf $t:str) => recordInlineMarker `cf stx t.getString
  | _ => throwUnsupportedSyntax

open Lean Elab Tactic in
@[tactic seeAlsoMarker]
def elabSeeAlso : Tactic := fun stx =>
  match stx with
  | `(tactic| see also $t:str) => recordInlineMarker `cf stx t.getString
  | _ => throwUnsupportedSyntax

open Lean Elab Tactic in
@[tactic todoMarker]
def elabTodo : Tactic := fun stx =>
  match stx with
  | `(tactic| todo $t:str) => recordInlineMarker `todo stx t.getString
  | _ => throwUnsupportedSyntax

open Lean Elab Tactic in
@[tactic fixmeMarker]
def elabFixme : Tactic := fun stx =>
  match stx with
  | `(tactic| fixme $t:str) => recordInlineMarker `fixme stx t.getString
  | _ => throwUnsupportedSyntax

open Lean Elab Tactic in
@[tactic detailMarker]
def elabDetail : Tactic := fun stx =>
  match stx with
  | `(tactic| detail $t:str) => recordInlineMarker `detail stx t.getString
  | _ => throwUnsupportedSyntax


end Atlas

-- Mark the marker tactics as legitimately-unused per the linter.
-- They look like no-ops to the linter (don't touch goals) but are
-- meaningful side-effect recordings into env extensions. The `!`
-- makes the allowance persist across importing modules.
#allow_unused_tactic! Atlas.quotingExplicit Atlas.quotingContinuation
                       Atlas.commentMarker Atlas.pageBreakMarker
                       Atlas.ideaMarker Atlas.intuitionMarker
                       Atlas.motivationMarker Atlas.cautionMarker
                       Atlas.asideMarker Atlas.cfMarker
                       Atlas.seeAlsoMarker Atlas.todoMarker
                       Atlas.fixmeMarker Atlas.detailMarker
