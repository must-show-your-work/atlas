/-
Atlas/Command.lean — `atlas <kind> <num> "Title" : T := body` command.

The two `syntax` declarations + `macro_rules` that turn an atlas decl
into either a `theorem`, `def`, or `axiom` carrying the `@[atlas k n t]`
attribute. The kind word is parsed via `rawIdent` so it can coexist
with Lean's command keywords (`lemma`, `axiom`, `theorem`) — see the
keyword-collision policy in `docs/keyword_collision.md`.

Body-less arm is reserved for `atlas axiom` (the only kind that doesn't
have a proof).

Depends on `Atlas/Basic.lean` (attribute) and `Atlas/Number.lean`
(atlasNumToString).
-/

import Lean
import Atlas.Basic
import Atlas.Number
import Atlas.Panels

open Lean Elab Command

namespace Atlas

/-! ## Command macros -/

/-- The TSyntax type for a sequence of bracketed binders
    (`{A : T}`, `(x : T)`, `[h : T]`, etc.). Passed through verbatim
    to the underlying `theorem`/`axiom`/`def` declaration. -/
abbrev BracketedBinders := TSyntaxArray ``Lean.Parser.Term.bracketedBinder

/-- An optional doc comment, captured before the `atlas` keyword and
    forwarded onto the generated declaration so `/-- … -/` attaches
    normally. -/
abbrev DocComment? := Option (TSyntax ``Lean.Parser.Command.docComment)

/-- Generate `@[atlas "kind" "num" "title"] theorem «title» <binders> : type := body`,
    prepending an optional doc comment so the macro can be preceded by
    `/-- … -/` like any builtin theorem. Helpers take `numStr : String`
    directly — callers either feed `← atlasNumToString n` (numbered
    form) or `""` (un-numbered form). The attribute hook treats empty
    string as "no book number" and skips the (kind, number) duplicate
    check accordingly. -/
private def expandAtlasTheorem
    (kind : String) (numStr : String)
    (title : TSyntax `str) (binders : BracketedBinders)
    (doc? : DocComment?) (ty body : Term)
    : MacroM (TSyntax `command) := do
  let kindLit := Syntax.mkStrLit kind
  let numLit  := Syntax.mkStrLit numStr
  -- Preserve the source range of `title` on the generated identifier
  -- so downstream tooling (e.g. SubVerso highlighter) sees a real
  -- definition-site token rather than a synthetic one. `mkIdent` alone
  -- produces a positionless ident, which `SubVerso.Highlighted.definedNames`
  -- treats as not-a-def-site and so omits from the per-decl extraction.
  let ident   := mkIdentFrom title.raw (Name.mkSimple title.getString)
  match doc? with
  | some doc =>
    `($doc:docComment
      @[atlas $kindLit $numLit $title] theorem $ident $binders* : $ty := $body)
  | none =>
    `(@[atlas $kindLit $numLit $title] theorem $ident $binders* : $ty := $body)

private def expandAtlasAxiom
    (kind : String) (numStr : String)
    (title : TSyntax `str) (binders : BracketedBinders)
    (doc? : DocComment?) (ty : Term)
    : MacroM (TSyntax `command) := do
  let kindLit := Syntax.mkStrLit kind
  let numLit  := Syntax.mkStrLit numStr
  -- Preserve the source range of `title` on the generated identifier
  -- so downstream tooling (e.g. SubVerso highlighter) sees a real
  -- definition-site token rather than a synthetic one. `mkIdent` alone
  -- produces a positionless ident, which `SubVerso.Highlighted.definedNames`
  -- treats as not-a-def-site and so omits from the per-decl extraction.
  let ident   := mkIdentFrom title.raw (Name.mkSimple title.getString)
  match doc? with
  | some doc =>
    `($doc:docComment
      @[atlas $kindLit $numLit $title] axiom $ident $binders* : $ty)
  | none =>
    `(@[atlas $kindLit $numLit $title] axiom $ident $binders* : $ty)

private def expandAtlasDef
    (kind : String) (numStr : String)
    (title : TSyntax `str) (binders : BracketedBinders)
    (doc? : DocComment?) (ty body : Term)
    : MacroM (TSyntax `command) := do
  let kindLit := Syntax.mkStrLit kind
  let numLit  := Syntax.mkStrLit numStr
  -- Preserve the source range of `title` on the generated identifier
  -- so downstream tooling (e.g. SubVerso highlighter) sees a real
  -- definition-site token rather than a synthetic one. `mkIdent` alone
  -- produces a positionless ident, which `SubVerso.Highlighted.definedNames`
  -- treats as not-a-def-site and so omits from the per-decl extraction.
  let ident   := mkIdentFrom title.raw (Name.mkSimple title.getString)
  match doc? with
  | some doc =>
    `($doc:docComment
      @[atlas $kindLit $numLit $title] def $ident $binders* : $ty := $body)
  | none =>
    `(@[atlas $kindLit $numLit $title] def $ident $binders* : $ty := $body)

-- Every atlas decl carries a number — this is what lets us add the
-- uniform term-position `atlas <kind> <num>` form below without parser
-- ambiguity. (An un-numbered command form would compete with that term
-- form on the `atlas <ident>` prefix and prevent backtracking.)
--
-- For theory lemmas without a book reference, use the three-part
-- `<chapter>.<level>.<index>` scheme — `<chapter>` is the book chapter
-- the file belongs to, `<level>` is the proposition number that the
-- lemma's deps require (0 if independent), `<index>` is sequential.
--
-- The kind word is parsed as `rawIdent` — accepts any identifier
-- including those reserved as keywords elsewhere (Mathlib's `lemma`,
-- Lean's `axiom`, etc.). This is what lets `atlas lemma <num> "Title"`
-- coexist with bare `lemma X : T := body` in the same module: no
-- token shadowing. The kind ident's text is validated in `macro_rules`
-- below.
syntax (docComment)? "atlas" rawIdent atlasNumLit str (bracketedBinder)* ":" term ":=" term : command
syntax (docComment)? "atlas" rawIdent atlasNumLit str (bracketedBinder)* ":" term            : command

-- Known kinds that expand to `def`; everything else expands to
-- `theorem` (or `axiom` for the body-less arm).
private def isDefKind (kind : String) : Bool := kind == "definition"

macro_rules
  -- Numbered, body-having.
  | `($[$doc?:docComment]? atlas $k:ident $n:atlasNumLit $t:str $bs:bracketedBinder* : $ty := $b) => do
      let kind := k.raw.getId.toString
      if kind == "axiom" then
        Macro.throwErrorAt k
          "atlas axiom takes no `:= body`; write `atlas axiom <num> \"<title>\" : <type>`"
      let numStr ← atlasNumToString n
      if isDefKind kind then
        expandAtlasDef kind numStr t bs doc? ty b
      else
        -- Theorem-flavored body: if tactic-mode, wrap in
        -- `with_atlas_panels` so the InfoView gets the per-decl refs +
        -- figures panels (elab lives in `Atlas/Refs.lean`). Term-mode
        -- bodies pass through unwrapped.
        let bodyWrapped ← match b with
          | `(by $tacs:tacticSeq) =>
              let kindLit := Syntax.mkStrLit kind
              let numLit  := Syntax.mkStrLit numStr
              `(by with_atlas_panels $kindLit $numLit $tacs)
          | _ => pure b
        expandAtlasTheorem kind numStr t bs doc? ty bodyWrapped
  -- Numbered axiom (no body).
  | `($[$doc?:docComment]? atlas $k:ident $n:atlasNumLit $t:str $bs:bracketedBinder* : $ty) => do
      let kind := k.raw.getId.toString
      if kind != "axiom" then
        Macro.throwErrorAt k
          s!"atlas {kind} requires `:= body` (only `atlas axiom` is body-less)"
      expandAtlasAxiom kind (← atlasNumToString n) t bs doc? ty

end Atlas
