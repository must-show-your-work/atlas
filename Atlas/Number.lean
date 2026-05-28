/-
Atlas/Number.lean — `atlasNumLit` standalone Parser + canonical string render.

**Why a standalone Parser, not a syntax category:**

The natural shape for atlas IDs is "anything between dots":
`3.Review.3.a.i`, `B.4.i`, `Ch3.Theory.5.a`, etc. Lean's built-in lexer
(`Lean/Parser/Basic.lean:879-880`) commits to scientific-notation parsing
the moment it sees `<digits> '.'` and errors with "unexpected identifier
after decimal point" if the next char is a letter. That blocks any ID
with an internal `<num>.<letter>` boundary.

A custom `ParserFn` can read raw chars and bypass the tokenizer entirely
— BUT only if Lean's framework doesn't tokenize first. The catch is
`prattParser`'s dispatch (`Basic.lean:1908-1921, 1697-1698`): for any
syntax *category*, `peekToken` runs unconditionally before any parser in
the category is tried, including the "unindexed leading parsers" that
opt out of first-token routing. If `peekToken` errors, the category
dispatcher bails before our parser ever runs.

So we DON'T declare `atlasNum` as a category. Instead, `atlasNumLit` is
a direct `Parser` used inline in consumer syntax declarations
(`Atlas/Command.lean`, `Atlas/Ref.lean`, `Atlas/Via.lean`,
`Atlas/Commentary.lean`). Inline parsers are sequenced via `andthenFn`
(`Basic.lean:90-92`), which doesn't call `peekToken` — so the
tokenizer never gets a chance to trip on our IDs.

The trade-off: every consumer must use `atlasNumLit` directly instead
of the cleaner `atlasNum` category shorthand. Pattern matches that used
to use `\`(atlasNum| …)` now walk the syntax atom directly via
`atlasNumToString?`.
-/

import Lean

namespace Atlas

open Lean Parser

/-! ## Syntax node kind for the custom-lexed atlas number. -/

/-- The single atom node kind that `atlasNumFn` pushes onto the parser
stack. The atom's raw text is the canonical ID string (e.g.,
`"3.Review.3.a.i"`). -/
def atlasNumKind : SyntaxNodeKind := `atlasNumLit

/-- Character predicate for an atlasNum body. Includes alphanumerics,
underscore (for slugs), and hyphen (for Greenberg's `B-1a` / `B-4ii`
compound axiom labels). -/
private def isAtlasNumChar (c : Char) : Bool :=
  c.isAlphanum || c == '_' || c == '-'

/-- ParserFn reading an atlasNum as one raw greedy token of shape
`isAtlasNumChar+ ('.' isAtlasNumChar+)*`. Bypasses Lean's lexer
entirely — `takeWhileFn` reads chars directly from `c.input` without
calling `tokenFn`. -/
private partial def atlasNumFn : ParserFn := fun c s =>
  let startPos := s.pos
  if h : c.atEnd s.pos then
    s.mkUnexpectedError "atlasNum: expected digit or letter"
  else
    let firstCh := c.get' s.pos h
    if !isAtlasNumChar firstCh then
      s.mkUnexpectedError s!"atlasNum: expected digit or letter, got '{firstCh}'"
    else
      let s := takeWhileFn isAtlasNumChar c s
      let s := readDots c s
      mkNodeToken atlasNumKind startPos true c s
where
  /-- Greedy: consume `.<segment>` while next char is dot-then-validChar.
  Back off if next is dot-then-EOF / dot-then-other (don't eat the dot). -/
  readDots c s :=
    if h : c.atEnd s.pos then s
    else if c.get' s.pos h != '.' then s
    else
      let afterDot := c.next' s.pos h
      if h2 : c.atEnd afterDot then s
      else if !isAtlasNumChar (c.get' afterDot h2) then s
      else
        let s := s.setPos afterDot
        let s := takeWhileFn isAtlasNumChar c s
        readDots c s

/-- The atlas-number Parser used directly in consumer syntax
declarations. `firstTokens := .unknown` means our parser doesn't claim
any specific leading token — and since we're used in `andthen`
position (not a category), no `peekToken` runs before our `fn`.

Wrapped in `withAntiquot`/`mkAntiquot` so consumers can write
antiquotation patterns like `$n:atlasNumLit` in syntax declarations —
mirroring the pattern from `Lean.Parser.numLit`. -/
def atlasNumLit : Parser :=
  withAntiquot (mkAntiquot "atlasNumLit" atlasNumKind) {
    fn := atlasNumFn
    info := { firstTokens := .unknown }
  }

-- The PrettyPrinter wants combinator formatter/parenthesizer for any
-- custom `Parser`. Use the standard atom visitors keyed on our kind.
@[combinator_formatter atlasNumLit, expose]
def atlasNumLit.formatter : PrettyPrinter.Formatter :=
  PrettyPrinter.Formatter.visitAtom atlasNumKind

@[combinator_parenthesizer atlasNumLit, expose]
def atlasNumLit.parenthesizer : PrettyPrinter.Parenthesizer :=
  PrettyPrinter.Parenthesizer.visitToken

/-! ## Canonical-string extraction. -/

/-- Walk a Syntax tree and return the first atom's raw text. Works
because `atlasNumFn` produces a node with a single atom child carrying
the full ID. -/
private partial def syntaxFirstAtom? : Syntax → Option String
  | .atom _ raw => some raw
  | .node _ _ args => args.toList.findSome? syntaxFirstAtom?
  | _ => none

/-- Pure extraction: given an atlasNumLit-produced Syntax, return the
canonical string. Used by Ref/Via/Commentary which run in TermElabM. -/
def atlasNumToString? (stx : Syntax) : Option String := syntaxFirstAtom? stx

/-- MacroM-flavored version for the `atlas` command (which runs in
`MacroM`). -/
def atlasNumToString (stx : Syntax) : MacroM String :=
  match atlasNumToString? stx with
  | some s => return s
  | none   => Macro.throwUnsupported

end Atlas
