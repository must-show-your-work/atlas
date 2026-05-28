/-
Atlas/Figure.lean — `figure := by …` nested field for the commentary
block, plus the env extension and flip-through InfoView widget.

A figure is one SVG (read from disk at elab time) plus metadata
(title, index, caption). Each commentary may declare multiple figure
blocks; the widget displays them with ◀ / ▶ buttons to flip through.

Figures are keyed by `(targetKind, targetNum)` of their enclosing
commentary block, matching how `CommentaryBlock` works. The atlas
macro override (in `Atlas/Refs.lean`) wraps every tactic-mode atlas
proof with `with_atlas_figures <kind> <num> <tacs>`, which looks up
matching figures and attaches the widget panel.

Reading happens at elab time (`IO.FS.readFile`) so the SVG bytes are
stored in the env extension and survive incremental builds without
needing the asset path to resolve at the consumer's runtime.
-/

import Lean
import ProofWidgets.Data.Html
import ProofWidgets.Component.HtmlDisplay
import Atlas.Basic
import Atlas.Number

open Lean Elab Command ProofWidgets

namespace Atlas

/-! ## Minimal SVG → Html parser

We need the figure's contents as a `ProofWidgets.Html` element tree
(not a raw string) so lean.nvim's TUI rasterizes it: `html.lua`
dispatches on `tag == 'svg'` to `tui.svg.serialize` which walks
`{tag, attrs, children}` and produces SVG XML that libresvg can
render. A raw `Html.text "<svg>…</svg>"` would XML-escape the inner
markup and produce nothing useful.

Scope is intentionally narrow — basic XML good enough for the figure
SVGs we hand-author. `<style>` bodies are kept as a single raw-text
child (CSS isn't valid XML, but lean.nvim's serializer only escapes
`& < >` so common CSS round-trips). Doesn't handle CDATA or namespace
prefixes beyond what passes for valid attribute names.
-/

namespace SvgParser

structure St where
  src : String
  pos : String.Pos.Raw

abbrev P := EStateM String St

private def peek? : P (Option Char) := do
  let s : Atlas.SvgParser.St ← get
  let endP : String.Pos.Raw := ⟨s.src.utf8ByteSize⟩
  return if s.pos < endP then some (String.Pos.Raw.get s.src s.pos) else none

private def advance : P Unit :=
  modify fun (s : St) => { s with pos := String.Pos.Raw.next s.src s.pos }

private def startsWith (lit : String) : P Bool := do
  let s : Atlas.SvgParser.St ← get
  let endP : String.Pos.Raw := ⟨s.src.utf8ByteSize⟩
  return (String.Pos.Raw.extract s.src s.pos endP).startsWith lit

private def consume (lit : String) : P Unit := do
  unless ← startsWith lit do throw s!"expected '{lit}'"
  let mut i := 0
  while i < lit.length do
    advance
    i := i + 1

private def expectCh (c : Char) : P Unit := do
  match ← peek? with
  | some c' => if c' = c then advance else throw s!"expected '{c}', got '{c'}'"
  | none    => throw s!"expected '{c}', got EOF"

private partial def skipWs : P Unit := do
  match ← peek? with
  | some c => if c.isWhitespace then advance; skipWs
  | none   => pure ()

private partial def readNameLoop (acc : String) : P String := do
  match ← peek? with
  | some c =>
    if c.isAlpha || c.isDigit || c = '-' || c = '_' || c = ':' || c = '.' then
      advance; readNameLoop (acc.push c)
    else pure acc
  | none => pure acc

private def readName : P String := do
  let n ← readNameLoop ""
  if n.isEmpty then throw "expected name" else return n

private partial def readQuotedLoop (q : Char) (acc : String) : P String := do
  match ← peek? with
  | some c =>
    if c = q then pure acc
    else do advance; readQuotedLoop q (acc.push c)
  | none => throw "unterminated quoted string"

private def readQuoted : P String := do
  let some q ← peek? | throw "expected quoted string"
  unless q = '"' || q = '\'' do throw s!"expected quote, got '{q}'"
  advance
  let s ← readQuotedLoop q ""
  expectCh q
  return s

private partial def readAttrs : P (Array (String × Lean.Json)) := do
  let mut attrs : Array (String × Lean.Json) := #[]
  skipWs
  let mut done := false
  while !done do
    match ← peek? with
    | none => done := true
    | some c =>
      if c = '>' || c = '/' then done := true
      else
        let name ← readName
        skipWs; expectCh '='; skipWs
        let val ← readQuoted
        attrs := attrs.push (name, Lean.Json.str val)
        skipWs
  return attrs

private partial def skipPrologEtc : P Unit := do
  skipWs
  if ← startsWith "<?" then
    while !(← startsWith "?>") do
      match ← peek? with | none => throw "unterminated <? ?>" | some _ => advance
    consume "?>"
    skipPrologEtc
  else if ← startsWith "<!--" then
    while !(← startsWith "-->") do
      match ← peek? with | none => throw "unterminated comment" | some _ => advance
    consume "-->"
    skipPrologEtc
  else if ← startsWith "<!" then
    while ((← peek?).map (· != '>')).getD false do advance
    advance
    skipPrologEtc

/-- One stack frame: an open element with its accumulated children. -/
private abbrev Frame := String × Array (String × Lean.Json) × Array Html

/-- Append `child` to the children-array of the top frame, or set it as
the document root if the stack is empty. -/
private def appendChildOrFinish (stack : Array Frame) (root? : Option Html) (child : Html)
    : Array Frame × Option Html :=
  if stack.isEmpty then (stack, some child)
  else
    let idx := stack.size - 1
    let (t, a, kids) := stack[idx]!
    (stack.set! idx (t, a, kids.push child), root?)

/-- Iterative XML parser using an explicit stack. Avoids `mutual` (whose
name resolution interacts badly with our private state struct) by
threading element opens/closes through a frame stack. Stops once the
root element closes. -/
partial def parseDoc : P Html := do
  skipPrologEtc
  skipWs
  let mut stack : Array Frame := #[]
  let mut root? : Option Html := none
  while root?.isNone do
    if ← startsWith "<!--" then
      consume "<!--"
      while !(← startsWith "-->") do
        match ← peek? with | none => throw "unterminated comment" | some _ => advance
      consume "-->"
    else if ← startsWith "</" then
      consume "</"
      let closeName ← readName
      skipWs
      expectCh '>'
      let some (tag, attrs, kids) := stack.back? | throw "stray close tag"
      stack := stack.pop
      if tag != closeName then throw s!"mismatched </{closeName}>, expected </{tag}>"
      let (stack', root'?) := appendChildOrFinish stack root? (Html.element tag attrs kids)
      stack := stack'
      root? := root'?
    else if ← startsWith "<" then
      expectCh '<'
      let tag ← readName
      let attrs ← readAttrs
      skipWs
      if ← startsWith "/>" then
        consume "/>"
        let (stack', root'?) := appendChildOrFinish stack root? (Html.element tag attrs #[])
        stack := stack'
        root? := root'?
      else
        expectCh '>'
        if tag = "style" then
          -- raw-text body — CSS isn't valid XML so don't recurse
          let mut body : String := ""
          let closeTag := s!"</{tag}>"
          let mut sawClose := false
          while !sawClose do
            if ← startsWith closeTag then sawClose := true
            else match ← peek? with
              | none => throw "unterminated <style>"
              | some c => body := body.push c; advance
          consume closeTag
          let el := Html.element tag attrs #[Html.text body]
          let (stack', root'?) := appendChildOrFinish stack root? el
          stack := stack'
          root? := root'?
        else
          stack := stack.push (tag, attrs, #[])
    else
      let mut text : String := ""
      let mut stopText := false
      while !stopText do
        match ← peek? with
        | none      => stopText := true
        | some c =>
          if c = '<' then stopText := true
          else text := text.push c; advance
      if !text.isEmpty then
        if stack.isEmpty then
          -- whitespace between prolog/root and end-of-file is harmless
          if text.all Char.isWhitespace then pure ()
          else throw "stray text outside root element"
        else
          let idx := stack.size - 1
          let (pt, pa, pk) := stack[idx]!
          stack := stack.set! idx (pt, pa, pk.push (Html.text text))
  match root? with
  | some h => return h
  | none   => throw "no root element parsed"

/-- Parse an SVG document string into a `Html` element tree. -/
def parse (input : String) : Except String Html :=
  let initSt : St := { src := input, pos := (⟨0⟩ : String.Pos.Raw) }
  match parseDoc.run initSt with
  | .ok h _      => .ok h
  | .error msg _ => .error msg

end SvgParser

/-- One figure attached to an atlas decl. Field names deliberately
    avoid the `title` / `index` / `caption` tokens reserved by the
    scoped `atlasFigureField` syntax below, since those would shadow
    the field-LHS in structure-literal initialization.

    `svgHtml` is the file contents pre-parsed into a `ProofWidgets.Html`
    element tree so lean.nvim's TUI can rasterize via libresvg. -/
structure Figure where
  filePath  : String
  titleStr  : Option String
  idx       : Option Nat
  captionStr: Option String
  svgHtml   : Html
  deriving Inhabited

/-- Per-commentary figure record. Multiple figures per decl are
    flattened into one block (one entry per `figure := by …` in the
    source). Keyed by `(targetKind, targetNum)` so resolution can
    happen after the commentary parses but before the target decl
    exists. -/
structure FigureBlock where
  targetKind : String
  targetNum  : String
  figure     : Figure
  deriving Inhabited

initialize atlasFigureExt :
    SimplePersistentEnvExtension FigureBlock (Array FigureBlock) ←
  registerSimplePersistentEnvExtension {
    name          := `Atlas.atlasFigureExt
    addEntryFn    := fun s e => s.push e
    addImportedFn := fun arr =>
      arr.foldl (init := (#[] : Array FigureBlock)) Array.append
    asyncMode     := .sync
  }

/-- Look up every figure block matching a `(kind, number)` key, ordered
    by the user-supplied `index` (figures without an index sort last,
    in source order). -/
def atlasFiguresFor (env : Environment) (kind number : String) : Array Figure :=
  let localBlocks := atlasFigureExt.getState env
  let imported : Array FigureBlock := Id.run do
    let mut acc : Array FigureBlock := #[]
    let mut i : Nat := 0
    let n := env.allImportedModuleNames.size
    while i < n do
      for fb in PersistentEnvExtension.getModuleEntries atlasFigureExt env i do
        acc := acc.push fb
      i := i + 1
    return acc
  let allBlocks := imported ++ localBlocks
  let matched := allBlocks.filterMap fun fb =>
    if fb.targetKind == kind && fb.targetNum == number then some fb.figure else none
  matched.qsort fun a b =>
    match a.idx, b.idx with
    | some i, some j => i < j
    | some _, none   => true
    | none,   some _ => false
    | none,   none   => false

/-! ## Field syntax: `figure := by file … title … index … caption …` -/

declare_syntax_cat atlasFigureField

scoped syntax (name := afFile)    "file"    str : atlasFigureField
scoped syntax (name := afTitle)   "title"   str : atlasFigureField
scoped syntax (name := afIndex)   "index"   num : atlasFigureField
scoped syntax (name := afCaption) "caption" str : atlasFigureField

/-- Parse a list of `atlasFigureField` syntax args, read the referenced
    file, parse its SVG into a `Html` tree, and produce a `Figure`.
    The `file` field is required; others optional. -/
def elabFigureFields (fields : Array Syntax) : CommandElabM Figure := do
  let mut fpOpt    : Option String := none
  let mut titleOpt : Option String := none
  let mut idxOpt   : Option Nat    := none
  let mut capOpt   : Option String := none
  for fld in fields do
    match fld with
    | `(atlasFigureField| file $s:str) =>
      fpOpt := some s.getString
    | `(atlasFigureField| title $s:str) =>
      titleOpt := some s.getString
    | `(atlasFigureField| index $n:num) =>
      idxOpt := some n.getNat
    | `(atlasFigureField| caption $s:str) =>
      capOpt := some s.getString
    | _ => throwErrorAt fld "atlas figure: unrecognized field"
  let some path := fpOpt |
    throwError "atlas figure: missing `file \"<path>\"` field — required"
  let svgStr ← liftM (IO.FS.readFile path : IO String)
  let svgHtml ← match SvgParser.parse svgStr with
    | .ok h => pure h
    | .error msg => throwError s!"atlas figure: failed to parse SVG at '{path}': {msg}"
  return { filePath := path, titleStr := titleOpt, idx := idxOpt,
           captionStr := capOpt, svgHtml := svgHtml }

/-! ## Html assembly for the figures section

Builds the figures slice of the InfoView panel: a heading row per
figure (title + index), the SVG itself (as parsed Html so lean.nvim
rasterizes via libresvg), and an optional italic caption. All wrapped
in a bordered container styled to match the refs panel. -/

private def styleAttr (s : String) : String × Lean.Json := ("style", Lean.Json.str s)

private def renderOneFigure (f : Figure) (n : Nat) : Html :=
  let titleText : String :=
    match f.titleStr, f.idx with
    | some t, some i => s!"Figure {i}: {t}"
    | some t, none   => t
    | none,   some i => s!"Figure {i}"
    | none,   none   => s!"Figure {n + 1}"
  let header := Html.element "div"
    #[styleAttr "font-weight: bold; margin-bottom: 0.25em;"]
    #[Html.text titleText]
  let svgWrap := Html.element "div"
    #[styleAttr "text-align: center; margin-bottom: 0.5em;"]
    #[f.svgHtml]
  let pieces : Array Html := match f.captionStr with
    | some c =>
      let cap := Html.element "div"
        #[styleAttr "font-size: 0.85em; color: #93a1a1; font-style: italic; margin-bottom: 0.5em;"]
        #[Html.text c]
      #[header, svgWrap, cap]
    | none => #[header, svgWrap]
  Html.element "div"
    #[styleAttr "margin-bottom: 1em;"] pieces

/-- Build the figures Html section for a decl. Returns `none` if the
    decl has no figures (caller decides whether to skip the section
    or render an empty state). -/
def figuresHtmlSection (figs : Array Figure) : Option Html :=
  if figs.isEmpty then none
  else
    let header := Html.element "h4"
      #[styleAttr "margin: 1em 0 0.5em 0;"]
      #[Html.text "Figures",
        Html.element "span"
          #[styleAttr "color: #888888; margin-left: 0.5em; font-weight: normal;"]
          #[Html.text s!"({figs.size})"]]
    let body := figs.mapIdx fun i f => renderOneFigure f i
    some <| Html.element "div"
      #[styleAttr "border-top: 1px solid #93a1a1; padding-top: 0.5em; margin-top: 0.5em;"]
      (#[header] ++ body)

end Atlas
