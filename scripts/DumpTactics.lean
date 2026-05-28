/-
Extract per-decl highlighted source HTML and tactic occurrences using
SubVerso. Mirrors `subverso-extract-mod`'s frontend setup (see
`.lake/packages/subverso/ExtractModule.lean`) but instead of dumping
the internal `Highlighted` JSON for downstream tools, walks the tree
directly to emit two artifacts:

  - `blueprint/highlighted.json` — `{ decl_name : html_string }`
    Each declaration's source rendered as HTML with token-kind CSS
    classes (`lean-kw`, `lean-const`, `lean-var`, …). Consumed by
    `scripts/export_graph.py` and shown in the inspector pane.

  - `blueprint/tactics.json` — `[{ decl, tactic, line }]`
    Each tactic occurrence (e.g. `intro`, `rcases`, `obvious`) inside
    a declaration's proof body, with the source line. Used by
    `tactic_hotspots.cypher` and similar diagnostic queries.

Per-module cost: subverso re-runs the elaborator from scratch, so
running this for the whole `Geometry/` tree takes minutes. That's the
trade-off for getting real syntactic info instead of regex tokenizing.
-/

import Lean
import Atlas
import SubVerso.Compat
import SubVerso.Examples.Env
import SubVerso.Module
import SubVerso.Highlighting

open Lean Elab Frontend
open Lean.Elab.Command hiding Context
open SubVerso
open SubVerso.Module
open SubVerso.Highlighting

/-- HTML-escape `&`, `<`, `>`, `"`. -/
def htmlEscape (s : String) : String :=
  s.replace "&" "&amp;"
    |>.replace "<" "&lt;"
    |>.replace ">" "&gt;"
    |>.replace "\"" "&quot;"

/-- JSON-escape control characters and quotes. -/
def jsonEscape (s : String) : String :=
  s.replace "\\" "\\\\"
    |>.replace "\"" "\\\""
    |>.replace "\n" "\\n"
    |>.replace "\r" "\\r"
    |>.replace "\t" "\\t"

/-- Map a SubVerso token kind to a CSS class for HTML highlighting.
    Keep these names stable — the corresponding CSS lives in
    `scripts/graph.html`. -/
def tokenClass : Token.Kind → String
  | .keyword ..        => "lean-kw"
  | .const _ _ _ true  => "lean-def"      -- definition site
  | .const ..          => "lean-const"    -- reference to a constant
  | .anonCtor ..       => "lean-ctor"
  | .var ..            => "lean-var"
  | .str _             => "lean-str"
  | .option ..         => "lean-opt"
  | .docComment        => "lean-doc"
  | .sort _            => "lean-sort"
  | .levelVar _        => "lean-lvl"
  | .levelOp _         => "lean-lvl"
  | .levelConst _      => "lean-lvl"
  | .moduleName _      => "lean-mod"
  | .withType _        => "lean-typed"
  | .unknown           => "lean-unk"

/-- Walk a `Highlighted` tree, emitting HTML. Tactic spans and
    info spans are flattened (we don't surface their goal/message
    annotations in the inline source view — they belong on a separate
    "proof state" widget that we don't have yet). -/
partial def renderHtml : Highlighted → String
  | .seq xs => xs.foldl (fun s hl => s ++ renderHtml hl) ""
  | .text s => htmlEscape s
  | .unparsed s => htmlEscape s
  | .point _ _ => ""
  | .span _ inner => renderHtml inner
  | .tactics _ _ _ inner => renderHtml inner
  | .token tok =>
    "<span class=\"" ++ tokenClass tok.kind ++ "\">"
      ++ htmlEscape tok.content ++ "</span>"

/-- Find the first `token` value inside a `Highlighted` subtree. Used
    to label a `.tactics` span with its leading token (the tactic
    name) for the tactic-occurrence index. -/
partial def firstTokenContent : Highlighted → Option String
  | .token tok => some tok.content
  | .seq xs => Id.run do
    for hl in xs do
      if let some s := firstTokenContent hl then
        return some s
    return none
  | .span _ inner => firstTokenContent inner
  | .tactics _ _ _ inner => firstTokenContent inner
  | _ => none

/-- Collect `(tactic_name, source_line)` pairs from a `Highlighted`
    tree. `posToLine` converts the SubVerso start position into a
    1-based source line. -/
partial def collectTactics
    (posToLine : Nat → Nat) : Highlighted → List (String × Nat)
  | .seq xs =>
    xs.foldl (init := []) fun acc hl => acc ++ collectTactics posToLine hl
  | .tactics _ startPos _ inner =>
    -- Tactic token contents already lack whitespace, so no trim needed.
    let here := match firstTokenContent inner with
      | some name => [(name, posToLine startPos)]
      | none => []
    here ++ collectTactics posToLine inner
  | .span _ inner => collectTactics posToLine inner
  | _ => []

/-- Discover every `Geometry/**/*.lean` file (relative to the project
    root) and convert each to its module name. Matches the discovery
    logic in `scripts/DumpDecls.lean`. -/
partial def discoverGeometryModules (root : String) : IO (Array Name) := do
  let mut out : Array Name := #[]
  let entries ← System.FilePath.readDir root
  for entry in entries do
    let path := entry.path
    if (← path.isDir) then
      out := out ++ (← discoverGeometryModules path.toString)
    else if path.extension == some "lean" then
      let rel := path.toString
      let cleaned := if rel.startsWith "./" then rel.drop 2 else rel
      let withoutExt :=
        if cleaned.endsWith ".lean" then cleaned.dropEnd 5 else cleaned
      let dotted := withoutExt.replace "/" "."
      out := out.push dotted.toName
  return out

/-- Per-decl entry produced by `processModule`. -/
structure DeclEntry where
  name    : String
  html    : String
  tactics : List (String × Nat)

/-- Cache format version. Bump whenever the HTML/JSON schema or the
    `tokenClass` mapping changes — old caches with a different version
    are treated as stale and regenerated. -/
def cacheVersion : String := "v1"

/-- Per-module cache directory. One file per module; contains the
    pre-formatted JSON entry fragments (matches the master file's
    on-disk format so loading is just a concatenation). -/
def cacheDir : System.FilePath := ⟨"blueprint/highlighted-cache"⟩

def cacheFileFor (mod : Name) : System.FilePath :=
  cacheDir / (mod.toString ++ ".cache")

/-- Cache file layout:

    ```
    __VERSION__
    v1
    __HTML__
      "decl.name":"<span>…</span>"
      "decl.name":"<span>…</span>"
    __TACTICS__
      {"decl":"…","tactic":"…","line":N}
    ```

    The lines after each section header are pre-formatted entries
    ready to drop straight into the master JSON arrays. No JSON
    parsing required on the load path — keeps the rebuild loop fast.
-/
unsafe def loadCache (cf : System.FilePath)
    : IO (Option (Array String × Array String)) := do
  let contents ← IO.FS.readFile cf
  let lines := contents.splitOn "\n"
  let mut html    : Array String := #[]
  let mut tactics : Array String := #[]
  -- `section` is a Lean keyword; pick a non-reserved name.
  let mut sect : String := ""
  let mut sawVersion : Bool := false
  let mut versionOk : Bool := false
  for line in lines do
    if line == "__VERSION__" then sect := "version"
    else if line == "__HTML__" then sect := "html"
    else if line == "__TACTICS__" then sect := "tactics"
    else if sect == "version" && !sawVersion then
      sawVersion := true
      versionOk := line == cacheVersion
    else if sect == "html" && line.startsWith "  " then
      html := html.push line
    else if sect == "tactics" && line.startsWith "  " then
      tactics := tactics.push line
  if !versionOk then return none
  return some (html, tactics)

unsafe def writeCache (cf : System.FilePath)
    (html tactics : Array String) : IO Unit := do
  IO.FS.createDirAll cacheDir
  let body :=
    "__VERSION__\n" ++ cacheVersion ++ "\n" ++
    "__HTML__\n" ++ String.intercalate "\n" html.toList ++ "\n" ++
    "__TACTICS__\n" ++ String.intercalate "\n" tactics.toList ++ "\n"
  IO.FS.writeFile cf body

/-- Returns `true` if `cf` exists and is strictly newer than `src`.
    Falls back to `false` on any metadata error (treat as stale). -/
unsafe def cacheUpToDate (cf src : System.FilePath) : IO Bool := do
  try
    if !(← cf.pathExists) then return false
    let srcMeta   ← src.metadata
    let cacheMeta ← cf.metadata
    return cacheMeta.modified > srcMeta.modified
  catch _ => return false

/-- Run SubVerso's frontend pipeline on `modName` (loaded from
    `srcPath`), walk the resulting `Highlighted` items, and return one
    `DeclEntry` per declaration name defined in the module. Returns
    `#[]` on failure (so a single broken module doesn't abort the
    whole dump). The source path is passed in so `main` can use it
    for the mtime cache check. -/
unsafe def processModuleAt (modName : Name) (srcPath : System.FilePath)
    : IO (Array DeclEntry) := do
  try
    let contents ← IO.FS.readFile srcPath
    let fm := FileMap.ofString contents
    let ictx := Parser.mkInputContext contents srcPath.toString
    let (headerStx, parserState, msgs) ← Parser.parseHeader ictx
    let imports := headerToImports headerStx
    let isModule := Compat.isModule headerStx
    let env ← Compat.importModules imports {} (isModule := isModule) (asServer := true)
    -- Fully-qualified: opening `SubVerso.Highlighting` also pulls in
    -- a `Highlighting.Context`, so plain `Context` is ambiguous here.
    let pctx : Lean.Elab.Frontend.Context := { inputCtx := ictx }
    let commandState : Command.State :=
      { env, maxRecDepth := defaultMaxRecDepth, messages := msgs }
    let scopes :=
      let sc := commandState.scopes[0]!
      { sc with opts := sc.opts.setBool `pp.tagAppFns true } :: commandState.scopes.tail!
    let commandState := { commandState with scopes }
    let cmdPos := parserState.pos
    let cmdSt ← IO.mkRef { commandState, parserState, cmdPos }
    let res ← Compat.Frontend.processCommands headerStx pctx cmdSt
    let res := res.updateLeading contents
    let hls ← (Frontend.runCommandElabM <|
                  liftTermElabM <|
                  Highlighting.highlightFrontendResult res (suppressNamespaces := []))
                 pctx cmdSt
    -- Filter scope = atlas tagging (same constraint as `DumpDecls.lean`).
    --
    -- We can't use `hl.definedNames` because subverso doesn't mark
    -- macro-emitted decl identifiers as definition sites — the atlas
    -- command's expansion creates a synthetic-position ident for the
    -- title, and `isDefinition` rejects those. Instead, query the
    -- post-elaboration env for every atlas-tagged decl declared in
    -- THIS module and grab its line range. We then build one
    -- `DeclEntry` per atlas decl with html = (the full module HTML —
    -- subverso renders per-command and we concatenate) and tactics
    -- filtered to the decl's line range.
    let finalSt ← cmdSt.get
    let finalEnv := finalSt.commandState.env
    let importedAtlasSt := Atlas.atlasStateFromImports finalEnv
    let liveAtlasSt     := Atlas.atlasExt.getState finalEnv
    let posToLine (p : Nat) : Nat := (fm.toPosition ⟨p⟩).line
    -- Atlas decls added by commands in THIS module = (live state) − (imported state).
    -- `liveAtlasSt` is the combined live+imported view; `importedAtlasSt`
    -- is what the imports contributed. The difference is what THIS
    -- module's commands added.
    let atlasNamesHere : Array Lean.Name :=
      liveAtlasSt.byName.toArray.filterMap fun (n, _) =>
        if importedAtlasSt.byName.contains n then none else some n
    -- Run inside the elaborator context so `findDeclarationRanges?` works.
    let coreCtx : Lean.Core.Context := { fileName := srcPath.toString, fileMap := fm }
    let coreState : Lean.Core.State := { env := finalEnv }
    let collectRanges : Lean.CoreM (Array (Lean.Name × Nat × Nat)) := do
      let mut out : Array (Lean.Name × Nat × Nat) := #[]
      for n in atlasNamesHere do
        if let some r ← Lean.findDeclarationRanges? n then
          out := out.push (n, r.range.pos.line, r.range.endPos.line)
      return out
    let (nameRanges, _) ← collectRanges.toIO coreCtx coreState
    -- Pre-render the full module's HTML and tactic list once.
    let allHtml := String.intercalate "" (hls.map renderHtml).toList
    let allTactics : Array (String × Nat) :=
      hls.foldl (init := #[]) fun acc hl => acc ++ collectTactics posToLine hl
    -- Emit one entry per atlas decl, slicing tactics by line range.
    let mut out : Array DeclEntry := #[]
    for (name, lo, hi) in nameRanges do
      let tactics := (allTactics.filter (fun (_, ln) => lo ≤ ln && ln ≤ hi)).toList
      out := out.push { name := name.toString, html := allHtml, tactics }
    return out
  catch e =>
    IO.eprintln s!"[dumptactics] {modName}: {e}"
    return #[]

/-- Process a single named module and write its per-module cache file.
    Idempotent: skips work if the cache is already newer than the
    source. Designed to be called from the orchestrator
    (`scripts/run_dumptactics.py`), one subprocess per module, so RAM
    from each module's Mathlib import is released between calls. -/
unsafe def runOne (modString : String) : IO Unit := do
  initSearchPath (← findSysroot)
  enableInitializersExecution
  let mod := modString.toName
  let sp ← Compat.initSrcSearchPath
  let sp : SearchPath :=
    (sp : List System.FilePath) ++ [("." : System.FilePath)]
  match (← sp.findModuleWithExt "lean" mod) with
  | none =>
    IO.eprintln s!"[dumptactics] {mod}: source not found"
  | some srcPath =>
    let cf := cacheFileFor mod
    if (← cacheUpToDate cf srcPath) then
      IO.eprintln s!"[dumptactics] {mod}: cache up-to-date, skipping"
      return
    IO.eprintln s!"[dumptactics] {mod}: processing"
    let pairs ← processModuleAt mod srcPath
    if pairs.isEmpty then
      IO.eprintln s!"[dumptactics] {mod}: no decls extracted; cache NOT written"
      return
    let mut moduleHtml    : Array String := #[]
    let mut moduleTactics : Array String := #[]
    for entry in pairs do
      let nameEsc := jsonEscape entry.name
      let htmlEsc := jsonEscape entry.html
      moduleHtml := moduleHtml.push <|
        "  \"" ++ nameEsc ++ "\":\"" ++ htmlEsc ++ "\""
      for (tac, line) in entry.tactics do
        let tacEsc := jsonEscape tac
        moduleTactics := moduleTactics.push <|
          "  {\"decl\":\"" ++ nameEsc ++
          "\",\"tactic\":\"" ++ tacEsc ++
          "\",\"line\":" ++ toString line ++ "}"
    writeCache cf moduleHtml moduleTactics
    IO.eprintln s!"[dumptactics] {mod}: wrote {moduleHtml.size} decls, {moduleTactics.size} tactics"

unsafe def runAll : IO Unit := do
  initSearchPath (← findSysroot)
  enableInitializersExecution
  let modules ← discoverGeometryModules "Geometry"
  IO.eprintln s!"[dumptactics] discovered {modules.size} modules"

  let sp ← Compat.initSrcSearchPath
  let sp : SearchPath :=
    (sp : List System.FilePath) ++ [("." : System.FilePath)]

  let mut htmlEntries : Array String := #[]
  let mut tacticEntries : Array String := #[]
  let mut idx := 0
  let mut cachedCount := 0
  let mut processedCount := 0

  for mod in modules do
    idx := idx + 1
    -- Look up the source file. If it's not on the search path we skip
    -- with a warning; otherwise fall through to the cache check.
    match (← sp.findModuleWithExt "lean" mod) with
    | none =>
      IO.eprintln s!"[dumptactics] ({idx}/{modules.size}) {mod} — no source found, skipping"
    | some srcPath =>
      let cf := cacheFileFor mod
      -- Try the cache first. `reused?` is `true` iff we successfully
      -- loaded a fresh, version-matched cache; otherwise we fall
      -- through to re-elaboration.
      let mut reused? : Bool := false
      if (← cacheUpToDate cf srcPath) then
        match (← loadCache cf) with
        | some (h, t) =>
          IO.eprintln s!"[dumptactics] ({idx}/{modules.size}) {mod} (cached)"
          htmlEntries := htmlEntries ++ h
          tacticEntries := tacticEntries ++ t
          cachedCount := cachedCount + 1
          reused? := true
        | none =>
          IO.eprintln s!"[dumptactics] ({idx}/{modules.size}) {mod} (cache version stale)"
      else
        IO.eprintln s!"[dumptactics] ({idx}/{modules.size}) {mod}"

      if !reused? then
        let pairs ← processModuleAt mod srcPath
        processedCount := processedCount + 1
        let mut moduleHtml    : Array String := #[]
        let mut moduleTactics : Array String := #[]
        for entry in pairs do
          let nameEsc := jsonEscape entry.name
          let htmlEsc := jsonEscape entry.html
          moduleHtml := moduleHtml.push <|
            "  \"" ++ nameEsc ++ "\":\"" ++ htmlEsc ++ "\""
          for (tac, line) in entry.tactics do
            let tacEsc := jsonEscape tac
            moduleTactics := moduleTactics.push <|
              "  {\"decl\":\"" ++ nameEsc ++
              "\",\"tactic\":\"" ++ tacEsc ++
              "\",\"line\":" ++ toString line ++ "}"
        -- Only persist the cache if we actually got entries. An empty
        -- result usually means `processModuleAt` threw and bailed; if
        -- we wrote an empty cache here, the mtime check would mark it
        -- as up-to-date and we'd never retry the failing module.
        if pairs.isEmpty then
          IO.eprintln s!"[dumptactics]   ↳ no decls extracted from {mod}; cache NOT written"
        else
          writeCache cf moduleHtml moduleTactics
        htmlEntries := htmlEntries ++ moduleHtml
        tacticEntries := tacticEntries ++ moduleTactics

      -- Write the master files after every module so a Ctrl-C / OOM
      -- never throws away the progress we already made. Cheap because
      -- htmlEntries is just an array of pre-formatted JSON fragments.
      let htmlJson :=
        "{\n" ++ String.intercalate ",\n" htmlEntries.toList ++ "\n}\n"
      IO.FS.writeFile "blueprint/highlighted.json" htmlJson
      let tacticsJson :=
        "[\n" ++ String.intercalate ",\n" tacticEntries.toList ++ "\n]\n"
      IO.FS.writeFile "blueprint/tactics.json" tacticsJson

  IO.FS.createDirAll "blueprint"
  let htmlJson :=
    "{\n" ++ String.intercalate ",\n" htmlEntries.toList ++ "\n}\n"
  IO.FS.writeFile "blueprint/highlighted.json" htmlJson
  let tacticsJson :=
    "[\n" ++ String.intercalate ",\n" tacticEntries.toList ++ "\n]\n"
  IO.FS.writeFile "blueprint/tactics.json" tacticsJson
  IO.eprintln s!"[dumptactics] wrote {htmlEntries.size} highlighted decls → blueprint/highlighted.json"
  IO.eprintln s!"[dumptactics] wrote {tacticEntries.size} tactic occurrences → blueprint/tactics.json"
  IO.eprintln s!"[dumptactics] {cachedCount} from cache, {processedCount} re-elaborated"

/-- Entry point.
    - `lake exe dumptactics MODULE` — process one module, write its
      cache, exit. Designed for `scripts/run_dumptactics.py` so each
      module gets its own process (RAM released between modules).
    - `lake exe dumptactics` — legacy in-process loop over every
      module. Still useful for one-shot debugging but tends to OOM on
      heavy umbrella modules. -/
unsafe def main (args : List String) : IO Unit := do
  match args with
  | [mod] => runOne mod
  | [] => runAll
  | _ =>
    IO.eprintln "usage: dumptactics [MODULE_NAME]"
    IO.eprintln "  no arg  → process all modules in-process (legacy; OOM-prone)"
    IO.eprintln "  one arg → process just that module and exit"
