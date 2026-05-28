import Lean
import Geometry

/-- Convert a module name `Geometry.Ch3.Prop.P4` to a path `Geometry/Ch3/Prop/P4.lean`. -/
def moduleToFile (m : String) : String :=
  m.replace "." "/" ++ ".lean"

/-- Escape for JSON. -/
def jsonEscape (s : String) : String :=
  s.replace "\\" "\\\\"
    |>.replace "\"" "\\\""
    |>.replace "\n" "\\n"

/-- Discover every `Geometry/**/*.lean` file and convert each to its module name.
    Used to populate the import list so dump includes work-in-progress files
    not transitively reached from `Geometry.lean` yet. -/
partial def discoverGeometryModules (root : String) : IO (Array Lean.Name) := do
  let mut out : Array Lean.Name := #[]
  let entries ← System.FilePath.readDir root
  for entry in entries do
    let path := entry.path
    if (← path.isDir) then
      out := out ++ (← discoverGeometryModules path.toString)
    else if path.extension == some "lean" then
      let rel := path.toString
      let cleaned := if rel.startsWith "./" then rel.drop 2 else rel
      let withoutExt := if cleaned.endsWith ".lean" then cleaned.dropEnd 5 else cleaned
      let dotted := withoutExt.replace "/" "."
      out := out.push dotted.toName
  return out

open Lean in
def main : IO Unit := do
  initSearchPath (← findSysroot)
  let discovered ← discoverGeometryModules "Geometry"
  let oleanRoot := ".lake/build/lib/lean"
  let buildable ← discovered.filterM fun n => do
    let p := s!"{oleanRoot}/{n.toString.replace "." "/"}.olean"
    return (← System.FilePath.pathExists p)
  let imports : Array Import :=
    (#[{ module := `Geometry }] : Array Import) ++
    buildable.map fun n => { module := n : Import }
  let env ← importModules imports {}
  -- For each `Geometry.*` module in the loaded environment, emit its direct
  -- (level-1) imports filtered to `Geometry.*`.
  let mut entries : Array String := #[]
  for i in [0 : env.allImportedModuleNames.size] do
    let modName := env.allImportedModuleNames[i]!
    let modStr := modName.toString
    if !modStr.startsWith "Geometry" then continue
    let imports := env.header.moduleData[i]!.imports
    let importedNames : Array String := imports.filterMap fun imp =>
      let s := imp.module.toString
      if s.startsWith "Geometry" then some s else none
    let importsJson :=
      "[" ++ (importedNames.toList.map (fun s => s!"\"{s}\"") |> String.intercalate ",") ++ "]"
    let entry := String.intercalate "," [
      s!"\"name\":\"{jsonEscape modStr}\"",
      s!"\"file\":\"{jsonEscape (moduleToFile modStr)}\"",
      s!"\"imports\":{importsJson}"
    ]
    entries := entries.push ("{" ++ entry ++ "}")
  let json := "[\n" ++ String.intercalate ",\n" entries.toList ++ "\n]"
  IO.FS.createDirAll "blueprint"
  IO.FS.writeFile "blueprint/modules.json" json
  IO.eprintln s!"Wrote {entries.size} modules to blueprint/modules.json"
