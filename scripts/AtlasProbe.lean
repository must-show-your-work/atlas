import Lean
import Atlas
import Geometry.Ch3.Prop.Pasch

open Lean

/-- Probe: load Atlas + Pasch only, then dump the atlas extension state.
    Isolates whether the issue is in `dumpdecls`'s module discovery or
    in the env extension itself. -/
def main : IO Unit := do
  initSearchPath (← findSysroot)
  let env ← importModules #[
    { module := `Atlas },
    { module := `Geometry.Ch3.Prop.Pasch }
  ] {}
  IO.println s!"=== ENV STATS ==="
  IO.println s!"total imported modules: {env.header.moduleNames.size}"
  IO.println s!"constants count: {env.constants.toList.length}"

  -- Find module idx for Pasch
  let pasch := `Geometry.Ch3.Prop.Pasch
  let pidx := env.getModuleIdxFor? `Geometry.Ch3.Prop.«Pasch's Postulate»
  IO.println s!"pasch decl module idx: {pidx}"

  let st := Atlas.atlasExt.getState env
  IO.println s!"byName entries: {st.byName.toList.length}"
  for (n, e) in st.byName.toList do
    IO.println s!"  {n} => {e.kind}/{e.number} \"{e.title}\""

  -- Inspect the raw state pair (local entries × state σ)
  let envExtState := Atlas.atlasExt.toEnvExtension.getState env
  IO.println s!"importedEntries.size: {envExtState.importedEntries.size}"
  let mut totalImported := 0
  for arr in envExtState.importedEntries do
    totalImported := totalImported + arr.size
  IO.println s!"total imported across all modules: {totalImported}"
  IO.println s!"state pair: local entries count = {envExtState.state.1.length}"
  IO.println s!"               state σ byName = {envExtState.state.2.byName.toList.length}"

  -- Check getModuleEntries directly for Pasch module
  IO.println s!"--- per-module entries ---"
  let mut i : Nat := 0
  while i < env.header.moduleNames.size do
    let modEntries := PersistentEnvExtension.getModuleEntries Atlas.atlasExt env i
    if modEntries.size > 0 then
      let modName := env.header.moduleNames[i]?
      IO.println s!"  module idx {i} ({modName}): {modEntries.size} entries"
    i := i + 1

  -- Test the workaround: build state from getModuleEntries directly.
  let workaroundState := Atlas.atlasStateFromImports env
  IO.println s!"=== WORKAROUND ==="
  IO.println s!"atlasStateFromImports byName entries: {workaroundState.byName.toList.length}"
  for (n, e) in workaroundState.byName.toList do
    IO.println s!"  {n} => {e.kind}/{e.number} \"{e.title}\""

  -- Test the actual public API used by DumpDecls.
  let paschName := `Geometry.Ch3.Prop.«Pasch's Postulate»
  match Atlas.atlasEntry? env paschName with
  | some e => IO.println s!"=== atlasEntry? PASS: {paschName} → {e.kind}/{e.number} \"{e.title}\""
  | none   => IO.println s!"=== atlasEntry? FAIL: {paschName} not found"
