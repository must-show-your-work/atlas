import Lake
open Lake DSL

-- Atlas: book-style theorem metadata for Lean 4.
--
-- Extracted from the `geometry-is-your-friend` repo
-- (`~/rivendell/geometry_is_your_friend`) as a standalone library.
-- See `Atlas.lean` for the macro/attribute machinery and `AtlasTest.lean`
-- for the smoke test exercising the full pipeline.

package "atlas" where
  version := v!"0.1.0"

-- The core library has no dependencies outside the Lean stdlib.
@[default_target]
lean_lib «Atlas» where
  srcDir := "."
  roots := #[`Atlas]

-- Smoke test. Depends on Mathlib only because one of the coexistence
-- tests imports `Mathlib.Tactic.Lemma` to demonstrate that bare-`lemma`
-- declarations parse correctly alongside `atlas lemma` commands. If we
-- ever want a Mathlib-free Atlas package, the test can be split out.
lean_lib «AtlasTest» where
  srcDir := "."
  roots := #[`AtlasTest]

-- Dev-only libs: fixture corpus + mereology demo. Gated behind
-- `lake -Kenv=dev` so downstream consumers who `require atlas` don't
-- see them in their import surface. To build/work on these locally:
--
--   lake -Kenv=dev build Corpus Mereology
--   LAKE_ENV=dev lake build Corpus Mereology   -- same thing
--
-- Without the flag, `lake build` only produces `Atlas` and `AtlasTest`.
-- This is the same gating idiom GIYF uses for `doc-gen4`.

meta if get_config? env = some "dev" then
lean_lib «Corpus» where
  srcDir := "."
  roots := #[`Corpus]

meta if get_config? env = some "dev" then
lean_lib «Mereology» where
  srcDir := "."
  roots := #[`Mereology]

-- Dependencies — Mathlib LAST so its transitive pins
-- (aesop/batteries/plausible/etc.) win the manifest resolution. Lake
-- warns about version skew otherwise.

-- figures: declarative-figure IR + multi-backend renderer. Atlas
-- depends on it for the `direct_rep` field's Construction-typed
-- argument and for the SVG output that drives the figure widget.
-- Sibling repo at ../figures (same workspace as shed).
require figures from "../figures"

-- SubVerso powers `dumptactics` (per-decl source highlight + tactic
-- occurrence extraction). Pinned to a recent main HEAD because the
-- reservoir-default revision (4abb984) shipped with duplicate
-- `root := Main` on several `lean_exe`s — Lake errors out trying to
-- build it. Upstream fixed this; we point at the post-fix commit.
require verso from git
  "https://github.com/leanprover/verso.git" @ "c004fc5a02584e08def4bfe5c0632d7e208efb58"

-- Mathlib LAST. Only for `Mathlib.Tactic.Lemma` in AtlasTest.lean
-- (and `Mathlib.Tactic.Linter.UnusedTacticExtension` in
-- `Atlas/Markers.lean`). See `TODO.md` "Atlas-core Mathlib decoupling"
-- — moving the directive to a separate `Atlas.MathlibCompat` shim
-- file would let the core be Mathlib-free.
require "leanprover-community" / "mathlib"

-- ---------------------------------------------------------------------
-- Graph / display tooling (checkpointed from the GIYF repo). These
-- executables hardcode `import Geometry`, which won't resolve in a
-- pure-Atlas package — they'll need adapting (parameterise over the
-- library under analysis) when Atlas truly migrates. See CHECKPOINT.md.
-- ---------------------------------------------------------------------

lean_exe "dumpdecls" where
  root := `scripts.DumpDecls

lean_exe "atlasprobe" where
  root := `scripts.AtlasProbe

lean_exe "dumpimports" where
  root := `scripts.DumpImports

lean_exe "dumptactics" where
  root := `scripts.DumpTactics
  -- SubVerso's `processCommands` runs `IO.getRandomBytes` via the
  -- interpreter; without this flag every module fails with a
  -- native-impl error.
  supportInterpreter := true
