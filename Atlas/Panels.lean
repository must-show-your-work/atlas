import Lean

/-
Atlas/Panels.lean — `with_atlas_panels` tactic syntax token.

Extracted from `Atlas/Refs.lean` so `Atlas/Command.lean` can reference
the syntax token in its `atlas <kind> <num> "Title" := by ...`
expansion without taking on Refs's ProofWidgets dependency.

The token is *parsed* here; the *elaboration* (which builds the
InfoView Html and saves the panel widget info) lives in
`Atlas/Refs.lean`. Splitting parsing from elaboration is the standard
Lean trick when one file's elab pulls in a heavy dependency that
another file (which only needs to emit the syntax) shouldn't carry.

Auto-injected by the atlas-decl macro in `Atlas/Command.lean` for
every tactic-mode `atlas <kind> <num> ... := by ...` body so the
panel appears on every atlas proof without the author opting in.
-/

namespace Atlas

/-- `with_atlas_panels <kind> <num> <tacticSeq>` — wraps a proof in
the per-decl InfoView panels (atlas-references panel + figures panel).
Elaboration lives in `Atlas/Refs.lean`. -/
syntax (name := withAtlasPanels)
  "with_atlas_panels" str str tacticSeq : tactic

end Atlas
