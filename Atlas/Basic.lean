/-
Atlas/Basic.lean — types, env extension, attribute, kind tiers.

Foundation imported by every other Atlas module. Holds the persistent
state (`atlasExt`), per-decl row schema (`AtlasEntry` / `AtlasRow`), the
forward+reverse-lookup `AtlasState`, the `@[atlas k n t]` attribute that
populates the state at decl time, and the kind-tier table consulted by
the term-position `ref` cascade in `Atlas/Ref.lean`.

No syntax/elab here — those live in the per-feature modules.
-/

import Lean

open Lean Elab Command

namespace Atlas

/-! ## State -/

/-- Per-decl atlas metadata. -/
structure AtlasEntry where
  kind   : String
  number : String
  title  : String
  deriving Inhabited, Repr, BEq

/-- The persistent representation of one entry. -/
abbrev AtlasRow := Name × String × String × String

/-- In-memory state: per-decl entries plus the two reverse indexes used
    by elab-term lookups.

    `byKindNumber` stores a *list* of names per (kind, number) key
    because multi-part propositions and alternate proofs legitimately
    share keys. The elab term `proposition 3.4` consults this list:
      • 0 entries → error "no decl tagged"
      • 1 entry  → resolves unambiguously
      • 2+       → error with the list of titles, prompting the user
                   to disambiguate via the «Title» form. -/
structure AtlasState where
  byName       : NameMap AtlasEntry           := {}
  byKindNumber : Std.HashMap String (List Name) := {}  -- key: `"{kind}/{number}"`
  byTitle      : Std.HashMap String Name      := {}
  deriving Inhabited

private def insertEntry (s : AtlasState) (row : AtlasRow) : AtlasState :=
  let (n, k, num, t) := row
  let entry : AtlasEntry := { kind := k, number := num, title := t }
  let key := k ++ "/" ++ num
  let existing := s.byKindNumber.get? key |>.getD []
  { byName       := s.byName.insert n entry
    byKindNumber := s.byKindNumber.insert key (n :: existing)
    byTitle      := s.byTitle.insert t n }

initialize atlasExt : SimplePersistentEnvExtension AtlasRow AtlasState ←
  registerSimplePersistentEnvExtension {
    name          := `Atlas.atlasExt
    addEntryFn    := insertEntry
    addImportedFn := fun arr =>
      arr.foldl (init := ({} : AtlasState)) fun s sub =>
        sub.foldl insertEntry s
  }

/-- Walk `getModuleEntries` for every imported module and fold the
    results back into a fresh `AtlasState`. Workaround for the case
    where the in-memory `getState` doesn't seem to honour
    `addImportedFn` reliably across module boundaries — useful for
    consumers like `scripts/DumpDecls.lean` that need the merged
    forward-lookup map. -/
def atlasStateFromImports (env : Environment) : AtlasState := Id.run do
  let mut st : AtlasState := {}
  let mut i : Nat := 0
  let n := env.allImportedModuleNames.size
  while i < n do
    let entries := PersistentEnvExtension.getModuleEntries atlasExt env i
    for row in entries do
      st := insertEntry st row
    i := i + 1
  return st

/-! ## Helper for the common-shape array-state extension -/

/-- Register a `SimplePersistentEnvExtension` whose state is an
`Array α`, entries are `push`ed, and imported per-module arrays are
flattened with `Array.append`. `asyncMode := .sync` so writes from
inside tactic-elab survive the elaboration boundary (every Atlas marker
extension writes from tactics). Used by `Atlas/Markers.lean`,
`Atlas/Commentary.lean`, and `Atlas/Figure.lean`. -/
def registerArrayExt {α : Type} (name : Name) :
    IO (SimplePersistentEnvExtension α (Array α)) :=
  registerSimplePersistentEnvExtension {
    name          := name
    addEntryFn    := fun s e => s.push e
    addImportedFn := fun arr => arr.foldl (init := (#[] : Array α)) Array.append
    asyncMode     := .sync
  }

/-! ## Query helpers (read by `DumpDecls.lean` and the elab rules below) -/

def atlasEntry? (env : Environment) (n : Name) : Option AtlasEntry :=
  match (atlasExt.getState env).byName.find? n with
  | some e => some e
  | none   => (atlasStateFromImports env).byName.find? n

/-- Return every name tagged with `(kind, number)`. May be empty (no
    match) or contain more than one entry (multi-part propositions,
    alternate proofs, etc.). Callers decide how to handle ambiguity. -/
def atlasLookupByNumber (env : Environment) (kind number : String) : List Name :=
  (atlasExt.getState env).byKindNumber.get? (kind ++ "/" ++ number) |>.getD []

def atlasLookupByTitle (env : Environment) (title : String) : Option Name :=
  (atlasExt.getState env).byTitle.get? title

/-- Kind-tier table — used by `atlasLookupCascading`. A reference to a
    kind in some tier T cascades through T and every tier below it,
    collecting decls tagged with the requested number. The choice-
    resolver downstream picks by type unification.

    Kinds *not* listed in any tier are looked up *exactly* — they
    don't cascade and they don't get cascaded into. That's the right
    default for kinds where a request is intentional and specific:
    `alternate K` means "I want the alternate proof of K, not K
    itself", `definition K` means "the definition, not a result".

    Vocabulary covers most book-math kind names. If a project needs
    a kind not listed here, add it to whichever tier matches its
    role; the cascade is purely structural so adding entries is
    cheap. Conjecture/hypothesis are deliberately omitted — they
    name *unproven* things and don't fit the "result" or "commentary"
    framing; add them later if a use case appears. -/
def kindTiers : List (List String) :=
  [ -- T1: main results — what a reader cites as "the theorem"
    [ "theorem", "proposition", "postulate", "lemma", "axiom"
    , "exercise", "law", "principle", "fact", "scholium" ]
    -- T2: derivative — strict consequences of T1 (or each other)
  , [ "corollary", "consequence", "claim" ]
    -- T3: commentary — prose that doesn't carry the proof but
    -- clarifies or illustrates it
  , [ "remark", "note", "observation", "example", "discussion" ]
  ]

/-- Cascading lookup. Given a starting `kind` and `number`, find the
    tier containing `kind`, then collect every decl tagged `number`
    whose kind is in that tier or any tier below. Returns the names
    flat-in-tier-order. Kinds outside the tier table are exact-lookup
    only. -/
def atlasLookupCascading (env : Environment) (kind number : String) : List Name :=
  -- Find the starting tier (the one that contains `kind`). If `kind`
  -- isn't in any tier, the lookup stays exact — no cascade.
  let rec dropUntil : List (List String) → List (List String)
    | []         => []
    | t :: rest  => if t.contains kind then t :: rest else dropUntil rest
  let tiers := dropUntil kindTiers
  if tiers.isEmpty then
    atlasLookupByNumber env kind number
  else
    -- Search current + all lower tiers, in order. Within the starting
    -- tier, the user's requested kind goes first so it gets first
    -- crack at unification.
    let preferredFirst : List String := tiers.head!.filter (· != kind) |>.cons kind
    let allKinds : List String := preferredFirst ++ (tiers.tail!.foldl (· ++ ·) [])
    allKinds.foldl (init := []) fun acc k =>
      acc ++ atlasLookupByNumber env k number

/-! ## Attribute -/

syntax (name := atlasAttr) "atlas" str str str : attr

initialize registerBuiltinAttribute {
  name  := `atlasAttr
  descr := "tag a declaration with atlas metadata (kind, number, title)"
  add   := fun decl stx _attrKind => do
    let kindStr  ← match stx[1].isStrLit? with
      | some s => pure s
      | none   => throwError "atlas: expected string literal for `kind`"
    let numStr   ← match stx[2].isStrLit? with
      | some s => pure s
      | none   => throwError "atlas: expected string literal for `number`"
    let titleStr ← match stx[3].isStrLit? with
      | some s => pure s
      | none   => throwError "atlas: expected string literal for `title`"
    if titleStr.isEmpty then
      throwError "atlas: `title` cannot be empty"
    let env := (← getEnv)
    let st  := atlasExt.getState env
    -- No (kind, number) duplicate check: multi-part propositions
    -- (P1.i, P1.ii sharing 3.1), alternate proofs, and theory lemmas
    -- with empty numbers all legitimately share keys. Title
    -- uniqueness is what catches real conflicts.
    --
    -- The elab terms (`proposition 3.4`, `alternate 3.4`, …) error
    -- on ambiguous lookup — they refuse to silently pick one. The
    -- user disambiguates via the `«Title»` form.
    if let some existing := st.byTitle.get? titleStr then
      throwError s!"atlas: duplicate title \"{titleStr}\" — already on `{existing}`"
    setEnv <| atlasExt.addEntry env (decl, kindStr, numStr, titleStr)
}
end Atlas
