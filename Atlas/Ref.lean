/-
Atlas/Ref.lean — term-position references: `ref kind N`, plus the
per-kind shortcuts (`proposition 3.4`, `corollary 1.2`, etc.).

`ref` is the canonical citation form — uniform across all atlas kinds
including the ones that can't have bare term keywords (`lemma`/`theorem`/
`axiom`, because reserving those tokens would break bare command parsing
for `lemma X : T := ...`). The per-kind shortcuts (`proposition N`,
etc.) are convenience wrappers for the kinds that DON'T conflict with
Lean's keyword set.

Lookup goes through `atlasLookupCascading` (see `Atlas/Basic.lean`):
when multiple decls share `(kind, number)` and the user's kind sits in
a tier with lower tiers, the lookup falls through and Lean's
overload-choice mechanism picks by type unification. Cascade is
*disabled* in `Atlas/Via.lean` (it interacts badly with vararg dispatch).

The `elabAtlasRefAux` helper is internal to this file. It can't be
trivially shared with `Via.lean`: Via's multi-match path does an
`isDefEq` loop over candidates against the surrounding args + expected
type, while Ref's emits a choice node and lets Lean's overload
resolution pick. These are genuinely different dispatch strategies.

The planned unification (see `docs/unified_ref_ux.md`) folds Via's
isDefEq machinery INTO Ref — making `ref kind N args` position-aware
(no-args → choice-node dispatch by expected type; with-args → isDefEq
over the args). When that lands, Ref absorbs Via rather than the
reverse. Until then, the two elabs stay parallel.

Depends on `Atlas/Basic.lean` (lookups), `Atlas/Number.lean`
(atlasNum + atlasNumToString).
-/

import Lean
import Atlas.Basic
import Atlas.Number

open Lean Elab Command

namespace Atlas

/-! ## Reference (term-position) elaboration -/

-- Helper used by every term-elab below. Looks up the (kind, number)
-- pair in the atlas reverse index and emits a constant reference with
-- fresh universe metavariables (the standard pattern for emitting a
-- reference to a polymorphic decl from elab code).
private def elabAtlasRefAux (kind : String) (num : Syntax)
    (expectedType? : Option Expr := none)
    : Elab.Term.TermElabM Expr := do
  let numStr : String ← match atlasNumToString? num with
    | some s => pure s
    | none   => throwError "atlas: malformed number reference"
  let env ← getEnv
  -- Tier cascade: when the user writes `<kind> N`, we collect every
  -- decl tagged `N` whose kind is in the same tier as `<kind>` OR a
  -- lower (more derivative) tier. The collected list is then wrapped
  -- in an overload-choice node; Lean's elaborator picks by unifying
  -- each branch's type against the expected type.
  --
  -- Tiers (in order, top-first):
  --   T1 results:       theorem, proposition, postulate, lemma,
  --                     axiom, exercise, alternate
  --   T2 derived:       corollary
  --   T3 commentary:    remark
  --
  -- So `theorem 3.3` searches theorems first, then corollaries of
  -- 3.3, then remarks of 3.3 — picking the first that unifies. The
  -- starting tier is whichever tier contains the kind the user wrote,
  -- so `corollary 3.3` does *not* fall back up to T1 (you asked
  -- for the corollary specifically); only T2→T3 cascade.
  --
  -- Definitions and axioms (the foundational kinds) don't cascade —
  -- their lookup stays exact. Querying `axiom B-1b` for a corollary
  -- would surprise.
  let ns := atlasLookupCascading env kind numStr
  match ns with
  | []  => throwError s!"atlas: no {kind} (or derivative tier) tagged `{numStr}` found"
  | [n] =>
    -- Singleton: don't thread the expected type — passing a metavariable
    -- expected type interferes with `have ⟨pat⟩ := …` destructuring,
    -- which needs the rhs to elaborate to a concrete type unaided.
    Lean.Elab.Term.elabTerm (mkIdent n) none
  | _  =>
    -- Multiple candidates — wrap in an overload-choice node so Lean's
    -- built-in elab tries each branch against `expectedType?`. Caveat:
    -- this only disambiguates when `expectedType?` is a concrete (or
    -- partially-concrete) type at the choice's elab site. In
    -- function-application position (`ref proposition 3.3 ⟨…⟩` is
    -- the function part), the expected type is `?α → ?β`-shaped and
    -- every candidate unifies trivially — so an outer `have x : T :=`
    -- annotation alone is not sufficient to dispatch. Those sites
    -- still need the «Title» form, or an out-of-line `have foo : T :=
    -- ref kind N args` extraction.
    let alts : Array Syntax := ns.toArray.map (fun n => (mkIdent n).raw)
    let choice : Syntax := mkNode choiceKind alts
    Lean.Elab.Term.elabTerm choice expectedType?

-- `:max` precedence so these can stand in function position of an
-- application: `proposition 3.4 heq` parses as `(proposition 3.4) heq`
-- instead of consuming `heq` as part of the elab-term syntax and bailing.
--
-- NOTE: we deliberately do *not* expose term-position keywords for
-- `theorem`/`lemma`/`axiom`, even though they are valid `atlas` kinds.
-- Registering those as term-position tokens would mark them as parser
-- keywords, which then breaks the *command*-position parsing of bare
-- `lemma X {b : T} : ...` / `axiom X : ...` (Lean's parser gets confused
-- between the term-position and command-position uses). For references
-- to those kinds, use the French-quoted title form: «My Title».
syntax:max (name := atlasRefProposition) "proposition" atlasNumLit : term
-- `alternate N.K` refers to an alternate proof of proposition N.K.
-- If multiple alternates share a number, the reference errors with
-- the list of titles; use «Title» to disambiguate.
syntax:max (name := atlasRefAlternate)   "alternate"   atlasNumLit : term
syntax:max (name := atlasRefCorollary)   "corollary"   atlasNumLit : term
syntax:max (name := atlasRefExercise)    "exercise"    atlasNumLit : term
syntax:max (name := atlasRefRemark)      "remark"      atlasNumLit : term
syntax:max (name := atlasRefPostulate)   "postulate"   atlasNumLit : term
syntax:max (name := atlasRefDefinition)  "definition"  atlasNumLit : term

-- Uniform `ref <kind> <num>` term-position form. Works for *every*
-- atlas kind including `lemma`/`axiom`/`theorem` (which can't have bare
-- term keywords because that would reserve those tokens and break bare
-- command parsing of `lemma X.Y {b}: T := body`). The kind is parsed as
-- `rawIdent` so any keyword-shaped name resolves.
syntax:max (name := atlasRef) "ref" rawIdent atlasNumLit : term

-- With-args form: `ref <kind> <num> args+`. Requires at least one arg
-- (the `+`) so it doesn't shadow the no-args `atlasRef` syntax.
--
-- Lean has two distinct mechanisms for `<func> <args>` elaboration that
-- diverge on autoParam handling:
--
--   1. No-parens (`f arg`): user args bind the FIRST explicit slot in
--      order, autoParam-typed binders included. Lets the caller override
--      an autoParam's default by supplying a positional value whose type
--      unifies with the autoParam slot's type.
--
--   2. Parens (`(f) arg`): Lean elaborates the function fully first,
--      which auto-fills autoParams via their tactic defaults; then the
--      user arg binds the first slot AFTER the autoParams.
--
-- Both patterns appear in giyf: some call sites supply a value meant for
-- the autoParam slot (Ex3 — `via exercise X ABC.symm` substitutes ABC);
-- others supply a value meant for a later non-autoParam slot, expecting
-- the autoParams to fill themselves (B4iii — `ref axiom B.4.i ⟨...⟩`
-- where the three `off`-hypothesis autoParams must auto-fill so the
-- conjunction slot receives `⟨...⟩`).
--
-- The term-elab below probes both mechanisms in order, type-directed:
--   (a) Try no-parens first. If the user arg's type fits the next slot
--       (which may be an autoParam), Lean elaborates successfully.
--   (b) On failure, restore state and try parens. autoParams auto-fill;
--       user arg binds the next non-autoParam slot.
-- No syntactic marker required at the call site; the types decide.
syntax:max (name := atlasRefApp)
  "ref" rawIdent atlasNumLit (ppSpace colGt term:max)+ : term

/-- Type-directed singleton dispatch: try no-parens (args may bind
autoParam slots whose type unifies with the user arg), fall back to
parens (autoParams auto-fill, args bind the first non-autoParam slot).

`errToSorry` is disabled during the probes — otherwise Lean would log
the failing arm's error and emit a `sorry`, which our `try` wouldn't
see (and the failing arm would silently "succeed" downstream). With
errToSorry off, the failing arm throws; the catch restores state and
tries the other arm. The outer caller's errToSorry context is what
governs the final attempt's error reporting. -/
private def elabRefAppSingleton (cand : Name) (args : Array (TSyntax `term))
    (expectedType? : Option Expr) : Lean.Elab.Term.TermElabM Lean.Expr := do
  let head := mkIdent cand
  let snap ← Lean.Elab.Term.saveState
  try
    Lean.Elab.Term.withoutErrToSorry do
      let appStx ← `($head $args*)
      Lean.Elab.Term.elabTerm appStx expectedType?
  catch _ =>
    snap.restore
    let appStx ← `(($head) $args*)
    Lean.Elab.Term.elabTerm appStx expectedType?

@[term_elab atlasRefApp]
def elabAtlasRefAppTerm : Lean.Elab.Term.TermElab := fun stx expectedType? =>
  match stx with
  | `(term| ref $k:ident $n:atlasNumLit $arg $args*) => do
      let kind := k.getId.toString
      let numStr ← match atlasNumToString? n with
        | some s => pure s
        | none   => throwError "atlas: malformed number reference"
      let env ← getEnv
      let ns := atlasLookupCascading env kind numStr
      let allArgs := #[arg] ++ args
      match ns with
      | []  =>
        throwError s!"atlas: no {kind} tagged `{numStr}` found"
      | [n] =>
        elabRefAppSingleton n allArgs expectedType?
      | _   =>
        -- Multi-match: try each candidate's type-directed dispatch in
        -- turn, keep the first that elaborates without throwing. If
        -- giyf needs more sophisticated multi-match resolution (e.g.,
        -- preferring candidates whose inferred type best-matches a
        -- concrete expected type), revisit.
        let mut lastError : Option Lean.MessageData := none
        for cand in ns do
          let snap ← Lean.Elab.Term.saveState
          try
            return (← elabRefAppSingleton cand allArgs expectedType?)
          catch ex =>
            lastError := some ex.toMessageData
            snap.restore
        match lastError with
        | some msg =>
          throwError m!"atlas: no candidate for {kind} `{numStr}` fits ({ns.length} tried):\n{msg}"
        | none =>
          throwError s!"atlas: no candidate for {kind} `{numStr}` fits"
  | _ => Lean.Elab.throwUnsupportedSyntax

-- Uniform `atlas <kind> <num>` term-position form. Works for *every*
-- atlas kind including `lemma`/`axiom`/`theorem` (which can't have bare
-- term keywords because that would reserve those tokens and break bare
-- command parsing of `lemma X.Y {b}: T := body`). The leading `"atlas"`
-- keyword disambiguates from the command form: command needs a string
-- title next, term form takes an `atlasNum` (none of whose variants
-- start with `"`, since the string-form is bracketed as `["..."]`).
-- so the rule fires in every position — including function-application slots
-- like `ref lemma 0.0.5 S`, where `ref lemma 0.0.5` is elaborated with no
-- expected type because it's the function part of an application. The `<=`
-- form gates rules to only fire when an expected type is provided directly,
-- which is too restrictive here. The `expectedType?` arg gives us the same
-- info when available, without the gating.

@[term_elab atlasRefProposition]
def elabAtlasRefPropositionTerm : Lean.Elab.Term.TermElab := fun stx expectedType? =>
  match stx with
  | `(term| proposition $n:atlasNumLit) => elabAtlasRefAux "proposition" n expectedType?
  | _ => Lean.Elab.throwUnsupportedSyntax

@[term_elab atlasRefAlternate]
def elabAtlasRefAlternateTerm : Lean.Elab.Term.TermElab := fun stx expectedType? =>
  match stx with
  | `(term| alternate $n:atlasNumLit) => elabAtlasRefAux "alternate" n expectedType?
  | _ => Lean.Elab.throwUnsupportedSyntax

@[term_elab atlasRefCorollary]
def elabAtlasRefCorollaryTerm : Lean.Elab.Term.TermElab := fun stx expectedType? =>
  match stx with
  | `(term| corollary $n:atlasNumLit) => elabAtlasRefAux "corollary" n expectedType?
  | _ => Lean.Elab.throwUnsupportedSyntax

@[term_elab atlasRefExercise]
def elabAtlasRefExerciseTerm : Lean.Elab.Term.TermElab := fun stx expectedType? =>
  match stx with
  | `(term| exercise $n:atlasNumLit) => elabAtlasRefAux "exercise" n expectedType?
  | _ => Lean.Elab.throwUnsupportedSyntax

@[term_elab atlasRefRemark]
def elabAtlasRefRemarkTerm : Lean.Elab.Term.TermElab := fun stx expectedType? =>
  match stx with
  | `(term| remark $n:atlasNumLit) => elabAtlasRefAux "remark" n expectedType?
  | _ => Lean.Elab.throwUnsupportedSyntax

@[term_elab atlasRefPostulate]
def elabAtlasRefPostulateTerm : Lean.Elab.Term.TermElab := fun stx expectedType? =>
  match stx with
  | `(term| postulate $n:atlasNumLit) => elabAtlasRefAux "postulate" n expectedType?
  | _ => Lean.Elab.throwUnsupportedSyntax

@[term_elab atlasRefDefinition]
def elabAtlasRefDefinitionTerm : Lean.Elab.Term.TermElab := fun stx expectedType? =>
  match stx with
  | `(term| definition $n:atlasNumLit) => elabAtlasRefAux "definition" n expectedType?
  | _ => Lean.Elab.throwUnsupportedSyntax

@[term_elab atlasRef]
def elabAtlasRefTerm : Lean.Elab.Term.TermElab := fun stx expectedType? =>
  match stx with
  | `(term| ref $k:ident $n:atlasNumLit) =>
      elabAtlasRefAux k.getId.toString n expectedType?
  | _ => Lean.Elab.throwUnsupportedSyntax

end Atlas
