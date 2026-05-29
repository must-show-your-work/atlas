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
-- Why a separate syntax + macro_rules instead of folding args into
-- `atlasRef`'s term-elab: Lean's app elab handles autoParam binders
-- correctly only when the function head is a CUSTOM SYNTAX KIND in
-- function-application position. In that case `elabAppFn`
-- (`Lean/Elab/App.lean:1947-1965`) does two steps: (A) `elabTerm f none
-- catchPostpone` elaborates the head alone — which auto-fills
-- autoParams since the user-arg queue is empty at that point; (B)
-- `elabAppLVals` applies the user args to the partial application,
-- which now only has the non-autoParam binders remaining.
--
-- If we instead built `(const) args*` ourselves in a term-elab and
-- handed it to `elabTerm`, Lean would route through `elabAppFnId` →
-- `elabAppFnResolutions` → `elabAppLVals` (line 1787) WITHOUT the
-- separate elab-head-alone step, and the user args would bind to the
-- autoParam slots (failing on type mismatch). The macro-rules expansion
-- to `(ref k n) $args*` keeps the function head as a custom-syntax
-- form, so the fallthrough path fires and autoParams get auto-filled
-- before user args bind.
syntax:max (name := atlasRefApp)
  "ref" rawIdent atlasNumLit (ppSpace colGt term:max)+ : term

macro_rules
  | `(ref $k:ident $n:atlasNumLit $arg $args*) =>
      `((ref $k $n) $arg $args*)

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
