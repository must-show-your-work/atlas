/-
Atlas/Via.lean — vararg-capturing reference: `via kind N args*`.

Used when `(kind, num)` resolves to multiple atlas decls and we need
type-directed dispatch on the *application*. Lean's `elabAppFn` can't
disambiguate a choice node in function-application position (it only
recognises `choiceKind` syntactically before macro expansion of
`stx[0]`, and our `ref` is a custom kind that fails that check).

Capturing args ourselves lets us elaborate each candidate against the
full application + the surrounding `expectedType?`, accept by
`isDefEq`, and reject candidates whose implicits remain
metavariables after `synthesizeSyntheticMVarsNoPostponing`.

Cascade is DISABLED here (`atlasLookupByNumber`, exact-kind only) —
`via proposition 3.3` is the user being explicit, and pulling in
adjacent kinds (`corollary 3.3`, etc.) creates spurious type-equivalent
candidates that defeat dispatch.

Depends on `Atlas/Basic.lean` (lookups), `Atlas/Number.lean`
(`atlasNumLit` parser + `atlasNumToString?` extraction).
-/

import Lean
import Atlas.Basic
import Atlas.Number
import Atlas.Ref  -- only so `ref` syntax is already in scope when `via` is opened together

open Lean Elab Command

namespace Atlas


-- Vararg-capturing variant: `via kind N args*` parses as one unit (the
-- args are consumed into the parse tree, not left for `App`). Used when
-- the kind+num resolves to *multiple* atlas decls and we need
-- type-directed dispatch on the application — which Lean's `elabAppFn`
-- can't do for our custom `ref` (it only dispatches choices that are
-- syntactically `choiceKind` *before* macro expansion of `stx[0]`).
-- With args captured, we try each candidate and pick the one that fits.
--
-- Reads naturally at call sites:
-- `have h : T := via proposition 3.3 ⟨ABC, ACD⟩` — "h, of type T, *via*
-- proposition 3.3 applied to these args".
--
-- Backward-compat note: `ref kind N` (no varargs) stays the canonical
-- form when the lookup is unambiguous; reserve `via kind N args*` for
-- paired-decl sites where dispatch is needed. The two keywords keep
-- the greedy-vararg issue contained: `subset_inter ref lemma 2.0.4 ref
-- lemma 2.0.14` still parses with sibling refs (the old way), and only
-- sites that opt in to `via` accept trailing args.
syntax:max (name := atlasVia) "via" rawIdent atlasNumLit (ppSpace colGt term:max)+ : term
-- An `@`-explicit variant of `ref` was attempted (`eref`, also `@ref`).
-- Neither composes cleanly with Lean's built-in `@`: that lives at
-- the syntactic level and gates which `TermElab` runs, while our
-- elab_rule resolves and elaborates the constant directly, bypassing
-- the explicit-mode flag. For positional-implicits call sites, use
-- `@«Title»` form (Lean handles French-quoted idents natively after `@`).


-- Vararg-capturing `apply kind N args*` elab. Used when the (kind, num)
-- key resolves to multiple atlas decls and we need type-directed
-- dispatch on the application. Lean's `elabAppFn` can't disambiguate a
-- choice in function-position because it doesn't propagate return type
-- to the function elab; capturing args ourselves lets us try each
-- candidate against the full application + expected type.
@[term_elab atlasVia]
def elabAtlasViaTerm : Lean.Elab.Term.TermElab := fun stx expectedType? => do
  match stx with
  | `(term| via $k:ident $n:atlasNumLit $args*) => do
      let kind := k.getId.toString
      let numStr ← match atlasNumToString? n with
        | some s => pure s
        | none   => throwError "atlas: malformed number reference"
      let env ← getEnv
      -- Use *exact* (non-cascading) lookup for `apply`. The cascade
      -- (T1 → T2 → T3) is the right default for the loose-typing
      -- `ref kind N` form — "I want the result-tier thing at N, don't
      -- care if it's labeled `theorem` or `proposition`". But for
      -- `apply kind N args*`, the user is explicit about which kind
      -- they want, and pulling in adjacent kinds (corollaries when
      -- `proposition` was requested) creates spurious type-equivalent
      -- candidates that defeat dispatch.
      let ns := atlasLookupByNumber env kind numStr
      match ns with
      | []  =>
        throwError s!"atlas via: no {kind} tagged `{numStr}` found (exact lookup; cascade is disabled for `apply`)"
      | [n] =>
        -- Single match — just elaborate as a normal application.
        let head := mkIdent n
        let appStx ← `($head $args*)
        Lean.Elab.Term.elabTerm appStx expectedType?
      | _  =>
        -- Multi-match. Need a concrete `expectedType` to dispatch on.
        -- Postpone if it's None or contains *any* metavariables (not
        -- just at the head) — Lean re-runs after surrounding context
        -- pins them. Without this, sites like `ref lemma X ⟨apply prop
        -- 3.3 …, sibling⟩` get elaborated before `sibling` constrains
        -- the implicits, so the apply slot sees a metavar-laden
        -- expected type and every candidate trivially unifies.
        --
        -- `tryPostponeIfNoneOrMVar` only checks the *head* — we need
        -- `tryPostponeIfHasMVars?` which scans the whole expression
        -- and postpones if any unassigned mvars remain.
        let some expected ← Lean.Elab.Term.tryPostponeIfHasMVars? expectedType?
          | throwError s!"atlas via: {kind} `{numStr}` expected type still has metavariables after postpone — can't dispatch ({ns.length} candidates). Add `: T` annotation or restructure (e.g., extract to `have x : T := ...`)."
        let mut successes : List Name := []
        let mut lastError : Option MessageData := none
        for cand in ns do
          let snap ← Lean.Elab.Term.saveState
          try
            let head := mkIdent cand
            let appStx ← `($head $args*)
            -- Elaborate without expected-type guidance, then *explicitly*
            -- check inferred type against expected via `isDefEq`.
            -- `elabTerm`/`elabTermEnsuringType` defer most unification
            -- via postponed metavars and don't surface failures
            -- synchronously; the only reliable way to know whether the
            -- candidate's return type matches is to compare types directly.
            let e ← Lean.Elab.Term.elabTerm appStx (some expected)
            Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
            let e ← Lean.instantiateMVars e
            -- Reject candidates whose elaborated form still has
            -- unresolved metavariables — that means the args didn't
            -- fully pin the implicits and `isDefEq` would aggressively
            -- unify them downstream to make types appear to match.
            if e.hasExprMVar then
              snap.restore
            else
              let inferredType ← Lean.Meta.inferType e
              let inferredType ← Lean.instantiateMVars inferredType
              if ← Lean.Meta.isDefEq inferredType expected then
                successes := successes ++ [cand]
              snap.restore
          catch ex =>
            lastError := some ex.toMessageData
            snap.restore
        match successes with
        | [] =>
          match lastError with
          | some msg => throwError m!"atlas via: no {kind} `{numStr}` candidate fits this application:\n{msg}"
          | none     => throwError s!"atlas via: no {kind} `{numStr}` candidate fits this application"
        | [cand] =>
          let head := mkIdent cand
          let appStx ← `($head $args*)
          Lean.Elab.Term.elabTerm appStx expectedType?
        | _ =>
          throwError s!"atlas via: multiple {kind} candidates at `{numStr}` fit this application: {successes}"
  | _ => Lean.Elab.throwUnsupportedSyntax

end Atlas
