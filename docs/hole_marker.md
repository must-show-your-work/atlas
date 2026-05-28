---
name: hole marker (planned)
description: Planned tactic — `needs [<hypos>] := by <proof>` marks a structural gap in a proof where the author silently assumes a hypothesis the formalization is missing. Acts like a typed `sorry` that records what's missing, with a stretch goal of auto-introducing the hypothesis at the decl signature.
type: project
---
# `needs [<hypos>] := by <proof>` — planned tactic

## Motivation

Formalizing a textbook proof regularly surfaces *holes the author elided*.
Two flavours:

1. **Silent hypothesis** — author writes "X follows from hypothesis and
   axiom Y" but the formalization's stated hypothesis is genuinely weaker
   than the English. Example surfaced in GIYF: Pasch's Theorem step (2),
   "A and B do not lie on l (hypothesis and Axiom B-1)" — only works if
   "L intersects AB **in a point** between A and B" is read as
   single-point intersection at a strict-interior witness. Lean's
   `L intersects segment A B` (existence-only) is too weak; A *can* be on L.
2. **Genuine gap** — the proof actually has a load-bearing step the
   author skipped or got wrong. Found by formalization; needs author
   judgment to close (add hypothesis? rework the proof?).

Today the formalizer's only options are `sorry` (opaque) or a comment.
Both lose the *structured* information: *what* hypothesis would close
this. That information is the most valuable artifact of finding the
hole — surface it.

## Shape

```lean
atlas proposition 3.7 "Pasch's Postulate"
  {A B C : Point} {L : Line}
  (triABC : ¬(collinear A B C)) (LintSegAB : L intersects segment A B) :
  ...
  := by
  ...
  have AoffL : A off L := by
    needs [X : Point, AXB : A - X - B, LintSegAB' : L intersects segment A B at X] := by
      intro AonL
      have : A ∈ L ∩ segment A B := ⟨AonL, by obvious⟩
      rw [LintSegAB'] at this
      have AeqX : A = X := this
      have ⟨dist, _⟩ := ref axiom ["B.1.a"] AXB
      separate at dist
      exact AneX AeqX
  ...
```

Reading: "this `have AoffL` would go through if the listed hypotheses
were available; here's the proof that uses them. Until they're
introduced, this is a hole."

## Semantics

- **Type-checks like `sorry`** — the hole occupies a `have`/proof slot,
  proves no real obligation. The `by` body is *unchecked* against the
  surrounding context (its hypotheses come from the `needs` list).
- **Build-time**: gated by the same flag(s) that allow `sorry`. Emits
  a `hole` warning rather than `sorry` warning.
- **Records to atlas DB**: each `needs` block produces a `Hole` node:
  ```
  Hole {
    decl: Name,          -- enclosing atlas decl
    line, column: Nat,   -- source position
    reason: String,      -- optional free-text justification
    needs: Array Hyp,    -- {name, type} pairs from the binder list
  }
  ```
  Queryable via Cypher: "show all holes citing axiom X", "show all
  holes in chapter N", etc.

## Stretch: `atlas fill-holes` code action

A `lake exec atlas fill-holes <decl>` (or LSP code action) that:

1. Locates the `needs [...]` block in the named decl.
2. Lifts each item from `needs` into the decl's binder list, marked
   with a comment:
   ```
   atlas proposition 3.7 "Pasch's Postulate"
     {A B C : Point} {L : Line}
     {X : Point}                                    -- hole-fill 3.7@L83
     (AXB : A - X - B)                              -- hole-fill 3.7@L83
     (LintSegAB : L intersects segment A B at X)    -- hole-fill 3.7@L83
     (triABC : ¬(collinear A B C)) :
     ...
   ```
   (note: the lifted `LintSegAB` *replaces* the weaker original.)
3. Rewrites the `needs [...] := by body` to plain `body` — the
   `needs`-bound hypos are now in scope from the signature.
4. Updates downstream call sites (the existing renumber-script
   machinery already does name-rewrites; same shape).

Reversible by `git revert`. The point isn't to force the introduction
— it's to make the *cost of doing it honestly* one keystroke, so the
formalizer chooses based on what the proof actually needs rather than
on what's easy to type.

## Distinction from `sorry`, `todo`, `fixme`

| Marker  | Semantics                              | Build effect       |
|---------|----------------------------------------|--------------------|
| `sorry` | "unfinished, anonymous"                | warn               |
| `todo`  | "planned work, commentary"             | none (no-op)       |
| `fixme` | "known broken placeholder, commentary" | none (no-op)       |
| `hole`  | "load-bearing gap, here's what's missing" | warn (structured) |

`todo` / `fixme` are *annotations* (see `inline_annotation_vocabulary`
in the GIYF planning notes) — pure commentary, no proof-state effect.
`hole` is a real tactic that consumes an obligation, like `sorry`, but
carries structured metadata about *what would close it*.

## Implementation outline

1. **Tactic** (`Atlas.Tactic.Hole` or similar):
   - `syntax "needs" "[" sepBy(binder, ",") "]" " := by " tacticSeq : tactic`
   - Elaborates the `needs [...]` binders into a fresh local context.
   - Elaborates the body against that context. Type-checks the body
     locally (it's a real proof of the goal *under those binders*).
   - The outer obligation is closed by `sorry` (or a typed
     equivalent) — the body's existence is a *witness that the proof
     would go through given the binders*, but doesn't actually
     discharge the obligation.
2. **Recording**: env extension `holeExt : PersistentEnvExtension HoleRec`.
   Each `needs` block appends a record.
3. **`scripts/DumpDecls.lean`**: emit `holes` array per decl + a
   top-level `holes.json` for cross-cutting queries.
4. **Graph schema**: new `Hole` node kind, edges to the enclosing
   decl and to any atlas decls cited in the `reason` field.
5. **Lint surface**: `lake exec atlas list-holes` for a status board.

## Open questions

- Should `needs` accept a `reason "..."` string? (Yes, probably — same
  field shape as `comment` markers.)
- Multiple `needs` blocks per decl: union or sequential? Sequential
  makes more sense (each block has its own context).
- Auto-fill: when does the rewriter know it's safe to lift a `needs`
  hypothesis to the signature? E.g., if the hypothesis names a free
  variable that already exists in the signature with a different name,
  there's a conflict. Probably: refuse to fill, surface the conflict.
- Interaction with `via` / `ref`: should a `needs` body be allowed to
  use `ref lemma N.K`? Yes — the `by` body is fully elaborated; refs work.
- Storage: do `needs`-bound hypos get tracked as deps? Probably as
  edges of a distinct kind (`needs-hyp` rather than `cites`), so
  the viewer can render them differently.

## Cost estimate

- Core tactic: ~80–120 LOC (parsing the binder list, setting up local
  context, recording).
- DumpDecls + JSON: ~30 LOC.
- Viewer integration: ~50 LOC for a holes panel + node styling.
- `atlas fill-holes` rewriter: ~200 LOC (the binder-lifting is the
  bulk; reuses the renumber-script infra for call-site updates).

## Order

After Atlas extraction lands (`atlas_extraction_planned`) and the
inline-annotation marker family stabilizes (we'll have learned what
the env-extension + JSON shape should look like by then). Not urgent
— the `sorry` + comment pattern works in the interim — but valuable
once the corpus is large enough that *cross-cutting* hole queries
("which proofs depend on unstated single-point-intersection
hypotheses?") start paying off.
