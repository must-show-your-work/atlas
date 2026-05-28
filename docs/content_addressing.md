# Content addressing for atlas decls

## Motivation

A decl has two semantic signals worth tracking independently:

- **Type** — *what* is being proved. The Lean proposition itself. Two decls with the same type prove the same proposition (modulo definitional equality).
- **Proof content** — *how* it's being proved. Tactic script, term structure, embedded comments and markers.

Atlas's primary key is `(kind, number)` — a *human-curated* identifier the author assigns. Type is the **best semantic key** for "what's been proved" because it captures the proposition directly. Proof content is a secondary signal worth tracking in the database for refactor-detection, dedup, provenance, and lint queries — things that need to distinguish "different proof" from "different proposition" from "different name."

## Multiple hash forms

A single content hash isn't enough — different normalizations answer different questions:

### Type hash

Primary identity for "what is this theorem."

- **`type_hash_raw`** — hash of the type's source text. Sensitive to formatting.
- **`type_hash_pp`** — hash of the pretty-printed type. Stable across whitespace differences.
- **`type_hash_elab`** — hash of the elaborated term (post type-checking). Stable across syntactic sugar; same hash ⇔ definitionally-equal types (at the level Lean's elaborator resolves).

`type_hash_elab` is the canonical "this is the same proposition" key. The other forms are mostly for diagnostics.

### Proof hash

Identity for "how is it being proved."

- **`proof_hash_raw`** — full source body bytes. Any whitespace / comment / reorder produces a new hash.
- **`proof_hash_stripped`** — strip `/-! … -/`, `-- …`, and atlas marker bodies (`quoting`, `comment`, `idea`, `todo`, `fixme`, etc.) before hashing. Identifies proofs that differ only in commentary.
- **`proof_hash_normalized`** — `proof_hash_stripped` + α-rename bound variables to canonical names + sort commutative tactic invocations. Identifies "essentially the same proof" up to cosmetic / naming variations.
- **`proof_hash_ast`** — hash of the parsed AST nodes (kind + structure, not source positions). Most aggressive normalization; agrees with `proof_hash_normalized` on most realistic inputs.

Choice of which to store / index depends on use case. Storing all four is cheap (a hash per decl per form) and lets queries pick whichever specificity they want.

### Metadata hash (optional, partial)

Some queries care about commentary or atlas metadata changes; others don't. A `metadata_hash` can be computed over a configurable subset of the commentary block (title, preface, notes, tags, page reference, etc.) — useful for detecting "metadata-only edits" vs. "proof body edits" vs. "both."

The partition is configurable per query: include / exclude `notes`, `preface`, `tags`, etc. Stored individually so queries can recombine.

## Storage in kuzu

Extend the `Decl` node table:

```cypher
CREATE NODE TABLE Decl(
    name STRING PRIMARY KEY,
    -- existing fields ...
    type_hash_pp STRING,
    type_hash_elab STRING,
    proof_hash_raw STRING,
    proof_hash_stripped STRING,
    proof_hash_normalized STRING,
    proof_hash_ast STRING,
    metadata_hash STRING
);
```

Each hash is a fixed-length string (SHA-256 or BLAKE3 — choice is cheap to change). Optional fields can be empty for decls that don't have proofs (axioms, abbrevs, etc.).

## Use cases / queries

The point of indexing these is that the same-shaped Cypher query, with a different hash field, asks a different research question:

- **Same proposition, different proofs**: `MATCH (a:Decl), (b:Decl) WHERE a.type_hash_elab = b.type_hash_elab AND a.proof_hash_stripped <> b.proof_hash_stripped`. Tells you where the same theorem is proved more than one way — candidates for unification, or interesting for the strategy-zoology work to compare proof styles.
- **Same proof, different propositions**: same query with the operands swapped (`proof_hash_normalized` equal, `type_hash_elab` different). Tells you when a proof was copy-pasted across slightly different statements — likely refactor opportunities.
- **Cosmetic-only changes**: compare `proof_hash_raw` (changed) against `proof_hash_normalized` (same) — the diff is whitespace, comments, or marker reorganization. Useful for filtering noise in code review.
- **Metadata-only edits**: `metadata_hash` changed, `proof_hash_*` and `type_hash_*` unchanged. Drives "edit the commentary, don't re-verify the proof."
- **Provenance**: when two decls share `proof_hash_normalized` but live in different files / chapters, they're probably one decl wearing different names. Candidates for inlining or shared-lemma extraction.

Lint queries follow the same pattern: "show me everywhere `proof_hash_X = …`" identifies duplicates; "show me decls with `type_hash_elab` matching some external benchmark" cross-references against an external library.

## Type is the primary semantic key

Worth pinning down: **type is what identifies *what* a decl proves; everything else is metadata about *how* it proves it or *where* it lives.**

- `(kind, number)` is the *human-curated* address.
- `type_hash_elab` is the *semantic* address — the proposition itself.
- `proof_hash_*` are *implementation* addresses — the specific tactic script.
- Atlas `complexes`, `aliases`, etc., are *grouping* metadata.

The kuzu graph today indexes primarily on `(kind, number)`. Adding type and proof hashes gives queries a second axis of identity — they answer "is this the same theorem semantically?" rather than "is this the theorem the author labeled `2.0.25`?" Both axes are useful; both should be queryable.

## Type hash as a permanent identifier

The natural extension of "type identifies the proposition": **`type_hash_elab` (or some canonical-form refinement) is a permanent, content-derived ID for the decl.** Same proposition → same hash, forever, regardless of who proved it, when, where, or under what curated number / title.

This adds a *third* addressing axis to atlas:

1. **Curated address**: `(kind, number)` — author-assigned, can move under renumbering.
2. **Title address**: the title string — author-assigned, changes with rewording.
3. **Content address**: canonical type hash — semantic, permanent, language- and curator-independent.

### What it buys you

- **Survives renumbering / renaming**. The `2.0.25` corollary becoming `2.0.25.A` (or any future shuffle) doesn't change its content hash. Cross-references via content hash never break under reorganization.
- **Cross-project identity**. Two libraries that prove the same theorem under different names produce the same content hash. The proposition "two distinct points determine a unique line through them" hashes to the same string in GIYF as in a hypothetical Mathlib formalization (modulo canonicalization details). External tools can cross-reference / dedup across libraries.
- **External citation**. A paper citing `[atlas:type:sha256:7c1f…]` resolves to whichever decl proves that proposition in whichever atlas-instrumented codebase the reader has handy. The citation doesn't bind to a specific source location or numbering.
- **Robust against project reorganization**. Moving a theorem from chapter 2 to chapter 3, splitting a complex into pieces, merging — none change the proposition. Content-hash references survive all of it.

### Syntactic surface

Likely too ugly for in-source author use, but useful as a *metadata field* on commentary blocks and as a *resolvable URI* externally:

```
atlas commentary := by
  ref axiom I.1
  permaid "sha256:7c1f3a8e…"      -- optional explicit pin; auto-computed if omitted
  ...
```

Or for cross-project references in source:

```
have h : ... := @permaid "sha256:7c1f3a8e…"     -- or some shorter syntax TBD
```

The author normally writes `ref axiom I.1`; the permaid is the *fallback* / *external* identifier that doesn't care about curation. Atlas can compute and store it automatically — no per-decl annotation work needed unless the author wants to pin to a specific hash explicitly (e.g., to detect drift if canonicalization changes).

### Canonical form is the hard part

The whole scheme rests on choosing a canonical form for the type such that semantically-equivalent propositions produce the same hash. Difficulty axes:

- **Alpha-renaming**: `∀ A B : Point, A ≠ B → …` and `∀ X Y : Point, X ≠ Y → …` are the same proposition. The canonical form must alpha-rename bound variables to a fixed convention (de Bruijn indices, or canonical names by binding order).
- **Definitional unfolding**: should `Segment A B ⊆ Ray A B` hash the same as `{C | (A-C-B) ∨ …} ⊆ Segment A B ∪ Extension A B` (the unfolded form)? Choice of how aggressively to unfold definitions determines what counts as "the same proposition."
- **Universe variables and elaboration metadata**: should universe parameters be in the hash? Implicit arguments?
- **Lean version sensitivity**: as the elaborator evolves, the canonical form may shift. Need to either (a) version the canonicalization explicitly (`canonical-form-v1:sha256:…`), or (b) accept that permanent IDs are stable only within an elaborator generation.

Pragmatic stance: ship `type_hash_elab` first with a simple canonicalization (de Bruijn + reducible-only unfolding), call it "v1", commit to versioning the scheme so future canonicalization changes don't silently re-key the database. Authors who want truly permanent IDs across Lean-version shifts can pin a specific `permaid-v1` or `permaid-v2` etc.

### What's *not* included

- Proof content. Two different proofs of the same proposition share a `permaid`. That's the *point* — the permanent ID is for the proposition, not the implementation.
- Author / commentary metadata. None of that affects identity.
- Module / file location. The same proposition proved in two files has one `permaid`.

This is what distinguishes the permanent ID from the curated `(kind, number)`: curation tracks the *human's organizational choices*; content hash tracks the *propositional semantics*. Both are useful; both are stored.

## Caveats

- **Definitional equality**: Lean's elaborator collapses many syntactically-different types to the same `Expr`. `type_hash_elab` captures this but only at the level Lean's `isDefEq` resolves. Deeper equivalences (e.g., classical-equivalences over Prop) won't collapse.
- **Tactic order**: tactic-mode proofs often have multiple equivalent orderings. `proof_hash_normalized` needs a canonical-form pass for commutative steps (e.g., `(have h : P := …) ; (have k : Q := …)` should hash the same regardless of which `have` comes first when there's no dependency). This is hard in full generality; ship a best-effort version.
- **Hash bucket explosion**: storing four+ hashes per decl is fine at atlas scale (hundreds to low thousands of decls per project). At Mathlib scale (~hundreds of thousands), the index size matters and selective storage becomes appropriate.
- **Stability across Lean versions**: elaborated terms can differ across Lean versions for the same source. `type_hash_elab` is version-sensitive in principle; in practice this matters only when projects pin different toolchain versions and need to cross-reference.

## Implementation pieces

Roughly in dependency order:

1. **Hash computation** in `DumpDecls.lean` (or wherever per-decl extraction happens). One function per hash form; all run on the same per-decl pass.
2. **Schema extension** in `scripts/schema.cypher`. Drop-and-recreate keeps things simple.
3. **Ingest path** updates to write the new fields. Existing `ingest.py` (or whatever the loader is) needs to read the new dump format.
4. **Standard queries** in `scripts/queries/` covering the use cases above. `duplicate_proofs.cypher`, `metadata_only_edits.cypher`, `same_prop_different_proof.cypher`, etc.
5. **ProofWidget integration** (optional, downstream): the goal-pane ProofWidget from `unified_ref_ux.md` could surface "this decl shares its proof with N other decls" as a hover info — discovered via the new hash indexes.
