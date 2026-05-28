# Unified `ref` UX

Three pieces hang together to make atlas reference ergonomics work end-to-end:

1. **Unified `ref` tactic** — subsumes the current `ref` / `via` / `ref complex N.K` split into a single position-aware, type-dispatched lookup.
2. **Canonization lint** — autofixable; drives all source toward the terse `ref N args` form.
3. **ProofWidget for the goal pane** — walks the current goal's proof tree, renders a table of every `ref N` site → its long-name title.

The three together: source code is terse, the IDE makes it readable, the tactic is permissive enough to accept in-progress / experimental forms while the lint nudges everything toward the canonical form.

## Surface design

**Canonical form**: `ref N args`. Number-only — no kind, no title. The lint enforces this.

**Tactic also accepts off-plan forms** (extra data just narrows the search faster; result is the same):

- `ref kind N args` — kind narrows by tier (today's syntax).
- `ref N "Title" args` — title pins a specific decl.
- `ref kind N "Title" args` — both.

All resolve identically via the dispatch path. Authors writing experimental code can use the narrower forms; the lint converges them back to canonical on commit.

## Dispatch semantics

Position-aware:

- **Function position** (with arguments) — type-dispatch by arg types via `isDefEq`. Same machinery as today's `via`.
- **Term position** (no arguments) — type-dispatch by expected type from elaboration context. Extension of `via` to use expected type when no args are present.

Looks up the full theorem complex (every decl matching the number, cascading through `kindTiers`), then picks the unique decl whose signature unifies. Errors clearly if zero or multiple match.

Atlas-internal narrowing for performance (whether via a unique discriminator field on `Decl` or a small-list linear search per number) is an implementation choice that doesn't affect the user surface. Cluster sizes are small enough that perf isn't a real concern at any realistic atlas size.

## The "theorem complex" framing

Atlas numbers identify **theorem complexes**, not individual theorems. A complex contains the main result + its corollaries + its alternative formulations — all sharing the same number, distinguished by kind and signature.

When a mathematician writes "by Cauchy's theorem (or its corollaries)", they're invoking the complex. The unified `ref` tactic mirrors that idiom: `ref N args` means "use whichever decl in the complex N fits this call site." Position-aware dispatch picks the specific one.

This is the framing the rest of the design crystallizes around — kind becomes a hint (narrows search faster), number is the load-bearing identifier.

## Implicit complex via prefix matching

Complexes are *named* by atlas number — but a complex's *members* often have sub-numbered identifiers (`B.1.a`, `B.1.b`, …) so each individual decl is uniquely keyed for commentary lookup. The author's idiom is to refer to the complex by its bare number ("Betweenness Axiom B-1"); we want the code to mirror that, so `via axiom B.1 args` should find any member of the B.1 complex.

**Mechanism**: when the exact-number lookup returns nothing, fall back to a **prefix scan** — find every decl whose stored number matches `<requested>.` as a literal prefix. So `via axiom B.1` falls through to find `B.1.a`, `B.1.b`, etc., then runs type-dispatch over the collected candidates.

```
via axiom B.1.a args   -- exact: matches the sub-numbered decl only
via axiom B.1   args   -- exact misses → prefix scan finds B.1.a, B.1.b → type-dispatch picks one
via axiom B.1   args   -- if B.1 itself exists as a decl, exact wins → no prefix scan
```

**Why prefix-only, not full glob**: prefix preserves the hierarchy intuition (parent → children). A glob like `B.*` would conflate unrelated chapters / sub-systems. Prefix-then-`.` keeps `B.1.a` matching `B.1` but not matching `B.10.x` (since `B.10` doesn't have `B.1.` as a prefix-with-separator).

**Cost**: prefix scan iterates the byKindNumber index for the matching kind. Index size at any realistic atlas scale is small (hundreds of decls), so the linear scan is cheap. Cache the prefix→list mapping if it ever matters.

### Complexes: a "type-class-of-the-willing"

A complex is **a set of heterogeneous-but-related decls that act together as a unit** — opt-in membership rather than externally-enumerated. Each decl announces which complex(es) it belongs to; lookups across a complex name find the union of all opted-in decls.

The framing matters because complexes are **not type classes** (although they're shaped similarly at the use-site):

- A **type class** binds a uniform interface over a set of types. Members share a shape.
- A **complex** binds a thematic grouping over a set of decls that may have **very different shapes** — different signatures, different kinds, different propositional content — but that the author treats as one "thing" in the book.

Complexes cut the design space on a different axis from type classes. A single decl can sit in **multiple complexes** without any conflict: a lemma might belong to the "B-1" complex (because the book treats it as part of that betweenness axiom group) **and** to a "plane-separation" complex (because it's used together with B-4 results in figure-3.6-style arguments). Both memberships are visible to `via` lookups; both contribute candidates.

This also means complex membership has nothing to say about decl signatures — dispatching across a complex is exactly type-dispatch via `isDefEq` on whichever candidates were retrieved. Same machinery as paired-decl dispatch; just a richer source of candidates.

### Explicit complex tag (refinement, later)

When prefix matching is too coarse or too narrow (a corollary that conceptually belongs to a complex but lives at a different numeric address, or a decl that belongs to *multiple* complexes), use an explicit `complexes [...]` field on the `atlas commentary` block:

```
atlas commentary := by
  ref axiom ["B.1.a"]
  complexes ["B-1"]
  ...

atlas commentary := by
  ref lemma 3.0.7
  complexes ["B-1", "plane-separation"]   -- opt into two
  ...
```

Looking up `via axiom B.1 args` then checks (a) exact number match, (b) prefix scan, **and** (c) explicit complex membership — union the results, type-dispatch picks the unique winner.

The `complexes` field is a **list** because multi-membership is the common case. A single-membership decl just gives a list of one.

This is a refinement layered on top of prefix matching, not a replacement. Most cases will be handled by the prefix scan when the book's numeric hierarchy is the grouping; the explicit tag covers the cases where the hierarchy doesn't capture how the author actually thinks about the cluster.

### Interaction with the canonization lint

When a `via N args` resolves uniquely via prefix scan (not exact match), the canonization lint can offer to specialize: rewrite to the specific sub-number that was picked. So `via axiom B.1 hABC` would lint to `via axiom ["B.1.a"] hABC` once the dispatch resolves to that specific decl.

Whether you *want* this specialization depends on intent — the same trade-off as the hint-form → canonical lint:

- Prefer prefix form (`B.1`) for **author-style** code that mirrors the book.
- Prefer specific form (`B.1.a`) for **performance** and **stability** against new decls being added to the complex.

Both lints exist; pick per project / per file via configuration.

## Canonization lint

When dispatch resolves uniquely on a `ref` invocation, the lint offers an **autofixable code action** to rewrite to the canonical form `ref N args` — stripping kind/title hints if present.

**Inverse direction** also potentially useful: rewrite `«Title» args` (explicit decl reference) to `ref N args` for rename-stability. Both directions optional; project-configurable. Useful at different phases:

- Project early, titles still evolving → prefer `ref N` (rename-stable).
- Specific decl committed, want to skip dispatch → prefer explicit `«Title»` (but then stuck with renames).

The lint family supports either norm; pick per project.

## Tag-driven exploratory search (`via? [tags]`)

A complementary entry-point for when the author knows the *concept* but doesn't remember the specific theorem number:

```
have h : L splits A and B := via? ["intersection" "splits" "segment"]
```

**Mechanism**: query atlas for all decls carrying the given tags (intersection of tag sets — every named tag must match). For each candidate, attempt `via`-style dispatch with the surrounding args / expected type. Pick the unique match (or error with the candidate list if zero or multiple).

**Deliberately slow.** Same shape as Lean's `exact?` — tries everything once, scoped by tags instead of the whole environment. Not suitable for hot paths; the `?` suffix signals "this is a search tactic; commit-and-canonize before merging."

**Canonization**: the same lint that rewrites hint-forms to canonical also rewrites a successful `via? [tags]` invocation to the specific `ref N args` form. Authors use `via?` exploratorially, then commit to the resolved reference on lint pass.

**Prerequisite**: tag metadata must be populated on atlas decls. Sits downstream of the broader metadata extension work (page references, kind tiers, role tags, etc.).

The full lint family — canonizing hint-forms, canonizing successful `via?` searches, optionally the inverse (explicit-title → `ref N` for rename-stability) — all share the same mechanism: pattern-match `ref`-resolved sites, offer the most-canonical replacement.

## ProofWidget for the goal pane

Walks the current goal's proof tree, finds every `ref N` invocation, renders a table in the goal pane:

```
2.0.25 → "If A-X-B and L meets the segment at X then L splits A and B"
1.0.32 → "A pointed intersection's witness point lies on the left line"
2.0.20 → "Membership in the intersection of distinct nonparallel lines is the pointed intersection"
```

This is the load-bearing piece that makes terse-number-as-canonical actually pleasant. Without it, terse refs are illegible at a glance; you'd need to grep the codebase to know what `2.0.25` means. With it, you write `ref 2.0.25 ABC h` and see the full citation in the goal pane next to the goal.

This subsumes earlier per-symbol hover lookup designs — the goal-pane table is a more powerful surface, since it covers the entire active proof at once.

## Supersedes / subsumes

This design supersedes / subsumes the following earlier atlas plans:

- **`ref` / `via` split** (current state: `ref` for unambiguous term-position lookups, `via` for paired-decl function-position dispatch) — **superseded**. The unified `ref` handles both via position-aware dispatch. Per-call-site migration is mechanical sed; the underlying machinery is in `Atlas/Via.lean` already.
- **`ref complex N.K`** (planned: explicit syntax for cluster-wide dispatch) — **subsumed**. The default `ref N` behavior IS cluster dispatch; no separate keyword needed.
- **In-editor lookup / hover** (`atlas_inline_lookup.md`) — **subsumed by the ProofWidget piece**, which provides a more powerful goal-pane table view rather than per-symbol hover.

## Implementation pieces

Ordered roughly by dependency:

1. **Extend `Atlas/Ref.lean`** to accept the number-only form, kind/title hints; do type-dispatch via `isDefEq` (lifting `via`'s machinery). Function-position behavior is already there in `Atlas/Via.lean` — port and unify.
2. **Term-position dispatch by expected type** — `withExpectedType` / similar from Lean's elaboration, fed to the same `isDefEq` machinery.
3. **Canonization lint** — Lean 4 linter that runs on `ref` invocations, checks for single-match dispatch, offers autofixable rewrite to canonical form. Could live in `Atlas/Lints.lean`.
4. **ProofWidget** — registers via Lean's widget system; walks the active proof tree, collects `ref` sites, renders the table. Goes in `Atlas/ProofWidget.lean` or similar.

(1) and (2) are the substantive tactic-side change. (3) is small once (1)+(2) exist. (4) is independent of (1)–(3) and can land in either order, but is what makes the whole UX actually usable.
