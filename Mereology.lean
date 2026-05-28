/-
# Mereology — a small obscure-theory demo for Atlas.

Mereology is the formal theory of parts and wholes: one primitive
relation `≼` ("is a part of"), a handful of axioms, and a surprising
amount of algebraic structure. Originated with Leśniewski (1916);
modern axiomatization tradition follows Leonard–Goodman (1940) and
Casati–Varzi (1999).

This is a self-contained demo built to exercise the Atlas pipeline
end-to-end: paired propositions, every commentary field, every
marker kind, multi-chapter dependency structure, a punchline theorem
(4.3) that connects mereology to Boolean algebras.

Commentary in this demo is **original** — we don't quote from a
specific source. The `preface` / `notes` content is editorial, written
to be readable as a book sketch.

## Chapter map

- `Mereology/Preamble.lean` — opaque `Ind : Type` + primitive `≼`.
- `Mereology/Ch1.lean` — Ground Mereology: M1–M3 + proper part +
  asymmetry + transitivity (proofs done).
- `Mereology/Ch2.lean` — Overlap, Disjoint, Weak Supplementation,
  Extensionality of proper parts.
- `Mereology/Ch3.lean` — Unrestricted Fusion + uniqueness + binary
  sum + complete-lattice theorem.
- `Mereology/Ch4.lean` — Atom, Atomism, atomic-GEM-as-powerset.

## Proof completeness

Chapter 1 proofs are fully discharged. Chapters 2–4 have `sorry`'d
proofs as initial scaffolding — each carries `idea` / `intuition` /
`cf` markers sketching the intended proof, ready to be filled in.

## What this demos

- Every `atlasNum` syntax form in use (`1.1`, `2.2.i`, `2.2.ii`).
- Every commentary field (`preface`, `notes`, `tags`, paired-decl
  reference to `2.2.i` / `2.2.ii`).
- Multiple kinds (axiom, definition, proposition, theorem, corollary).
- Code-state markers `sorry` to demonstrate work-in-progress UX.
- Reader-cue markers (`idea`, `motivation`, `cf`, `intuition`) in
  the more interesting proofs.
- A dependency graph deep enough that the viewer's graph layout
  has something to render (Ch4 cites Ch1, Ch2, Ch3 — long chains).
-/

import Mereology.Preamble
import Mereology.Ch1
import Mereology.Ch2
import Mereology.Ch3
import Mereology.Ch4
