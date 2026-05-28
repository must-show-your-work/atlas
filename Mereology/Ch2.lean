/-
Mereology / Chapter 2 — Overlap and Supplementation.

Two defined notions (`Overlap`, `Disjoint`), one new axiom
(*Weak Supplementation*), and the first non-trivial proposition:
extensionality of proper parts. Together these distinguish mereology
from a bare partial order — without supplementation, an object could
have exactly one proper part, which Leśniewski's original system
rules out.

Numbering: Chapter 2, items 1–5. Proposition 2.2 is paired
(2.2.i, 2.2.ii) — reflexivity and symmetry of overlap.

Proofs in this chapter are stubs (`sorry`). Each carries an `idea`
or `intuition` marker sketching the intended proof; filling them in
is the next pass.
-/

import Mereology.Ch1

namespace Mereology.Ch2

open Atlas
open Mereology.Ch1

/-! ## Overlap -/

atlas commentary := by
  ref definition 2.1
  name "Overlap"
  preface "x and y overlap when they share a part."
  notes "The fundamental relation for extensional mereology. Two
objects are the same iff they have the same parts iff they overlap
the same things (2.5)."

atlas definition 2.1 "Overlap"
  (x y : Ind) : Prop := ∃ z : Ind, z ≼ x ∧ z ≼ y

attribute [reducible] «Overlap»

@[inherit_doc «Overlap»]
notation:50 (priority := high) "O(" x ", " y ")" => «Overlap» x y


/-! ## Reflexivity and symmetry of overlap (paired) -/

atlas commentary := by
  ref proposition 2.2.i
  name "Reflexivity of overlap"
  preface "Every individual overlaps itself."
  notes "Witness is the individual itself, by reflexivity of parthood (1.1)."

atlas proposition 2.2.i "Reflexivity of overlap"
  : ∀ x : Ind, O(x, x) := by
  idea "x is its own witness — `x ≼ x` from 1.1 gives both clauses."
  sorry


atlas commentary := by
  ref proposition 2.2.ii
  name "Symmetry of overlap"
  preface "Overlap is symmetric in its arguments."
  notes "Same witness works both ways; the existential's body is
symmetric in x and y after swapping clauses."

atlas proposition 2.2.ii "Symmetry of overlap"
  : ∀ x y : Ind, O(x, y) → O(y, x) := by
  idea "destructure the witness ⟨z, zPx, zPy⟩ and re-pair as ⟨z, zPy, zPx⟩."
  sorry


/-! ## Disjoint -/

atlas commentary := by
  ref definition 2.3
  name "Disjoint"
  preface "x and y are disjoint when they share no part."
  notes "Negation of overlap. The supplementation axioms 2.4 / SSP
constrain when two objects can be disjoint relative to a third."

atlas definition 2.3 "Disjoint"
  (x y : Ind) : Prop := ¬ O(x, y)

attribute [reducible] «Disjoint»

@[inherit_doc «Disjoint»]
notation:50 (priority := high) "D(" x ", " y ")" => «Disjoint» x y


/-! ## Weak Supplementation -/

atlas commentary := by
  ref axiom 2.4
  name "Weak Supplementation"
  preface "If x is a proper part of y, then y has another proper part
disjoint from x."
  notes "Rules out the pathological case where y has exactly one proper
part. Without it, mereology degenerates: a thing could be \"a part of
y\" without anything else inside y to distinguish it."
  tags ["axiom", "supplementation"]

atlas axiom 2.4 "Weak Supplementation"
  : ∀ x y : Ind, x ≺ y → ∃ z : Ind, z ≺ y ∧ D(z, x)


/-! ## Extensionality of proper parts -/

atlas commentary := by
  ref proposition 2.5
  name "Extensionality of proper parts"
  preface "If x and y have the same proper parts, then x = y (assuming
both have at least one proper part)."
  notes "The headline result of Chapter 2. Mereological identity is
determined by parthood structure — two objects with the same parts are
the same object. This is what makes ≼ a *partial order on a Boolean-
algebra-shaped lattice* rather than just an arbitrary preorder."

atlas proposition 2.5 "Extensionality of proper parts"
  : ∀ x y : Ind,
    (∃ w : Ind, w ≺ x) →
    (∀ w : Ind, w ≺ x ↔ w ≺ y) →
    x = y := by
  motivation "the headline result of ground mereology — identity is determined by parthood structure."
  idea "if x ≠ y, WLOG x has a part that y doesn't have, contradicting the same-proper-parts hypothesis. WSP supplies the witness."
  cf "in Boolean algebras: two sets are equal iff they have the same elements (extensionality of ∈)."
  sorry

end Mereology.Ch2
